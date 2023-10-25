use std::{
    ffi::CString,
    io,
    mem::size_of,
    os::fd::AsRawFd,
    panic::AssertUnwindSafe,
    result,
    sync::{atomic::AtomicBool, Arc, Barrier},
    thread::{self, JoinHandle},
};

use anyhow::anyhow;
use num_enum::TryFromPrimitive;
use seccompiler::{apply_filter, SeccompAction};
use thiserror::Error;
use virtio_devices::{
    seccomp_filters::get_seccomp_filter, ActivateError, EpollHelper, EpollHelperError,
    EpollHelperHandler, VirtioCommon, VirtioDevice, VirtioInterrupt, VirtioInterruptType,
    EPOLL_HELPER_EVENT_LAST,
};
use virtio_queue::{DescriptorChain, Queue, QueueT};
use vm_allocator::page_size::get_page_size;
use vm_memory::{
    bitmap::AtomicBitmap, ByteValued, Bytes, GuestAddress, GuestAddressSpace, GuestMemory,
    GuestMemoryAtomic, GuestMemoryError, GuestMemoryLoadGuard, GuestMemoryMmap,
};
use vm_migration::{Migratable, MigratableError, Pausable, Snapshot, Snapshottable, Transportable};
use vmm_sys_util::eventfd::EventFd;

// One virtqueue, for guest-originated requests
const QUEUE_SIZE: u16 = 128;
const QUEUE_SIZES: &[u16] = &[QUEUE_SIZE];

const MAJOR_VERSION: u32 = 1;
const MINOR_VERSION: u32 = 0;

const VIRTIO_F_VERSION_1: u32 = 32;

// New descriptors are pending on the virtio queue.
const QUEUE_AVAIL_EVENT: u16 = EPOLL_HELPER_EVENT_LAST + 1;

#[derive(Error, Debug)]
pub enum Error {
    // device errors
    #[error("Guest gave us bad memory addresses: {0}")]
    GuestMemory(GuestMemoryError),
    #[error("Guest gave us a write only descriptor that protocol says to read from")]
    UnexpectedWriteOnlyDescriptor,
    #[error("Guest gave us a read only descriptor that protocol says to write to")]
    UnexpectedReadOnlyDescriptor,
    #[error("Guest gave us too few descriptors in a descriptor chain")]
    DescriptorChainTooShort,
    #[error("Guest gave us a buffer that was too short to use")]
    BufferLengthTooSmall,
    #[error("Failed adding used index: {0}")]
    QueueAddUsed(virtio_queue::Error),
    #[error("Guest sent us invalid request")]
    InvalidRequest,

    // memctl errors
    #[error("Request contains invalid arguments")]
    InvalidArgument(u64),
    #[error("Unknown function code: {0}")]
    UnknownFunctionCode(u64),
    #[error("Libc call fail.: {0}")]
    LibcFail(std::io::Error),
}

#[repr(u64)]
#[derive(Copy, Clone, TryFromPrimitive, Debug)]
enum FunctionCode {
    Info = 0,
    Dontneed = 1,
    Remove = 2,
    Free = 3,
    Pageout = 4,
    Unmergeable = 5,
    Dontdump = 6,
    Mlock = 7,
    Munlock = 8,
    MprotectNone = 9,
    MprotectR = 10,
    MprotectW = 11,
    MprotectRW = 12,
    SetVMAAnonName = 13,
}

#[repr(C)]
#[derive(Copy, Clone, Debug, Default)]
struct MemctlReq {
    func_code: u64,
    addr: u64,
    length: u64,
    arg: u64,
}

// SAFETY: it only has data and has no implicit padding.
unsafe impl ByteValued for MemctlReq {}

#[repr(C)]
#[derive(Copy, Clone, Debug, Default)]
struct MemctlNormalResp {
    ret_value: u64,
    arg0: u64,
    arg1: u64,
}

#[repr(C)]
#[derive(Copy, Clone, Debug, Default)]
struct MemctlInfoResp {
    big_endian: u64,
    major_version: u32,
    minor_version: u32,
    page_size: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
union VmmRetUnion {
    normal_ret: MemctlNormalResp,
    info_ret: MemctlInfoResp,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct MemctlResp {
    ret_errno: u32,
    ret_code: u32,
    ret_payload: VmmRetUnion,
}

impl std::default::Default for MemctlResp {
    fn default() -> Self {
        Self {
            ret_errno: Default::default(),
            ret_code: Default::default(),
            ret_payload: VmmRetUnion {
                normal_ret: Default::default(),
            },
        }
    }
}

impl std::fmt::Debug for MemctlResp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let MemctlResp {
            ret_errno,
            ret_code,
            ..
        } = self;
        write!(
            f,
            "MemctlResp {{ ret_errno: {}, ret_code: {}, .. }}",
            ret_errno, ret_code
        )
    }
}

// SAFETY: it only has data and has no implicit padding.
unsafe impl ByteValued for MemctlResp {}

struct Request {
    req: MemctlReq,
    status_addr: GuestAddress,
}

impl Request {
    fn parse(
        desc_chain: &mut DescriptorChain<GuestMemoryLoadGuard<GuestMemoryMmap<AtomicBitmap>>>,
    ) -> result::Result<Request, Error> {
        let desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;
        // The descriptor contains the request type which MUST be readable.
        if desc.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor);
        }
        if desc.len() as usize != size_of::<MemctlReq>() {
            return Err(Error::InvalidRequest);
        }
        let req: MemctlReq = desc_chain
            .memory()
            .read_obj(desc.addr())
            .map_err(Error::GuestMemory)?;

        let status_desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;

        // The status MUST always be writable
        if !status_desc.is_write_only() {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }

        if (status_desc.len() as usize) < size_of::<MemctlResp>() {
            return Err(Error::BufferLengthTooSmall);
        }

        Ok(Request {
            req,
            status_addr: status_desc.addr(),
        })
    }

    fn write_response(
        &self,
        mem: &GuestMemoryMmap<AtomicBitmap>,
        resp: MemctlResp,
    ) -> Result<u32, Error> {
        mem.write_obj(resp, self.status_addr)
            .map_err(Error::GuestMemory)?;
        Ok(size_of::<MemctlResp>() as u32)
    }
}

struct MemctlEpollHandler {
    interrupt_cb: Arc<dyn VirtioInterrupt>,
    queue_evt: EventFd,
    kill_evt: EventFd,
    pause_evt: EventFd,
    queue: Queue,
    mem: GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
}

impl MemctlEpollHandler {
    /// f is called with the host address of `range_base` and only when
    /// [`range_base`, `range_base` + `range_len`) is present in the guest
    fn operate_on_memory_range<F>(
        memory: &GuestMemoryMmap<AtomicBitmap>,
        addr: u64,
        length: u64,
        f: F,
    ) -> result::Result<(), Error>
    where
        F: FnOnce(*mut libc::c_void, libc::size_t) -> libc::c_int,
    {
        let range_base = GuestAddress(addr);
        let range_len = usize::try_from(length).map_err(|_| Error::InvalidRequest)?;

        // assume guest memory is not interleaved with vmm memory on the host.
        if !memory.check_range(range_base, range_len) {
            return Err(Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(
                range_base,
            )));
        }
        let hva = memory
            .get_host_address(range_base)
            .map_err(Error::GuestMemory)?;
        debug!(
            "guest address {:X} hva {:X} length {}",
            addr as usize, hva as usize, range_len
        );
        let res = f(hva as *mut libc::c_void, range_len as libc::size_t);
        if res != 0 {
            return Err(Error::LibcFail(io::Error::last_os_error()));
        }
        Ok(())
    }

    fn madvise(
        memory: &GuestMemoryMmap<AtomicBitmap>,
        addr: u64,
        length: u64,
        advice: libc::c_int,
    ) -> result::Result<(), Error> {
        debug!("addr {:X} length {} advice {}", addr, length, advice);
        Self::operate_on_memory_range(memory, addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::madvise(base, len, advice)
        })
    }

    fn mlock(
        memory: &GuestMemoryMmap<AtomicBitmap>,
        addr: u64,
        length: u64,
        on_default: bool,
    ) -> result::Result<(), Error> {
        Self::operate_on_memory_range(memory, addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::mlock2(base, len, if on_default { libc::MLOCK_ONFAULT } else { 0 })
        })
    }

    fn munlock(
        memory: &GuestMemoryMmap<AtomicBitmap>,
        addr: u64,
        length: u64,
    ) -> result::Result<(), Error> {
        Self::operate_on_memory_range(memory, addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::munlock(base, len)
        })
    }

    fn mprotect(
        memory: &GuestMemoryMmap<AtomicBitmap>,
        addr: u64,
        length: u64,
        protection: libc::c_int,
    ) -> result::Result<(), Error> {
        Self::operate_on_memory_range(memory, addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::mprotect(base, len, protection)
        })
    }

    fn set_vma_anon_name(
        memory: &GuestMemoryMmap<AtomicBitmap>,
        addr: u64,
        length: u64,
        name: u64,
    ) -> result::Result<(), Error> {
        let name = (name != 0).then(|| CString::new(format!("memctl-{}", name)).unwrap());
        let name_ptr = if let Some(name) = &name {
            name.as_ptr()
        } else {
            std::ptr::null()
        };
        debug!("addr {:X} length {} name {:?}", addr, length, name);

        Self::operate_on_memory_range(memory, addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::prctl(
                libc::PR_SET_VMA,
                libc::PR_SET_VMA_ANON_NAME,
                base,
                len,
                name_ptr,
            )
        })
    }

    fn signal(&self, int_type: VirtioInterruptType) -> result::Result<(), virtio_devices::Error> {
        self.interrupt_cb.trigger(int_type).map_err(|e| {
            error!("Failed to signal used queue: {:?}", e);
            virtio_devices::Error::FailedSignalingUsedQueue(e)
        })
    }

    fn process_request(
        &mut self,
        memory: &GuestMemoryMmap<AtomicBitmap>,
        func_code: FunctionCode,
        addr: u64,
        length: u64,
        arg: u64,
    ) -> Result<MemctlResp, Error> {
        let result = match func_code {
            FunctionCode::Info => {
                return Ok(MemctlResp {
                    ret_errno: 0,
                    ret_code: 0,
                    ret_payload: VmmRetUnion {
                        info_ret: MemctlInfoResp {
                            big_endian: if cfg!(target_endian = "big") { 1 } else { 0 },
                            major_version: MAJOR_VERSION,
                            minor_version: MINOR_VERSION,
                            page_size: get_page_size(),
                        },
                    },
                })
            }
            FunctionCode::Dontneed => Self::madvise(memory, addr, length, libc::MADV_DONTNEED),
            FunctionCode::Remove => Self::madvise(memory, addr, length, libc::MADV_REMOVE),
            FunctionCode::Free => Self::madvise(memory, addr, length, libc::MADV_FREE),
            FunctionCode::Pageout => Self::madvise(memory, addr, length, libc::MADV_PAGEOUT),
            FunctionCode::Unmergeable => {
                Self::madvise(memory, addr, length, libc::MADV_UNMERGEABLE)
            }
            FunctionCode::Dontdump => Self::madvise(memory, addr, length, libc::MADV_DONTDUMP),
            FunctionCode::Mlock => Self::mlock(memory, addr, length, false),
            FunctionCode::Munlock => Self::munlock(memory, addr, length),
            FunctionCode::MprotectNone => Self::mprotect(memory, addr, length, libc::PROT_NONE),
            FunctionCode::MprotectR => Self::mprotect(memory, addr, length, libc::PROT_READ),
            FunctionCode::MprotectW => Self::mprotect(memory, addr, length, libc::PROT_WRITE),
            FunctionCode::MprotectRW => {
                Self::mprotect(memory, addr, length, libc::PROT_READ | libc::PROT_WRITE)
            }
            FunctionCode::SetVMAAnonName => Self::set_vma_anon_name(memory, addr, length, arg),
        };
        result.map(|_| MemctlResp::default())
    }

    fn process_queue(&mut self) -> Result<bool, Error> {
        let mut used_descs = false;

        while let Some(mut desc_chain) = self.queue.pop_descriptor_chain(self.mem.memory()) {
            let r = Request::parse(&mut desc_chain)?;
            let MemctlReq {
                func_code,
                addr,
                length,
                arg,
            } = r.req;

            let resp_or_err = FunctionCode::try_from(func_code)
                .map_err(|_| Error::UnknownFunctionCode(func_code))
                .and_then(|func_code| {
                    self.process_request(desc_chain.memory(), func_code, addr, length, arg)
                });

            let resp = match resp_or_err {
                Ok(resp) => resp,
                Err(e) => match e {
                    Error::InvalidArgument(arg) => MemctlResp {
                        ret_errno: libc::EINVAL as u32,
                        ret_code: arg as u32,
                        ..Default::default()
                    },
                    Error::LibcFail(err) => MemctlResp {
                        ret_errno: err.raw_os_error().unwrap_or(libc::EFAULT) as u32,
                        ret_code: 0u32,
                        ..Default::default()
                    },
                    Error::UnknownFunctionCode(func_code) => MemctlResp {
                        ret_errno: libc::EOPNOTSUPP as u32,
                        ret_code: func_code as u32,
                        ..Default::default()
                    },
                    // device error, stop responding
                    other => return Err(other),
                },
            };

            let len = r.write_response(desc_chain.memory(), resp)?;
            self.queue
                .add_used(desc_chain.memory(), desc_chain.head_index(), len)
                .map_err(Error::QueueAddUsed)?;
            used_descs = true;
        }

        Ok(used_descs)
    }

    fn run(
        &mut self,
        paused: Arc<AtomicBool>,
        paused_sync: Arc<Barrier>,
    ) -> result::Result<(), EpollHelperError> {
        let mut helper = EpollHelper::new(&self.kill_evt, &self.pause_evt)?;
        helper.add_event(self.queue_evt.as_raw_fd(), QUEUE_AVAIL_EVENT)?;
        helper.run(paused, paused_sync, self)?;

        Ok(())
    }
}

impl EpollHelperHandler for MemctlEpollHandler {
    fn handle_event(
        &mut self,
        _helper: &mut EpollHelper,
        event: &epoll::Event,
    ) -> result::Result<(), EpollHelperError> {
        let ev_type = event.data as u16;

        match ev_type {
            QUEUE_AVAIL_EVENT => {
                self.queue_evt.read().map_err(|e| {
                    EpollHelperError::HandleEvent(anyhow!("Failed to get queue event: {:?}", e))
                })?;

                let needs_notification = self.process_queue().map_err(|e| {
                    EpollHelperError::HandleEvent(anyhow!("Failed to process queue : {:?}", e))
                })?;
                if needs_notification {
                    self.signal(VirtioInterruptType::Queue(0)).map_err(|e| {
                        EpollHelperError::HandleEvent(anyhow!(
                            "Failed to signal used queue: {:?}",
                            e
                        ))
                    })?;
                }
            }
            _ => {
                return Err(EpollHelperError::HandleEvent(anyhow!(
                    "Unexpected event: {}",
                    ev_type
                )));
            }
        }
        Ok(())
    }
}

pub struct Memctl {
    common: VirtioCommon,
    id: String,
    seccomp_action: SeccompAction,
    exit_evt: EventFd,
}

impl Pausable for Memctl {
    fn pause(&mut self) -> result::Result<(), MigratableError> {
        self.common.pause()
    }

    fn resume(&mut self) -> result::Result<(), MigratableError> {
        self.common.resume()
    }
}

impl Snapshottable for Memctl {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn snapshot(&mut self) -> std::result::Result<Snapshot, MigratableError> {
        Snapshot::new_from_state(&())
    }
}
impl Transportable for Memctl {}
impl Migratable for Memctl {}

impl Drop for Memctl {
    fn drop(&mut self) {
        if let Some(kill_evt) = self.common.kill_evt.take() {
            // Ignore the result because there is nothing we can do about it.
            let _ = kill_evt.write(1);
        }
        self.common.wait_for_epoll_threads();
    }
}

impl Memctl {
    pub fn new(id: String, seccomp_action: SeccompAction, exit_evt: EventFd) -> io::Result<Memctl> {
        Ok(Memctl {
            common: VirtioCommon {
                avail_features: 1u64 << VIRTIO_F_VERSION_1,
                acked_features: 0,
                paused: Arc::new(AtomicBool::new(false)),
                paused_sync: Some(Arc::new(Barrier::new(2))),
                queue_sizes: QUEUE_SIZES.to_vec(),
                device_type: vm_virtio::VirtioDeviceType::Memctl as u32,
                min_queues: 1,
                ..Default::default()
            },
            id,
            seccomp_action,
            exit_evt,
        })
    }
}

impl VirtioDevice for Memctl {
    fn device_type(&self) -> u32 {
        self.common.device_type
    }

    fn queue_max_sizes(&self) -> &[u16] {
        &self.common.queue_sizes
    }

    fn features(&self) -> u64 {
        self.common.avail_features
    }

    fn ack_features(&mut self, value: u64) {
        self.common.ack_features(value)
    }

    fn activate(
        &mut self,
        mem: GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
        interrupt_cb: std::sync::Arc<dyn virtio_devices::VirtioInterrupt>,
        mut queues: Vec<(usize, virtio_queue::Queue, EventFd)>,
    ) -> virtio_devices::ActivateResult {
        self.common.activate(&queues, &interrupt_cb)?;
        let (kill_evt, pause_evt) = self.common.dup_eventfds();
        let (_, queue, queue_evt) = queues.remove(0);

        let mut handler = MemctlEpollHandler {
            interrupt_cb,
            queue_evt,
            kill_evt,
            pause_evt,
            queue,
            mem,
        };

        let paused = self.common.paused.clone();
        let paused_sync = self.common.paused_sync.clone();
        let mut epoll_threads = Vec::new();

        spawn_virtio_thread(
            &self.id,
            &self.seccomp_action,
            virtio_devices::seccomp_filters::Thread::VirtioMemctl,
            &mut epoll_threads,
            &self.exit_evt,
            move || handler.run(paused, paused_sync.unwrap()),
        )?;
        self.common.epoll_threads = Some(epoll_threads);

        event!("virtio-device", "activated", "id", &self.id);
        Ok(())
    }
}

fn spawn_virtio_thread<F>(
    name: &str,
    seccomp_action: &SeccompAction,
    thread_type: virtio_devices::seccomp_filters::Thread,
    epoll_threads: &mut Vec<JoinHandle<()>>,
    exit_evt: &EventFd,
    f: F,
) -> Result<(), ActivateError>
where
    F: FnOnce() -> std::result::Result<(), EpollHelperError>,
    F: Send + 'static,
{
    let seccomp_filter = get_seccomp_filter(seccomp_action, thread_type)
        .map_err(ActivateError::CreateSeccompFilter)?;

    let thread_exit_evt = exit_evt
        .try_clone()
        .map_err(ActivateError::CloneExitEventFd)?;
    let thread_name = name.to_string();

    thread::Builder::new()
        .name(name.to_string())
        .spawn(move || {
            if !seccomp_filter.is_empty() {
                if let Err(e) = apply_filter(&seccomp_filter) {
                    error!("Error applying seccomp filter: {:?}", e);
                    thread_exit_evt.write(1).ok();
                    return;
                }
            }
            match std::panic::catch_unwind(AssertUnwindSafe(f)) {
                Err(_) => {
                    error!("{} thread panicked", thread_name);
                    thread_exit_evt.write(1).ok();
                }
                Ok(r) => {
                    if let Err(e) = r {
                        error!("Error running worker: {:?}", e);
                        thread_exit_evt.write(1).ok();
                    }
                }
            };
        })
        .map(|thread| epoll_threads.push(thread))
        .map_err(|e| {
            error!("Failed to spawn thread for {}: {}", name, e);
            ActivateError::ThreadSpawn(e)
        })
}
