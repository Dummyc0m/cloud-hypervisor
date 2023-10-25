use num_enum::TryFromPrimitive;
use std::{
    collections::HashMap,
    ffi::CString,
    io, result,
    sync::{Arc, Barrier, RwLock},
};
use thiserror::Error;
use vm_allocator::page_size::get_page_size;
use vm_device::BusDeviceSync;
use vm_memory::{
    bitmap::AtomicBitmap, ByteValued, Bytes, GuestAddress, GuestAddressSpace, GuestMemory,
    GuestMemoryAtomic, GuestMemoryError, GuestMemoryMmap,
};
use vm_migration::{Migratable, MigratableError, Pausable, Snapshot, Snapshottable, Transportable};

const MAJOR_VERSION: u32 = 1;
const MINOR_VERSION: u32 = 0;

pub const PORT: u32 = 0xbef0;
pub const NR_PORTS: u32 = 4;

/// The PORT + CONTROL_BYTE combination allows the host to initialize,
/// configure, and teardown the transport channels.
const CONTROL_BYTE: u8 = 0xff;

#[derive(Error, Debug)]
pub enum Error {
    // device errors
    #[error("Guest gave us bad memory addresses: {0}")]
    GuestMemory(GuestMemoryError),
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

#[repr(C)]
#[derive(Copy, Clone)]
struct MemctlTransportConnect {
    nr_cpus: u64,
    buf_phys_addr: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct MemctlTransportConnectResponse {
    #[allow(dead_code)]
    port: u64,
    #[allow(dead_code)]
    byte: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct MemctlTransportAck {
    #[allow(dead_code)]
    acked_phys_addr: u64,
    _padding: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
union MemctlTransportUnion {
    connect: MemctlTransportConnect,
    connect_response: MemctlTransportConnectResponse,
    ack: MemctlTransportAck,
}

#[repr(u64)]
#[derive(PartialEq, Eq, Copy, Clone)]
enum MemctlTransportType {
    Connect,
    Disconnect,
    ConnectResponse,
    Ack,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct MemctlTransport {
    r#type: MemctlTransportType,
    payload: MemctlTransportUnion,
}

impl MemctlTransport {
    fn ack(addr: GuestAddress) -> Self {
        MemctlTransport {
            r#type: MemctlTransportType::Ack,
            payload: MemctlTransportUnion {
                ack: MemctlTransportAck {
                    acked_phys_addr: addr.0,
                    _padding: 0,
                },
            },
        }
    }

    fn connect_response(port: u64, byte: u64) -> Self {
        MemctlTransport {
            r#type: MemctlTransportType::ConnectResponse,
            payload: MemctlTransportUnion {
                connect_response: MemctlTransportConnectResponse { port, byte },
            },
        }
    }

    fn is_disconnect(&self) -> bool {
        self.r#type == MemctlTransportType::Disconnect
    }

    fn as_connect(self) -> Option<MemctlTransportConnect> {
        if self.r#type == MemctlTransportType::Connect {
            Some(unsafe { self.payload.connect })
        } else {
            None
        }
    }
}

// Contains no references and does not have compiler-inserted padding
unsafe impl ByteValued for MemctlTransport {}

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

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
struct GuestConnection {
    port: u32,
    byte: u8,
}

impl Default for GuestConnection {
    fn default() -> Self {
        GuestConnection::new(PORT, 0)
    }
}

impl GuestConnection {
    fn new(port: u32, byte: u8) -> Self {
        Self { port, byte }
    }

    fn next(&self) -> Self {
        let GuestConnection { port, byte } = *self;
        let port_offset = port - PORT;

        if byte == u8::MAX {
            GuestConnection::new((port_offset + 1) % NR_PORTS + PORT, 0)
        } else {
            GuestConnection::new(port, byte + 1)
        }
    }
}

struct PercpuInitState {
    transport_addr: GuestAddress,
    nr_cpus: u64,
    done_cpus: u64,
    port_buf_map: HashMap<GuestConnection, GuestAddress>,
    next_conn: GuestConnection,
}

impl PercpuInitState {
    fn new(transport_addr: GuestAddress, nr_cpus: u64) -> Self {
        let mut port_buf_map = HashMap::new();
        // reserve the PORT + CONTROL_BYTE combination for teardown
        port_buf_map.insert(GuestConnection::new(PORT, CONTROL_BYTE), transport_addr);

        PercpuInitState {
            transport_addr,
            nr_cpus,
            done_cpus: 0,
            port_buf_map,
            next_conn: GuestConnection::default(),
        }
    }
}

enum MemctlState {
    TransportInit(Vec<u8>),
    TransportAvailable(GuestAddress),
    PercpuInit(PercpuInitState),
    Ready(HashMap<GuestConnection, GuestAddress>),
    Broken,
}

impl MemctlState {
    fn do_handle_percpu_init(
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
        mut state: PercpuInitState,
        MemctlTransportConnect { buf_phys_addr, .. }: MemctlTransportConnect,
    ) -> Self {
        // access to this address is checked
        let buf_phys_addr = GuestAddress(buf_phys_addr);
        if !guest_memory.memory().check_range(
            buf_phys_addr,
            std::mem::size_of::<MemctlResp>().max(std::mem::size_of::<MemctlReq>()),
        ) {
            warn!("guest sent invalid phys addr {:#x}", buf_phys_addr.0);
            return MemctlState::Broken;
        }
        let conn = {
            // find an available port+byte combination, and fail if full
            let mut next_conn = state.next_conn;
            while state.port_buf_map.contains_key(&next_conn) {
                next_conn = next_conn.next();
                if next_conn == state.next_conn {
                    warn!("port+byte combination exhausted");
                    return MemctlState::Broken;
                }
            }
            next_conn
        };
        state.next_conn = conn.next();
        state.port_buf_map.insert(conn, buf_phys_addr);
        state.done_cpus += 1;

        // inform guest of the port+byte combination
        let response = MemctlTransport::connect_response(conn.port as u64, conn.byte as u64);

        if let Err(err) = guest_memory
            .memory()
            .write_obj(response, state.transport_addr)
        {
            warn!(
                "failed to write to transport buffer during percpu init {}",
                err
            );
            return MemctlState::Broken;
        }

        if state.done_cpus == state.nr_cpus {
            MemctlState::Ready(state.port_buf_map)
        } else {
            MemctlState::PercpuInit(state)
        }
    }

    fn read_transport(
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
        transport_buf_addr: GuestAddress,
    ) -> Result<MemctlTransport, Self> {
        guest_memory
            .memory()
            .read_obj(transport_buf_addr)
            .map_err(|_| {
                warn!("failed to read from transport addr");
                MemctlState::Broken
            })
    }

    fn handle_percpu_init(
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
        state: PercpuInitState,
    ) -> Self {
        Self::read_transport(guest_memory, state.transport_addr).map_or_else(
            |s| s,
            |transport_buf| {
                if let Some(connect) = transport_buf.as_connect() {
                    Self::do_handle_percpu_init(guest_memory, state, connect)
                } else {
                    warn!("incorrect transport type during percpu init");
                    MemctlState::Broken
                }
            },
        )
    }

    fn handle_transport_available(
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
        transport_addr: GuestAddress,
    ) -> Self {
        Self::read_transport(guest_memory, transport_addr).map_or_else(
            |s| s,
            |transport| {
                if let Some(connect) = transport.as_connect() {
                    Self::do_handle_percpu_init(
                        guest_memory,
                        // Guest requests are required to send requests
                        // If the request is invalid, nr_cpu is a junk value
                        PercpuInitState::new(transport_addr, connect.nr_cpus),
                        connect,
                    )
                } else {
                    Self::do_handle_disconnect_request(transport, transport_addr, guest_memory)
                }
            },
        )
    }

    fn handle_transport_init(
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
        mut bytes: Vec<u8>,
        byte: u8,
    ) -> Self {
        match bytes.len() {
            i if i >= 8 => {
                warn!("incorrect transport buffer addr size");
                MemctlState::Broken
            }
            i if i == 7 => {
                bytes.push(byte);
                let mut arr: [u8; 8] = [0; 8];
                arr.copy_from_slice(&bytes);
                let addr = GuestAddress(u64::from_le_bytes(arr));
                // ack the write by writing the received address to
                // guest memory
                let ack = MemctlTransport::ack(addr);
                if let Err(err) = guest_memory.memory().write_obj(ack, addr) {
                    warn!("failed to ack transport buffer {}", err);
                    MemctlState::Broken
                } else {
                    MemctlState::TransportAvailable(addr)
                }
            }
            i if i < 7 => {
                bytes.push(byte);
                MemctlState::TransportInit(bytes)
            }
            _ => unreachable!(),
        }
    }

    fn handle_disconnect_request(
        addr: GuestAddress,
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
    ) -> Self {
        Self::read_transport(guest_memory, addr).map_or_else(
            |s| s,
            |transport_buf| Self::do_handle_disconnect_request(transport_buf, addr, guest_memory),
        )
    }

    fn do_handle_disconnect_request(
        transport: MemctlTransport,
        addr: GuestAddress,
        guest_memory: &GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
    ) -> Self {
        if !transport.is_disconnect() {
            MemctlState::Broken
        } else {
            if guest_memory
                .memory()
                .write_obj(MemctlTransport::ack(addr), addr)
                .is_err()
            {
                warn!("failed to ack device teardown");
                MemctlState::Broken
            } else {
                MemctlState::TransportInit(Vec::new())
            }
        }
    }
}

pub struct Memctl {
    id: String,
    mem: GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
    state: RwLock<MemctlState>,
}

impl Memctl {
    /// f is called with the host address of `range_base` and only when
    /// [`range_base`, `range_base` + `range_len`) is present in the guest
    fn operate_on_memory_range<F>(&self, addr: u64, length: u64, f: F) -> result::Result<(), Error>
    where
        F: FnOnce(*mut libc::c_void, libc::size_t) -> libc::c_int,
    {
        let memory = self.mem.memory();
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

    fn madvise(&self, addr: u64, length: u64, advice: libc::c_int) -> result::Result<(), Error> {
        debug!("addr {:X} length {} advice {}", addr, length, advice);
        self.operate_on_memory_range(addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::madvise(base, len, advice)
        })
    }

    fn mlock(&self, addr: u64, length: u64, on_default: bool) -> result::Result<(), Error> {
        self.operate_on_memory_range(addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::mlock2(base, len, if on_default { libc::MLOCK_ONFAULT } else { 0 })
        })
    }

    fn munlock(&self, addr: u64, length: u64) -> result::Result<(), Error> {
        self.operate_on_memory_range(addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::munlock(base, len)
        })
    }

    fn mprotect(
        &self,
        addr: u64,
        length: u64,
        protection: libc::c_int,
    ) -> result::Result<(), Error> {
        self.operate_on_memory_range(addr, length, |base, len| unsafe {
            // SAFETY: [`base`, `base` + `len`) is guest memory
            libc::mprotect(base, len, protection)
        })
    }

    fn set_vma_anon_name(&self, addr: u64, length: u64, name: u64) -> result::Result<(), Error> {
        let name = (name != 0).then(|| CString::new(format!("memctl-{}", name)).unwrap());
        let name_ptr = if let Some(name) = &name {
            name.as_ptr()
        } else {
            std::ptr::null()
        };
        debug!("addr {:X} length {} name {:?}", addr, length, name);

        self.operate_on_memory_range(addr, length, |base, len| unsafe {
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

    fn process_request(
        &self,
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
            FunctionCode::Dontneed => self.madvise(addr, length, libc::MADV_DONTNEED),
            FunctionCode::Remove => self.madvise(addr, length, libc::MADV_REMOVE),
            FunctionCode::Free => self.madvise(addr, length, libc::MADV_FREE),
            FunctionCode::Pageout => self.madvise(addr, length, libc::MADV_PAGEOUT),
            FunctionCode::Unmergeable => self.madvise(addr, length, libc::MADV_UNMERGEABLE),
            FunctionCode::Dontdump => self.madvise(addr, length, libc::MADV_DONTDUMP),
            FunctionCode::Mlock => self.mlock(addr, length, false),
            FunctionCode::Munlock => self.munlock(addr, length),
            FunctionCode::MprotectNone => self.mprotect(addr, length, libc::PROT_NONE),
            FunctionCode::MprotectR => self.mprotect(addr, length, libc::PROT_READ),
            FunctionCode::MprotectW => self.mprotect(addr, length, libc::PROT_WRITE),
            FunctionCode::MprotectRW => {
                self.mprotect(addr, length, libc::PROT_READ | libc::PROT_WRITE)
            }
            FunctionCode::SetVMAAnonName => self.set_vma_anon_name(addr, length, arg),
        };
        result.map(|_| MemctlResp::default())
    }

    fn handle_request(
        &self,
        MemctlReq {
            func_code,
            addr,
            length,
            arg,
        }: MemctlReq,
    ) -> Result<MemctlResp, Error> {
        let resp_or_err = FunctionCode::try_from(func_code)
            .map_err(|_| Error::UnknownFunctionCode(func_code))
            .and_then(|func_code| self.process_request(func_code, addr, length, arg));

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
                Error::GuestMemory(err) => {
                    warn!("{}", err);
                    MemctlResp {
                        ret_errno: libc::EINVAL as u32,
                        ret_code: func_code as u32,
                        ..Default::default()
                    }
                }
                // device error, stop responding
                other => return Err(other),
            },
        };
        Ok(resp)
    }

    fn handle_memctl_request(
        &self,
        conn_map: &HashMap<GuestConnection, GuestAddress>,
        port: u32,
        byte: u8,
    ) {
        let guest_addr = if let Some(x) = conn_map.get(&GuestConnection { port, byte }) {
            x
        } else {
            warn!(
                "port {} byte {} does not have an established connection",
                port, byte
            );
            return;
        };

        let request: MemctlReq = if let Ok(x) = self.mem.memory().read_obj(*guest_addr) {
            x
        } else {
            warn!("cannot read from guest address {:#x}", guest_addr.0);
            return;
        };

        let response: MemctlResp = match self.handle_request(request) {
            Ok(x) => x,
            Err(e) => {
                warn!("cannot process request {:?} with error {}", request, e);
                return;
            }
        };

        if self.mem.memory().write_obj(response, *guest_addr).is_err() {
            warn!("cannot write to guest address {:#x}", guest_addr.0);
        }
    }

    fn handle_guest_write(&self, port: u64, data: u8) {
        if port == PORT as u64 && data == CONTROL_BYTE {
            let mut state = self.state.write().expect("failed to acquire write lock");

            *state = match std::mem::replace(&mut *state, MemctlState::Broken) {
                // init transport addr byte can be control byte
                MemctlState::TransportInit(bytes) => {
                    MemctlState::handle_transport_init(&self.mem, bytes, data)
                }
                MemctlState::TransportAvailable(transport_buf_addr) => {
                    MemctlState::handle_transport_available(&self.mem, transport_buf_addr)
                }
                MemctlState::PercpuInit(state) => MemctlState::handle_percpu_init(&self.mem, state),
                // use control byte to clean up and return the device to a pristine state
                MemctlState::Ready(map) => {
                    let transport_addr = map.get(&GuestConnection::new(PORT, CONTROL_BYTE));

                    if let Some(addr) = transport_addr {
                        MemctlState::handle_disconnect_request(*addr, &self.mem)
                    } else {
                        warn!("cannot find transport addr during teardown");
                        MemctlState::Broken
                    }
                }
                MemctlState::Broken => {
                    warn!("broken communcation on port {} data {}", port, data);
                    MemctlState::Broken
                }
            }
        } else {
            let state = self.state.read().expect("failed to acquire read lock");
            match &*state {
                MemctlState::Ready(map) => self.handle_memctl_request(map, port as u32, data),
                // during transport init, the byte is used to send over the address of the
                // transport shared buffer.
                // since we've taken the read lock, drop it and re-take in write mode
                MemctlState::TransportInit(_) => {
                    drop(state);
                    let mut state = self
                        .state
                        .write()
                        .expect("failed to acquire write lock for transport init");

                    *state = match std::mem::replace(&mut *state, MemctlState::Broken) {
                        MemctlState::Ready(map) => {
                            warn!("race in initializing device");
                            self.handle_memctl_request(&map, port as u32, data);
                            MemctlState::Ready(map)
                        }
                        // consume init transport addr byte
                        MemctlState::TransportInit(bytes) => {
                            MemctlState::handle_transport_init(&self.mem, bytes, data)
                        }
                        s => {
                            warn!("device not ready; cannot handle memctl requests");
                            s
                        }
                    };
                }
                _ => {
                    warn!("device not ready; cannot handle memctl requests");
                }
            }
        }
    }

    pub fn new(
        id: String,
        mem: GuestMemoryAtomic<GuestMemoryMmap<AtomicBitmap>>,
    ) -> io::Result<Memctl> {
        Ok(Memctl {
            id,
            mem,
            state: RwLock::new(MemctlState::TransportInit(Vec::new())),
        })
    }
}

impl Pausable for Memctl {
    fn pause(&mut self) -> std::result::Result<(), MigratableError> {
        Ok(())
    }

    fn resume(&mut self) -> std::result::Result<(), MigratableError> {
        Ok(())
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

impl BusDeviceSync for Memctl {
    fn read(&self, _base: u64, _offset: u64, _data: &mut [u8]) {
        warn!("memctl read, not supposed to happen");
    }

    fn write(&self, base: u64, offset: u64, data: &[u8]) -> Option<Arc<Barrier>> {
        if data.len() != 1 {
            warn!(
                "io bus on base {}, offset {}, wrong number of bytes {}",
                base,
                offset,
                data.len()
            )
        } else {
            self.handle_guest_write(base, data[0])
        }
        None
    }
}
