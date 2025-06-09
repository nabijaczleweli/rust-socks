//! SOCKS proxy clients
#![doc(html_root_url="https://docs.rs/socks/0.3.0")]
#![warn(missing_docs)]

extern crate byteorder;

#[cfg(unix)]
extern crate libc;
#[cfg(windows)]
extern crate winapi;

use std::io;
use std::net::{
    Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6, TcpStream, ToSocketAddrs,
};
#[cfg(unix)]
use std::os::unix::net::{UnixStream, SocketAddr as UnixSocketAddr};
#[cfg(any(target_os = "linux", target_os = "android"))]
use std::os::linux::net::SocketAddrExt;
use std::hash::{Hash, Hasher};
use std::vec;

pub use v4::{Socks4Listener, Socks4Stream};
pub use v5::{Socks5Datagram, Socks5Listener, Socks5Stream};

mod v4;
mod v5;
mod writev;

/// Either a [`SocketAddr`], or, under unix, [`UnixSocketAddr`]
///
/// If `#[cfg(unix)]`, this can hold an internet socket address *or* a unix-domain socket address.
///
/// Otherwise, this can only hold an internet socket address.
#[derive(Clone, Debug)]
pub enum SocketAddrOrUnixSocketAddr {
    /// The internet address.
    SocketAddr(SocketAddr),
    /// The unix-domain address.
    #[cfg(unix)]
    UnixSocketAddr(UnixSocketAddr),
}

impl PartialEq for SocketAddrOrUnixSocketAddr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            #[cfg(unix)]
            (Self::SocketAddr(_), Self::UnixSocketAddr(_)) => false,
            #[cfg(unix)]
            (Self::UnixSocketAddr(_), Self::SocketAddr(_)) => false,
            (Self::SocketAddr(l), Self::SocketAddr(r)) => l == r,
            #[cfg(unix)]
            (Self::UnixSocketAddr(l), Self::UnixSocketAddr(r)) => {
                if (l.is_unnamed() && r.is_unnamed()) || (l.as_pathname() == r.as_pathname()) {
                    return true;
                }
                #[cfg(any(target_os = "linux", target_os = "android"))]
                if l.as_abstract_name() == r.as_abstract_name() {
                    return true;
                }
                false
            },
        }
    }
}

impl Hash for SocketAddrOrUnixSocketAddr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::SocketAddr(a) => a.hash(state),
            #[cfg(unix)]
            Self::UnixSocketAddr(a) => {
                a.is_unnamed().hash(state);
                a.as_pathname().hash(state);
                #[cfg(any(target_os = "linux", target_os = "android"))]
                a.as_abstract_name().hash(state);
            }
        }
    }
}

impl Into<SocketAddrOrUnixSocketAddr> for &SocketAddrOrUnixSocketAddr {
    fn into(self) -> SocketAddrOrUnixSocketAddr {
        self.clone() // no allocations, this struct is effectively Copy
    }
}
impl Into<SocketAddrOrUnixSocketAddr> for &mut SocketAddrOrUnixSocketAddr {
    fn into(self) -> SocketAddrOrUnixSocketAddr {
        self.clone() // no allocations, this struct is effectively Copy
    }
}
impl Into<SocketAddrOrUnixSocketAddr> for SocketAddr {
    fn into(self) -> SocketAddrOrUnixSocketAddr {
        SocketAddrOrUnixSocketAddr::SocketAddr(self)
    }
}
impl Into<SocketAddrOrUnixSocketAddr> for &SocketAddr {
    fn into(self) -> SocketAddrOrUnixSocketAddr {
        SocketAddrOrUnixSocketAddr::SocketAddr(self.clone())
    }
}
#[cfg(unix)]
impl Into<SocketAddrOrUnixSocketAddr> for UnixSocketAddr {
    fn into(self) -> SocketAddrOrUnixSocketAddr {
        SocketAddrOrUnixSocketAddr::UnixSocketAddr(self)
    }
}

/// Either a [`TcpStream`], or, under unix, [`UnixStream`]
///
/// If `#[cfg(unix)]`, this can hold an internet socket *or* a unix-domain socket.
///
/// Otherwise, this can only hold an internet socket.
#[derive(Debug)]
pub enum TcpOrUnixStream {
    /// The internet socket.
    Tcp(TcpStream),
    #[cfg(unix)]
    /// The unix-domain socket.
    Unix(UnixStream),
}

macro_rules! fwd {
    ($self:expr, $fun:ident) => {
        match $self {
            TcpOrUnixStream::Tcp(ref mut s) => s.$fun(),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(ref mut s) => s.$fun(),
        }
    };
    ($self:expr, $fun:ident, $arg:expr) => {
        match $self {
            TcpOrUnixStream::Tcp(ref mut s) => s.$fun($arg),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(ref mut s) => s.$fun($arg),
        }
    }
}

macro_rules! fwd_ref {
    ($self:expr, $fun:ident) => {
        match $self {
            TcpOrUnixStream::Tcp(s) => (&mut &*s).$fun(),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => (&mut &*s).$fun(),
        }
    };
    ($self:expr, $fun:ident, $arg:expr) => {
        match $self {
            TcpOrUnixStream::Tcp(s) => (&mut &*s).$fun($arg),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => (&mut &*s).$fun($arg),
        }
    }
}

macro_rules! fwd_move {
    ($self:expr, $fun:ident) => {
        match $self {
            TcpOrUnixStream::Tcp(s) => s.$fun(),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => s.$fun(),
        }
    };
    ($self:expr, $fun:ident, $arg:expr) => {
        match $self {
            TcpOrUnixStream::Tcp(s) => s.$fun($arg),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => s.$fun($arg),
        }
    }
}

impl TcpOrUnixStream {
    /// [`TcpStream::connect`] or [`UnixStream::connect_addr`]
    pub fn connect<T: Into<SocketAddrOrUnixSocketAddr>>(addr: T) -> std::io::Result<TcpOrUnixStream> {
        match addr.into() {
            SocketAddrOrUnixSocketAddr::SocketAddr(s) => TcpStream::connect(s).map(TcpOrUnixStream::Tcp),
            #[cfg(unix)]
            SocketAddrOrUnixSocketAddr::UnixSocketAddr(s) => UnixStream::connect_addr(&s).map(TcpOrUnixStream::Unix),
        }
    }

    /// [`TcpStream::connect`] with [`ToSocketAddrs`]
    pub fn connect_tsa<T: ToSocketAddrs>(addr: T) -> std::io::Result<TcpOrUnixStream> {
        TcpStream::connect(addr).map(TcpOrUnixStream::Tcp)
    }

    /// [`TcpStream::local_addr`] or [`UnixStream::local_addr`]
    pub fn local_addr(&self) -> std::io::Result<SocketAddrOrUnixSocketAddr> {
        match self {
            TcpOrUnixStream::Tcp(s) => s.local_addr().map(SocketAddrOrUnixSocketAddr::SocketAddr),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => s.local_addr().map(SocketAddrOrUnixSocketAddr::UnixSocketAddr),
        }
    }

    /// [`TcpStream::peer_addr`] or [`UnixStream::peer_addr`]
    pub fn peer_addr(&self) -> std::io::Result<SocketAddrOrUnixSocketAddr> {
        match self {
            TcpOrUnixStream::Tcp(s) => s.peer_addr().map(SocketAddrOrUnixSocketAddr::SocketAddr),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => s.peer_addr().map(SocketAddrOrUnixSocketAddr::UnixSocketAddr),
        }
    }

    /// [`TcpStream::read_timeout`] or [`UnixStream::read_timeout`]
    pub fn read_timeout(&self) -> std::io::Result<Option<std::time::Duration>> {
        fwd_ref!(self, read_timeout)
    }

    /// [`TcpStream::set_nonblocking`] or [`UnixStream::set_nonblocking`]
    pub fn set_nonblocking(&self, nonblocking: bool) -> std::io::Result<()> {
        fwd_ref!(self, set_nonblocking, nonblocking)
    }

    /// [`TcpStream::set_read_timeout`] or [`UnixStream::set_read_timeout`]
    pub fn set_read_timeout(&self, timeout: Option<std::time::Duration>) -> std::io::Result<()> {
        fwd_ref!(self, set_read_timeout, timeout)
    }

    /// [`TcpStream::set_write_timeout`] or [`UnixStream::set_write_timeout`]
    pub fn set_write_timeout(&self, timeout: Option<std::time::Duration>) -> std::io::Result<()> {
        fwd_ref!(self, set_write_timeout, timeout)
    }

    /// [`TcpStream::shutdown`] or [`UnixStream::shutdown`]
    pub fn shutdown(&self, how: std::net::Shutdown) -> std::io::Result<()> {
        fwd_ref!(self, shutdown, how)
    }

    /// [`TcpStream::take_error`] or [`UnixStream::take_error`]
    pub fn take_error(&self) -> std::io::Result<Option<std::io::Error>> {
        fwd_ref!(self, take_error)
    }

    /// [`TcpStream::try_clone`] or [`UnixStream::try_clone`]
    pub fn try_clone(&self) -> std::io::Result<TcpOrUnixStream> {
        match self {
            TcpOrUnixStream::Tcp(s) => s.try_clone().map(TcpOrUnixStream::Tcp),
            #[cfg(unix)]
            TcpOrUnixStream::Unix(s) => s.try_clone().map(TcpOrUnixStream::Unix),
        }
    }

    /// [`TcpStream::write_timeout`] or [`UnixStream::write_timeout`]
    pub fn write_timeout(&self) -> std::io::Result<Option<std::time::Duration>> {
        fwd_ref!(self, write_timeout)
    }
}

impl io::Read for TcpOrUnixStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        fwd!(self, read, buf)
    }
    fn read_vectored(&mut self, bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> {
        fwd!(self, read_vectored, bufs)
    }
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize> {
        fwd!(self, read_to_end, buf)
    }
    fn read_to_string(&mut self, buf: &mut String) -> std::io::Result<usize> {
        fwd!(self, read_to_string, buf)
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        fwd!(self, read_exact, buf)
    }
}

impl<'a> io::Read for &'a TcpOrUnixStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        fwd_ref!(self, read, buf)
    }
    fn read_vectored(&mut self, bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize> {
        fwd_ref!(self, read_vectored, bufs)
    }
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize> {
        fwd_ref!(self, read_to_end, buf)
    }
    fn read_to_string(&mut self, buf: &mut String) -> std::io::Result<usize> {
        fwd_ref!(self, read_to_string, buf)
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()> {
        fwd_ref!(self, read_exact, buf)
    }
}

impl<'a> io::Write for &'a TcpOrUnixStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        fwd_ref!(self, write, buf)
    }
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        fwd_ref!(self, write_vectored, bufs)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        fwd_ref!(self, flush)
    }
    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
        fwd_ref!(self, write_all, buf)
    }
    fn write_fmt(&mut self, fmt: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        fwd_ref!(self, write_fmt, fmt)
    }
}

impl io::Write for TcpOrUnixStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        fwd!(self, write, buf)
    }
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        fwd!(self, write_vectored, bufs)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        fwd!(self, flush)
    }
    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
        fwd!(self, write_all, buf)
    }
    fn write_fmt(&mut self, fmt: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        fwd!(self, write_fmt, fmt)
    }
}

#[cfg(unix)]
impl std::os::fd::AsRawFd for TcpOrUnixStream {
    fn as_raw_fd(&self) -> std::os::fd::RawFd {
        fwd_ref!(self, as_raw_fd)
    }
}

#[cfg(windows)]
impl std::os::windows::io::AsRawSocket for TcpOrUnixStream {
    fn as_raw_socket(&self) -> std::os::windows::io::RawSocket {
        fwd_ref!(self, as_raw_socket)
    }
}

#[cfg(unix)]
impl std::os::fd::IntoRawFd for TcpOrUnixStream {
    fn into_raw_fd(self) -> std::os::fd::RawFd {
        fwd_move!(self, into_raw_fd)
    }
}

#[cfg(windows)]
impl std::os::windows::io::IntoRawSocket for TcpOrUnixStream {
    fn into_raw_socket(self) -> std::os::windows::io::RawSocket {
        fwd_move!(self, into_raw_socket)
    }
}

impl Into<TcpOrUnixStream> for TcpStream {
    fn into(self) -> TcpOrUnixStream {
        TcpOrUnixStream::Tcp(self)
    }
}
#[cfg(unix)]
impl Into<TcpOrUnixStream> for UnixStream {
    fn into(self) -> TcpOrUnixStream {
        TcpOrUnixStream::Unix(self)
    }
}

/// A description of a connection target.
#[derive(Debug, Clone)]
pub enum TargetAddr {
    /// Connect to an IP address.
    Ip(SocketAddr),
    /// Connect to a fully qualified domain name.
    ///
    /// The domain name will be passed along to the proxy server and DNS lookup
    /// will happen there.
    Domain(String, u16),
}

impl ToSocketAddrs for TargetAddr {
    type Iter = Iter;

    fn to_socket_addrs(&self) -> io::Result<Iter> {
        let inner = match *self {
            TargetAddr::Ip(addr) => IterInner::Ip(Some(addr)),
            TargetAddr::Domain(ref domain, port) => {
                let it = (&**domain, port).to_socket_addrs()?;
                IterInner::Domain(it)
            }
        };
        Ok(Iter(inner))
    }
}

enum IterInner {
    Ip(Option<SocketAddr>),
    Domain(vec::IntoIter<SocketAddr>),
}

/// An iterator over `SocketAddr`s associated with a `TargetAddr`.
pub struct Iter(IterInner);

impl Iterator for Iter {
    type Item = SocketAddr;

    fn next(&mut self) -> Option<SocketAddr> {
        match self.0 {
            IterInner::Ip(ref mut addr) => addr.take(),
            IterInner::Domain(ref mut it) => it.next(),
        }
    }
}

/// A trait for objects that can be converted to `TargetAddr`.
pub trait ToTargetAddr {
    /// Converts the value of `self` to a `TargetAddr`.
    fn to_target_addr(&self) -> io::Result<TargetAddr>;
}

impl ToTargetAddr for TargetAddr {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        Ok(self.clone())
    }
}

impl ToTargetAddr for SocketAddr {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        Ok(TargetAddr::Ip(*self))
    }
}

impl ToTargetAddr for SocketAddrV4 {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        SocketAddr::V4(*self).to_target_addr()
    }
}

impl ToTargetAddr for SocketAddrV6 {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        SocketAddr::V6(*self).to_target_addr()
    }
}

impl ToTargetAddr for (Ipv4Addr, u16) {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        SocketAddrV4::new(self.0, self.1).to_target_addr()
    }
}

impl ToTargetAddr for (Ipv6Addr, u16) {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        SocketAddrV6::new(self.0, self.1, 0, 0).to_target_addr()
    }
}

impl<'a> ToTargetAddr for (&'a str, u16) {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        // try to parse as an IP first
        if let Ok(addr) = self.0.parse::<Ipv4Addr>() {
            return (addr, self.1).to_target_addr();
        }

        if let Ok(addr) = self.0.parse::<Ipv6Addr>() {
            return (addr, self.1).to_target_addr();
        }

        Ok(TargetAddr::Domain(self.0.to_owned(), self.1))
    }
}

impl<'a> ToTargetAddr for &'a str {
    fn to_target_addr(&self) -> io::Result<TargetAddr> {
        // try to parse as an IP first
        if let Ok(addr) = self.parse::<SocketAddrV4>() {
            return addr.to_target_addr();
        }

        if let Ok(addr) = self.parse::<SocketAddrV6>() {
            return addr.to_target_addr();
        }

        // split the string by ':' and convert the second part to u16
        let mut parts_iter = self.rsplitn(2, ':');
        let port_str = match parts_iter.next() {
            Some(s) => s,
            None => {
                return Err(io::Error::new(io::ErrorKind::InvalidInput, "invalid socket address"))
            }
        };

        let host = match parts_iter.next() {
            Some(s) => s,
            None => {
                return Err(io::Error::new(io::ErrorKind::InvalidInput, "invalid socket address"))
            }
        };

        let port: u16 = match port_str.parse() {
            Ok(p) => p,
            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "invalid port value")),
        };

        (host, port).to_target_addr()
    }
}
