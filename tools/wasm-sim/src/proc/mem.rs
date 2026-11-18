//! Host memory model: a sparse 64-bit address space of 4 KiB pages (the Rust twin of
//! `examples/wasm-sim/proc/wat/mem.wat`). Unmapped access = fault. No permissions.

use std::collections::HashMap;

pub const PAGE: u64 = 4096;

#[derive(Default, Clone)]
pub struct Mem {
    pages: HashMap<u64, Box<[u8; PAGE as usize]>>,
}

impl Mem {
    /// Map (zero-filled) every page meeting `[addr, addr + len)`; returns the number of new pages.
    pub fn map(&mut self, addr: u64, len: u64) -> usize {
        let (lo, hi) = (addr / PAGE, addr.saturating_add(len).div_ceil(PAGE));
        let mut n = 0;
        for p in lo..hi {
            self.pages.entry(p).or_insert_with(|| {
                n += 1;
                Box::new([0; PAGE as usize])
            });
        }
        n
    }

    pub fn mapped(&self, addr: u64) -> bool {
        self.pages.contains_key(&(addr / PAGE))
    }

    pub fn pages(&self) -> impl Iterator<Item = (u64, &[u8; PAGE as usize])> {
        self.pages.iter().map(|(k, v)| (k * PAGE, &**v))
    }

    pub fn load8(&self, a: u64) -> Option<u8> {
        self.pages.get(&(a / PAGE)).map(|p| p[(a % PAGE) as usize])
    }

    pub fn store8(&mut self, a: u64, v: u8) -> Option<()> {
        self.pages
            .get_mut(&(a / PAGE))
            .map(|p| p[(a % PAGE) as usize] = v)
    }

    /// Little-endian load of `n <= 8` bytes, zero-extended.
    pub fn load(&self, a: u64, n: usize) -> Option<u64> {
        let off = (a % PAGE) as usize;
        if off + n <= PAGE as usize {
            let p = self.pages.get(&(a / PAGE))?;
            let mut b = [0u8; 8];
            b[..n].copy_from_slice(&p[off..off + n]);
            return Some(u64::from_le_bytes(b));
        }
        let mut v = 0u64;
        for i in 0..n {
            v |= (self.load8(a.wrapping_add(i as u64))? as u64) << (8 * i);
        }
        Some(v)
    }

    pub fn store(&mut self, a: u64, n: usize, v: u64) -> Option<()> {
        let off = (a % PAGE) as usize;
        if off + n <= PAGE as usize {
            let p = self.pages.get_mut(&(a / PAGE))?;
            p[off..off + n].copy_from_slice(&v.to_le_bytes()[..n]);
            return Some(());
        }
        for i in 0..n {
            self.store8(a.wrapping_add(i as u64), (v >> (8 * i)) as u8)?;
        }
        Some(())
    }

    pub fn read_bytes(&self, a: u64, len: usize) -> Option<Vec<u8>> {
        (0..len)
            .map(|i| self.load8(a.wrapping_add(i as u64)))
            .collect()
    }

    pub fn write_bytes(&mut self, a: u64, bytes: &[u8]) -> Option<()> {
        for (i, b) in bytes.iter().enumerate() {
            self.store8(a.wrapping_add(i as u64), *b)?;
        }
        Some(())
    }

    pub fn read_cstr(&self, a: u64, max: usize) -> Option<Vec<u8>> {
        let mut out = Vec::new();
        for i in 0..max {
            match self.load8(a.wrapping_add(i as u64))? {
                0 => return Some(out),
                b => out.push(b),
            }
        }
        Some(out)
    }
}
