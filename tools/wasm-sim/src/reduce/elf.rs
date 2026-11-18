//! Minimal ELF64 little-endian reader: section headers, `.symtab` function symbols, and the
//! bytes of a virtual address range in an allocated section.

use anyhow::{Context, Result, bail};

pub struct Section {
    pub name: String,
    pub addr: u64,
    pub offset: u64,
    pub size: u64,
    pub kind: u32,
    pub flags: u64,
    pub link: u32,
}

pub struct Symbol {
    pub name: String,
    pub value: u64,
    pub size: u64,
    pub is_func: bool,
}

pub struct Elf {
    pub bytes: Vec<u8>,
    pub sections: Vec<Section>,
    pub symbols: Vec<Symbol>,
}

fn u16_at(b: &[u8], o: usize) -> Result<u16> {
    Ok(u16::from_le_bytes(
        b.get(o..o + 2).context("truncated ELF")?.try_into()?,
    ))
}
fn u32_at(b: &[u8], o: usize) -> Result<u32> {
    Ok(u32::from_le_bytes(
        b.get(o..o + 4).context("truncated ELF")?.try_into()?,
    ))
}
fn u64_at(b: &[u8], o: usize) -> Result<u64> {
    Ok(u64::from_le_bytes(
        b.get(o..o + 8).context("truncated ELF")?.try_into()?,
    ))
}
fn cstr(b: &[u8], o: usize) -> String {
    let end = b[o..]
        .iter()
        .position(|&c| c == 0)
        .map_or(b.len(), |p| o + p);
    String::from_utf8_lossy(&b[o..end]).into_owned()
}

impl Elf {
    pub fn parse(bytes: Vec<u8>) -> Result<Elf> {
        if bytes.get(0..4) != Some(b"\x7fELF") || bytes[4] != 2 || bytes[5] != 1 {
            bail!("not an ELF64 little-endian file");
        }
        if u16_at(&bytes, 18)? != 62 {
            bail!("not an x86-64 ELF (e_machine != EM_X86_64)");
        }
        let shoff = u64_at(&bytes, 0x28)? as usize;
        let shentsize = u16_at(&bytes, 0x3a)? as usize;
        let shnum = u16_at(&bytes, 0x3c)? as usize;
        let shstrndx = u16_at(&bytes, 0x3e)? as usize;
        let mut raw = Vec::new();
        for i in 0..shnum {
            let o = shoff + i * shentsize;
            raw.push((
                u32_at(&bytes, o)?,
                Section {
                    name: String::new(),
                    kind: u32_at(&bytes, o + 4)?,
                    flags: u64_at(&bytes, o + 8)?,
                    addr: u64_at(&bytes, o + 0x10)?,
                    offset: u64_at(&bytes, o + 0x18)?,
                    size: u64_at(&bytes, o + 0x20)?,
                    link: u32_at(&bytes, o + 0x28)?,
                },
            ));
        }
        let stroff = raw.get(shstrndx).context("bad e_shstrndx")?.1.offset as usize;
        let sections: Vec<Section> = raw
            .into_iter()
            .map(|(n, mut s)| {
                s.name = cstr(&bytes, stroff + n as usize);
                s
            })
            .collect();
        let mut symbols = Vec::new();
        for s in sections.iter().filter(|s| s.kind == 2) {
            let strtab = sections
                .get(s.link as usize)
                .context("bad symtab link")?
                .offset as usize;
            for k in 0..(s.size / 24) as usize {
                let o = s.offset as usize + k * 24;
                let name = cstr(&bytes, strtab + u32_at(&bytes, o)? as usize);
                let info = bytes[o + 4];
                symbols.push(Symbol {
                    name,
                    value: u64_at(&bytes, o + 8)?,
                    size: u64_at(&bytes, o + 16)?,
                    is_func: info & 0xf == 2,
                });
            }
        }
        Ok(Elf {
            bytes,
            sections,
            symbols,
        })
    }

    /// The bytes at virtual addresses `[addr, addr + len)` of an allocated PROGBITS section.
    pub fn read(&self, addr: u64, len: u64) -> Result<&[u8]> {
        for s in &self.sections {
            if s.kind == 1 && s.flags & 2 != 0 && s.addr <= addr && addr + len <= s.addr + s.size {
                let o = (s.offset + (addr - s.addr)) as usize;
                return Ok(&self.bytes[o..o + len as usize]);
            }
        }
        bail!("no allocated section holds {addr:#x}..{:#x}", addr + len)
    }

    pub fn symbol(&self, name: &str) -> Result<&Symbol> {
        self.symbols
            .iter()
            .find(|s| s.name == name)
            .with_context(|| format!("no symbol `{name}`"))
    }

    /// The `.text` section (address and bytes).
    pub fn text(&self) -> Result<(u64, &[u8])> {
        let s = self
            .sections
            .iter()
            .find(|s| s.name == ".text")
            .context("no .text section")?;
        Ok((
            s.addr,
            &self.bytes[s.offset as usize..(s.offset + s.size) as usize],
        ))
    }
}
