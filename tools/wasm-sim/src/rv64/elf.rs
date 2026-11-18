//! Minimal ELF64 little-endian reader: entry, PT_LOAD segments, sections and
//! function/label symbols (enough for static RV64 test programs).

use wasmtime::error::{Result, bail};

pub struct Segment {
    pub vaddr: u64,
    pub data: Vec<u8>,
    pub memsz: u64,
    pub exec: bool,
    /// p_flags (PF_X 1, PF_W 2, PF_R 4)
    pub flags: u32,
}

pub struct Section {
    pub name: String,
    pub addr: u64,
    pub data: Vec<u8>,
    pub exec: bool,
}

pub struct Elf {
    pub entry: u64,
    pub segments: Vec<Segment>,
    pub sections: Vec<Section>,
    pub symbols: Vec<(String, u64)>,
    /// symbol sizes (0 when the assembler recorded none), parallel to `symbols`
    pub sizes: Vec<u64>,
}

fn u16_(b: &[u8], o: usize) -> u64 {
    u16::from_le_bytes(b[o..o + 2].try_into().unwrap()) as u64
}
fn u32_(b: &[u8], o: usize) -> u64 {
    u32::from_le_bytes(b[o..o + 4].try_into().unwrap()) as u64
}
fn u64_(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}
fn cstr(b: &[u8], o: usize) -> String {
    let e = b[o..].iter().position(|&c| c == 0).unwrap_or(0);
    String::from_utf8_lossy(&b[o..o + e]).into_owned()
}

pub fn parse(b: &[u8]) -> Result<Elf> {
    if b.len() < 64 || &b[0..4] != b"\x7fELF" || b[4] != 2 || b[5] != 1 {
        bail!("not an ELF64 LE file");
    }
    if u16_(b, 18) != 243 {
        bail!("not a RISC-V ELF");
    }
    let entry = u64_(b, 24);
    let (phoff, shoff) = (u64_(b, 32) as usize, u64_(b, 40) as usize);
    let (phnum, shnum, shstrndx) = (
        u16_(b, 56) as usize,
        u16_(b, 60) as usize,
        u16_(b, 62) as usize,
    );
    let mut segments = vec![];
    for i in 0..phnum {
        let p = phoff + i * 56;
        if u32_(b, p) != 1 {
            continue;
        }
        let flags = u32_(b, p + 4);
        let off = u64_(b, p + 8) as usize;
        let vaddr = u64_(b, p + 16);
        let filesz = u64_(b, p + 32) as usize;
        let memsz = u64_(b, p + 40);
        segments.push(Segment {
            vaddr,
            data: b[off..off + filesz].to_vec(),
            memsz,
            exec: flags & 1 != 0,
            flags: flags as u32,
        });
    }
    let mut sections = vec![];
    let mut symbols = vec![];
    let mut sizes = vec![];
    if shoff != 0 {
        let sh = |i: usize| shoff + i * 64;
        let stroff = u64_(b, sh(shstrndx) + 24) as usize;
        for i in 0..shnum {
            let s = sh(i);
            let name = cstr(b, stroff + u32_(b, s) as usize);
            let ty = u32_(b, s + 4);
            let flags = u64_(b, s + 8);
            let addr = u64_(b, s + 16);
            let off = u64_(b, s + 24) as usize;
            let size = u64_(b, s + 32) as usize;
            let link = u32_(b, s + 40) as usize;
            if ty == 2 {
                // SYMTAB
                let str2 = u64_(b, sh(link) + 24) as usize;
                for k in 0..size / 24 {
                    let e = off + k * 24;
                    let info = b[e + 4];
                    let shndx = u16_(b, e + 6);
                    let value = u64_(b, e + 8);
                    let stype = info & 15;
                    if shndx != 0 && (stype == 0 || stype == 2) {
                        symbols.push((cstr(b, str2 + u32_(b, e) as usize), value));
                        sizes.push(u64_(b, e + 16));
                    }
                }
            }
            let data = if ty == 8 {
                vec![]
            } else {
                b[off..off + size].to_vec()
            };
            sections.push(Section {
                name,
                addr,
                data,
                exec: flags & 4 != 0,
            });
        }
    }
    Ok(Elf {
        entry,
        segments,
        sections,
        symbols,
        sizes,
    })
}
