//! ELF64 x86-64 loader (the Rust twin of `examples/wasm-sim/proc/wat/loader.wat`).
//!
//! * maps every `PT_LOAD` (`p_filesz` bytes from the file, the rest zero);
//! * program break = page-aligned end of the highest segment;
//! * `PT_DYNAMIC`: eager binding of `GLOB_DAT`/`JUMP_SLOT`/`64`/`RELATIVE`; undefined symbols
//!   resolve to *foreign* addresses `EXT_BASE + 16 * i` for `FOREIGN[i]`, weak undefined to 0;
//! * initial stack in the LPS layout (`Silmaril.Process.LPS.buildStackBytes`, ten auxv entries).

use super::mem::{Mem, PAGE};
use wasmtime::error::Context;
use wasmtime::{Result, bail};

pub const EXT_BASE: u64 = 0x7f00_0000_0000;
pub const EXT_SIZE: u64 = 0x1000;
/// Names of the foreign library functions (`ext.call` targets), in address order.
pub const FOREIGN: &[&str] = &["puts", "strlen", "putchar"];
pub const STACK_TOP: u64 = 0x7fff_ffff_f000;
pub const STACK_SIZE: u64 = 0x10_0000;
/// The fixed `AT_RANDOM` draw.
pub const AT_RANDOM_BYTES: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

pub struct Elf<'a> {
    pub data: &'a [u8],
}

fn rd(d: &[u8], o: usize, n: usize) -> Result<u64> {
    let s = d.get(o..o + n).context("ELF truncated")?;
    let mut b = [0u8; 8];
    b[..n].copy_from_slice(s);
    Ok(u64::from_le_bytes(b))
}

#[derive(Debug, Clone, Copy)]
pub struct Phdr {
    pub ty: u32,
    pub offset: u64,
    pub vaddr: u64,
    pub filesz: u64,
    pub memsz: u64,
}

impl<'a> Elf<'a> {
    pub fn parse(data: &'a [u8]) -> Result<Self> {
        if data.len() < 64 || &data[..4] != b"\x7fELF" || data[4] != 2 || data[5] != 1 {
            bail!("not an ELF64 little-endian file");
        }
        if rd(data, 18, 2)? != 62 {
            bail!("not x86-64");
        }
        Ok(Elf { data })
    }
    pub fn ty(&self) -> u64 {
        rd(self.data, 16, 2).unwrap()
    }
    pub fn entry(&self) -> u64 {
        rd(self.data, 24, 8).unwrap()
    }
    pub fn phdrs(&self) -> Result<Vec<Phdr>> {
        let (off, n) = (
            rd(self.data, 32, 8)? as usize,
            rd(self.data, 56, 2)? as usize,
        );
        (0..n)
            .map(|i| {
                let p = off + 56 * i;
                Ok(Phdr {
                    ty: rd(self.data, p, 4)? as u32,
                    offset: rd(self.data, p + 8, 8)?,
                    vaddr: rd(self.data, p + 16, 8)?,
                    filesz: rd(self.data, p + 32, 8)?,
                    memsz: rd(self.data, p + 40, 8)?,
                })
            })
            .collect()
    }
    /// Defined symbols of `.symtab` (name, value).
    pub fn symbols(&self) -> Result<Vec<(String, u64)>> {
        let d = self.data;
        let (shoff, shn) = (rd(d, 40, 8)? as usize, rd(d, 60, 2)? as usize);
        let mut out = vec![];
        for i in 0..shn {
            let s = shoff + 64 * i;
            if rd(d, s + 4, 4)? != 2 {
                continue; // SHT_SYMTAB
            }
            let (off, size, link) = (
                rd(d, s + 24, 8)? as usize,
                rd(d, s + 32, 8)? as usize,
                rd(d, s + 40, 4)? as usize,
            );
            let strs = rd(d, shoff + 64 * link + 24, 8)? as usize;
            for k in 0..size / 24 {
                let e = off + 24 * k;
                let (name, shndx, value) =
                    (rd(d, e, 4)? as usize, rd(d, e + 6, 2)?, rd(d, e + 8, 8)?);
                if shndx == 0 || name == 0 {
                    continue;
                }
                let n = &d[strs + name..];
                let n = &n[..n.iter().position(|&b| b == 0).unwrap_or(n.len())];
                out.push((String::from_utf8_lossy(n).into_owned(), value));
            }
        }
        Ok(out)
    }
}

/// The launched process image.
#[derive(Debug, Clone)]
pub struct Image {
    pub entry: u64,
    pub sp: u64,
    pub brk: u64,
    /// The foreign range, if the program has dynamic relocations.
    pub ext: Option<(u64, u64)>,
}

/// What `map_segments` returns: (initial brk, AT_PHDR address or 0, the foreign range if there are dynamic relocations).
pub type Mapped = (u64, u64, Option<(u64, u64)>);

/// Map the segments and apply dynamic relocations (no stack).
pub fn map_segments(mem: &mut Mem, elf: &Elf) -> Result<Mapped> {
    if elf.ty() != 2 {
        bail!("only ET_EXEC is supported");
    }
    let phs = elf.phdrs()?;
    let phoff = rd(elf.data, 32, 8)?;
    let (mut end, mut phdr, mut dyn_) = (0u64, None, None);
    for p in &phs {
        match p.ty {
            6 => phdr = Some(p.vaddr),
            2 => dyn_ = Some(p.vaddr),
            1 => {
                mem.map(p.vaddr, p.memsz);
                let src = elf
                    .data
                    .get(p.offset as usize..(p.offset + p.filesz) as usize)
                    .context("segment")?;
                mem.write_bytes(p.vaddr, src).context("map")?;
                if phdr.is_none() && p.offset <= phoff && phoff < p.offset + p.filesz {
                    phdr = Some(p.vaddr + phoff - p.offset);
                }
                end = end.max(p.vaddr + p.memsz);
            }
            _ => {}
        }
    }
    let mut ext = None;
    if let Some(d) = dyn_ {
        relocate(mem, d)?;
        ext = Some((EXT_BASE, EXT_BASE + EXT_SIZE));
    }
    Ok((end.div_ceil(PAGE) * PAGE, phdr.unwrap_or(0), ext))
}

fn relocate(mem: &mut Mem, mut d: u64) -> Result<()> {
    let ld = |m: &Mem, a: u64| m.load(a, 8).context("dynamic: unmapped");
    let (mut strtab, mut symtab, mut tabs) = (0, 0, [(0u64, 0u64); 2]);
    loop {
        let (tag, val) = (ld(mem, d)?, ld(mem, d + 8)?);
        match tag {
            0 => break,
            5 => strtab = val,
            6 => symtab = val,
            7 => tabs[0].0 = val,
            8 => tabs[0].1 = val,
            23 => tabs[1].0 = val,
            2 => tabs[1].1 = val,
            _ => {}
        }
        d += 16;
    }
    for (rela, size) in tabs {
        for r in (rela..rela + size).step_by(24) {
            let (off, info, add) = (ld(mem, r)?, ld(mem, r + 8)?, ld(mem, r + 16)?);
            let sym = symtab + 24 * (info >> 32);
            let v = match info & 0xffff_ffff {
                8 => add,
                ty @ (1 | 6 | 7) => {
                    let s = if ld(mem, sym + 4)? & 0xffff_0000 != 0 {
                        ld(mem, sym + 8)?
                    } else {
                        let name = mem
                            .read_cstr(strtab + (ld(mem, sym)? & 0xffff_ffff), 256)
                            .context("name")?;
                        match FOREIGN.iter().position(|f| f.as_bytes() == name) {
                            Some(i) => EXT_BASE + 16 * i as u64,
                            None if mem.load8(sym + 4).unwrap() >> 4 == 2 => 0,
                            None => bail!("unresolved symbol {}", String::from_utf8_lossy(&name)),
                        }
                    };
                    if ty == 1 { s.wrapping_add(add) } else { s }
                }
                ty => bail!("unsupported relocation type {ty}"),
            };
            mem.store(off, 8, v).context("relocation target unmapped")?;
        }
    }
    Ok(())
}

/// Load `file` and build the initial stack for `argv`/`envp`.
pub fn load(mem: &mut Mem, file: &[u8], argv: &[Vec<u8>], envp: &[Vec<u8>]) -> Result<Image> {
    let elf = Elf::parse(file)?;
    let (brk, phdr, ext) = map_segments(mem, &elf)?;
    let phnum = rd(file, 56, 2)?;
    mem.map(STACK_TOP - STACK_SIZE, STACK_SIZE);
    // LPS buildStackBytes
    let strs: usize = argv.iter().chain(envp).map(|s| s.len() + 1).sum();
    let structsz = 8 + (argv.len() + 1) * 8 + (envp.len() + 1) * 8 + 160;
    let raw = structsz + strs;
    let total = raw.div_ceil(8) * 8 + 16;
    let sp = (STACK_TOP - PAGE - total as u64) & !15;
    let at_random = sp + total as u64 - 16;
    let mut words = vec![argv.len() as u64];
    let mut a = sp + structsz as u64;
    let mut strings = vec![];
    for list in [argv, envp] {
        for s in list {
            words.push(a);
            strings.extend_from_slice(s);
            strings.push(0);
            a += s.len() as u64 + 1;
        }
        words.push(0);
    }
    let auxv = [
        (3, phdr),
        (4, 56),
        (5, phnum),
        (16, 0),
        (6, PAGE),
        (11, 0),
        (12, 0),
        (23, 0),
        (25, at_random),
        (0, 0),
    ];
    for (k, v) in auxv {
        words.extend([k, v]);
    }
    let mut block: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    block.extend(strings);
    block.resize(total - 16, 0);
    block.extend(AT_RANDOM_BYTES);
    mem.write_bytes(sp, &block).context("stack")?;
    Ok(Image {
        entry: elf.entry(),
        sp,
        brk,
        ext,
    })
}
