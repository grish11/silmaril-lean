import Silmaril.Elf.Staged.Defs
import Silmaril.Elf.Staged.Symbols.Defs
import Silmaril.Elf.Staged.Leaf.Defs
import Silmaril.Elf.Link.Dyn.Pages.Defs

/-!
# `elf-staged`: staged ELF parsing, natively (fast mode) and as kernel certificates

```
elf-staged layout FILE                 the stage-1 layout: sections, segments, spans
elf-staged bench FILE [TILES]          time every stage natively (fastRead and pageRead)
elf-staged emit FILE OUT.lean [opts]   a Lean module that kernel-checks stages (paranoid mode)
```

`TILES` is a file of `offset length` lines (instruction boundaries, file offsets in hex), as
`benchmarks/elf-staged/boundaries.sh` derives from `objdump -d`. The tool checks them as a
tiling (`tilesCover`, `tilesOk`) with the per-tile predicate "`Silmaril.X86.Ext.decode` reads an
instruction of exactly this length", and reports how many tiles the model accepts.

Everything this tool prints is **trusted computation**: the compiled reader on a `ByteArray`
(`fastRead`, proved to answer as the file by `Staged.sub_fast`). The theorems come from the
emitted module, checked by the kernel.
-/

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Elf.Link.DynElf (Rd Chunk pageRead pagesFrom)
open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader NameBytes Rela ObjectSymbol)

namespace ElfStaged

def nameStr (n : NameBytes) : String := String.ofList (n.map fun b => Char.ofNat b.toNat)

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Monotonic time of an action, in microseconds. -/
def timed {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← act
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000)

/-- Time `f x`, evaluated inside the measured interval (`noinline` and `IO.lazyPure` keep the
compiler from floating the computation out of it). -/
@[noinline] def timedOn {α β : Type} (x : β) (f : β → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure fun _ => f x
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000)

def ms (us : Nat) : String :=
  let s := toString (us / 1000) ++ "." ++ (toString (1000 + us % 1000)).drop 1
  s ++ " ms"

/-- The little-endian value of bytes `[lo, hi)` (divide and conquer: linearithmic, where a
byte-by-byte fold is quadratic). -/
partial def leRange (a : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 32 then Id.run do
    let mut v := 0
    let mut j := hi
    while j > lo do
      j := j - 1
      v := v * 256 + (a.get! j).toNat
    return v
  else
    let mid := (lo + hi) / 2
    leRange a lo mid + (leRange a mid hi <<< (8 * (mid - lo)))

/-- Little-endian 4 KiB chunk literals of a byte array (as `include_bytes` stores them). -/
def chunksOf (a : ByteArray) (c : Nat := 4096) : List Nat :=
  (List.range ((a.size + c - 1) / c)).map fun k => leRange a (c * k) (min a.size (c * (k + 1)))

def kindName (k : Nat) : String :=
  match k with
  | 0 => "NULL" | 1 => "PROGBITS" | 2 => "SYMTAB" | 3 => "STRTAB" | 4 => "RELA" | 5 => "HASH"
  | 6 => "DYNAMIC" | 7 => "NOTE" | 8 => "NOBITS" | 9 => "REL" | 11 => "DYNSYM" | 14 => "INIT_ARRAY"
  | 15 => "FINI_ARRAY" | 19 => "RELR" | 0x6ffffff6 => "GNU_HASH" | _ => hex k

def bodySize : Body → Nat
  | .symbols _ es => es.length | .relas es => es.length | .rels es => es.length
  | .relr ws => ws.length | .dynamic es => es.length | .versym vs => vs.length
  | .notes ns => ns.length | .gnuHash g => g.chain.length | .hash t => t.chains.length
  | _ => 0

def printLayout (L : Layout) (len : Nat) : IO Unit := do
  IO.println s!"type {L.header.fileType}  machine {L.header.machine}  entry {hex L.header.entry}  file {len} bytes"
  IO.println s!"bounds ok: {L.boundsOk len}"
  IO.println "segments (PT_LOAD):"
  for ph in L.phdrs do
    if ph.kind == PT_LOAD then
      IO.println s!"  off {hex ph.offset} filesz {hex ph.fileSize} vaddr {hex ph.virtualAddress} flags {ph.flags}"
  IO.println "sections:"
  for s in L.sections do
    let seg := match L.segmentOf s.span with
      | some ph => s!"in LOAD@{hex ph.offset}"
      | none => "-"
    IO.println s!"  {nameStr s.name}: {kindName s.header.kind} span [{hex s.span.off}, +{hex s.span.len}] {seg}"

def readFile (path : String) : IO ByteArray := IO.FS.readBinFile path

/-- Instruction tiles: `offset length` lines, hex offsets. -/
def readTiles (path : String) : IO (List (Nat × Nat)) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    match line.trimAscii.toString.splitOn " " with
    | [o, l] =>
      let o' := (o.drop 2).foldl (fun acc ch => acc * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toLower.toNat - 87)) 0
      out := out.push (o', l.toNat!)
    | _ => pure ()
  return out.toList

def layoutOrFail (r : Silmaril.Elf.Check.Src) : IO Layout :=
  match readLayout.run r with
  | some L => pure L
  | none => throw (IO.userError "not an ELF64 little-endian file the reader accepts")

def bench (path : String) (tiles? : Option String) : IO Unit := do
  let (a, tRead) ← timed (readFile path)
  IO.println s!"file {path}: {a.size} bytes, read in {ms tRead}"
  let src := fastRead a
  let (L?, tL) ← timedOn src fun r => readLayout.run r
  let some L := L? | throw (IO.userError "not an ELF64 file the reader accepts")
  IO.println s!"[fast] stage 1 layout ({L.phdrs.length} phdrs, {L.sections.length} sections): {ms tL}"
  IO.println s!"[fast] bounds ok: {L.boundsOk a.size}"
  let mut tBodies := 0
  let mut bodies : Array Body := #[]
  for s in L.sections do
    let (b?, t) ← timedOn src fun r => (Parse.body L.shs s.header).run r
    let some b := b? | throw (IO.userError s!"body of {nameStr s.name} failed")
    -- force the result before stopping the clock
    let n := bodySize b
    tBodies := tBodies + t
    bodies := bodies.push b
    if t > 1000 || n > 0 then
      IO.println s!"[fast] stage 2 body {nameStr s.name} ({n} entries): {ms t}"
  IO.println s!"[fast] stage 2 all bodies: {ms tBodies}"
  let (ld?, tLd) ← timedOn src fun r => (readLoader L.phdrs).run r
  let some ld := ld? | throw (IO.userError "loader view failed")
  IO.println s!"[fast] stage 2' loader view ({ld.dynamic.length} dynamic entries, interp {ld.interp.isSome}): {ms tLd}"
  let (A?, tA) ← timedOn src fun r => Silmaril.Elf.read.run r
  let some A := A? | throw (IO.userError "whole-file parse failed")
  IO.println s!"[fast] whole-file spec `read` ({A.sections.length} sections): {ms tA}"
  IO.println s!"[fast] stages assemble to the whole parse: {decide (L.assemble bodies.toList ld = A)}"
  let (ok, tC) ← timedOn src fun r => Silmaril.Elf.Check.file r A
  IO.println s!"[fast] existing checker Check.file on the parse: {ok} in {ms tC}"
  -- RELA windows
  for s in L.sections do
    if s.header.kind == SHT_RELA then
      if let .relas es := (Parse.body L.shs s.header).run src |>.getD .null then
        let w := 1024
        let (okw, tw) ← timedOn src fun src => (Id.run do
          let mut ok := true
          let mut i := 0
          while i < es.length do
            ok := ok && entriesOk src Parse.rela s.header.offset 24 i ((es.drop i).take w)
            i := i + w
          return ok)
        IO.println s!"[fast] stage 3 {nameStr s.name}: {(es.length + w - 1) / w} windows of {w} entries, ok {okw}: {ms tw}"
  -- the kernel's source, natively
  let (cs, tCs) ← timedOn a fun a => chunksOf a
  let pg := pagesFrom 4096 0 a.size cs
  IO.println s!"[pages] {cs.length} chunk literals built natively in {ms tCs}"
  let (Lp?, tLp) ← timedOn pg fun pg => readLayout.run (pageRead 4096 pg)
  IO.println s!"[pages] stage 1 layout on pageRead (native): {ms tLp}, agrees {decide (Lp? = some L)}"
  -- disassembly tiles
  if let some tp := tiles? then
    let ts ← readTiles tp
    let text := L.section? ".text"
    IO.println s!"[tiles] {ts.length} instruction tiles from {tp}"
    -- contiguous runs: tilesOk walks consecutive tiles from one start offset
    let lens := ts.map (·.2)
    let start := (ts.head?.map (·.1)).getD 0
    let contiguous := (ts.zip (ts.drop 1)).all fun (x, y) => x.1 + x.2 == y.1
    IO.println s!"[tiles] contiguous {contiguous}; covers .text {match text with
      | some s => tilesCover ⟨start, s.span.len⟩ lens && start == s.span.off
      | none => false}"
    let (n, tT) ← timedOn src fun src => ts.foldl (fun acc (o, l) =>
      match src o l with
      | some v => if x86Ok l v then acc + 1 else acc
      | none => acc) 0
    IO.println s!"[tiles] Silmaril.X86.Ext.decode accepts {n} / {ts.length} tiles ({n * 1000 / max 1 ts.length / 10}.{n * 1000 / max 1 ts.length % 10}%) in {ms tT}"
    let (okAll, tW) ← timedOn src fun src => tilesOk src (fun _ _ => true) start lens
    IO.println s!"[tiles] tilesOk (bounds only) over all tiles: {okAll} in {ms tW}"

/-! ## Emitting a paranoid-mode module -/

def litName (n : NameBytes) : String :=
  let v := (n.reverse.foldl (fun acc b => acc * 256 + b.toNat) 0)
  s!"(Silmaril.Elf.Lit.name {n.length} {v})"

def litHeader (h : Header) : String :=
  s!"⟨{h.osABI}, {h.abiVersion}, {h.fileType}, {h.machine}, {h.version}, {h.entry}, {h.programOffset}, {h.sectionOffset}, {h.flags}, {h.headerSize}, {h.programEntrySize}, {h.programCount}, {h.sectionEntrySize}, {h.sectionCount}, {h.sectionNameIndex}⟩"

def litPh (p : ProgramHeader) : String :=
  s!"⟨{p.kind}, {p.flags}, {p.offset}, {p.virtualAddress}, {p.physicalAddress}, {p.fileSize}, {p.memorySize}, {p.alignment}⟩"

def litSh (s : SectionHeader) : String :=
  s!"⟨{s.name}, {s.kind}, {s.flags}, {s.address}, {s.offset}, {s.size}, {s.link}, {s.info}, {s.alignment}, {s.entrySize}⟩"

def litLayout (L : Layout) : String :=
  let phs := ",\n    ".intercalate (L.phdrs.map litPh)
  let secs := ",\n    ".intercalate (L.sections.map fun s => s!"⟨{litSh s.header}, {litName s.name}⟩")
  s!"⟨{litHeader L.header},\n  [{phs}],\n  [{secs}]⟩"

def litRela (r : Rela) : String :=
  let a := match r.addend with
    | .ofNat n => s!"Int.ofNat {n}"
    | .negSucc n => s!"Int.negSucc {n}"
  s!"⟨{r.offset}, {r.info}, {a}⟩"

def litDyn (d : Dyn) : String := s!"⟨{d.tag}, {d.val}⟩"

def litOptName : Option NameBytes → String
  | none => "none"
  | some n => s!"(some {litName n})"

def litLoader (ld : Loader) : String :=
  s!"⟨[{", ".intercalate (ld.dynamic.map litDyn)}], {litOptName ld.interp}, [{", ".intercalate (ld.needed.map litName)}], {litOptName ld.soname}, {litOptName ld.runpath}⟩"

structure EmitOpts where
  relaWindows : Nat := 1
  relaWindow : Nat := 256
  tiles : Option String := none
  tileCount : Nat := 64
  /-- Also emit the monolithic baseline: the whole parse, one `decide +kernel`. -/
  whole : Bool := false
  /-- Also emit every section body and the assembled parse (small files). -/
  bodies : Bool := false
  /-- Use this existing `include_bytes` constant instead of including the file. -/
  bytesConst : Option String := none
  imports : List String := []
  ns : String := "ElfStagedBench"
  /-- First tile: the entry point by default. -/
  tileFrom : Option Nat := none

def emit (path out : String) (o : EmitOpts) : IO Unit := do
  let a ← readFile path
  let src := fastRead a
  let L ← layoutOrFail src
  let some ld := (readLoader L.phdrs).run src | throw (IO.userError "loader view failed")
  let absPath ← IO.FS.realPath path
  let cname := o.bytesConst.getD "bytes"
  let bytesDef := if o.bytesConst.isSome then "" else
    s!"noncomputable def bytes : Silmaril.Formats.Bytes := ⟨include_bytes \"{absPath}\"⟩\n\n"
  let mut s := s!"import Silmaril.Elf.Staged.Leaf.Thms
import Silmaril.Elf.Shapes.Thms
import Silmaril.Elf.Link.Dyn.Pages.Defs
{o.imports.foldl (fun acc m => acc ++ s!"import {m}\n") ""}
/-! Generated by `elf-staged emit` from {path} ({a.size} bytes). Paranoid mode: every theorem
below is checked by the kernel (`decide +kernel` on 4 KiB page literals); no compiled evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace {o.ns}

open Silmaril.Elf Silmaril.Elf.Staged
open Silmaril.Elf.Link.DynElf (pageRead pagesFrom ChunksOf)

{bytesDef}/-- The file. -/
noncomputable abbrev F : Silmaril.X86.Link.Blob := blobOf {cname}

/-- Its 4 KiB pages (the kernel's byte source). -/
noncomputable def pg := pagesFrom 4096 0 {a.size} (chunks_of% {cname})

theorem hc : ChunksOf F pg := Rows.pages_of_bytes rfl

/-- The stage-1 layout (emitted by the fast mode; checked below). -/
def L : Layout :=
{litLayout L}

/-- **Stage 1**, kernel-checked. -/
theorem layout : LayoutIs F L := Leaf.layout.of_kernel hc (c := L) (by decide +kernel)

/-- Every span of the layout lies in the file. -/
theorem bounds : L.boundsOk {a.size} = true := by decide +kernel

"
  s := s ++ s!"/-- **Stage 2'**: the loader view (`PT_DYNAMIC`, `PT_INTERP`, `DT_NEEDED`, …). -/
theorem loader : LoaderIs F L {litLoader ld} :=
  Leaf.loader.of_kernel hc (c := (L, {litLoader ld})) (by decide +kernel)

"
  let mut idx := 0
  for sec in L.sections do
    if sec.header.kind == SHT_RELA then
      if let .relas es := ((Parse.body L.shs sec.header).run src).getD .null then
        for k in List.range o.relaWindows do
          let i := k * o.relaWindow
          let win := (es.drop i).take o.relaWindow
          if !win.isEmpty then
            s := s ++ s!"/-- Window {k} of section {idx} (`{nameStr sec.name}`): entries {i}…{i + win.length - 1}. -/
def relaW_{idx}_{k} : List Silmaril.Formats.ELF.Rela :=
  [{", ".intercalate (win.map litRela)}]
/-- **Stage 3** (`elf.rela`): window {k} of section {idx}, kernel-checked. -/
theorem rela_{idx}_{k} : EntriesAt F Parse.rela {sec.header.offset} 24 {i} relaW_{idx}_{k} :=
  Leaf.rela.of_kernel hc (c := ({sec.header.offset}, {i}, relaW_{idx}_{k})) (by decide +kernel)

"
    idx := idx + 1
  if let some tp := o.tiles then
    let from_ := o.tileFrom.getD ((L.offsetOf L.header.entry).getD 0)
    let ts := ((← readTiles tp).dropWhile (·.1 < from_)).take o.tileCount
    if let some (start, _) := ts.head? then
      let lens := ts.map (·.2)
      let pre := ts.takeWhile fun (o, l) => match src o l with | some v => x86Ok l v | none => false
      s := s ++ s!"/-- **Disassembly tiles**: {ts.length} consecutive instruction boundaries from {hex start} lie in the
file (bounds only). -/
theorem tiles : TilesAt F (fun _ _ => true) {start} {lens} :=
  Leaf.tiles.of_kernel hc (c := ({start}, {lens})) (by decide +kernel)

"
      if !pre.isEmpty then
        s := s ++ s!"/-- **Decoded tiles**: the first {pre.length} of them are each one instruction of the local
x86 model (`Silmaril.X86.Ext.decode` reads exactly the tile). -/
theorem tiles_x86 : TilesAt F x86Ok {start} {pre.map (·.2)} :=
  Leaf.tilesX86.of_kernel hc (c := ({start}, {pre.map (·.2)})) (by decide +kernel)

"
  if o.whole then
    let some A := Silmaril.Elf.read.run src | throw (IO.userError "whole-file parse failed")
    s := s ++ s!"/-- The whole parse (emitted by the fast mode). -/
def A : File := {(reprStr A).replace "\n" " "}

/-- **Baseline**: the whole parse in one kernel run of the specification on the pages. -/
theorem whole : Parses F A := Rows.parses_of_pages (c := 4096) hc (by decide +kernel)

"
  if o.bodies then
    let mut names : Array String := #[]
    let mut bs : Array String := #[]
    for (sec, k) in L.sections.zipIdx do
      let some b := (Parse.body L.shs sec.header).run src | throw (IO.userError "body failed")
      names := names.push s!"body_{k}"
      bs := bs.push s!"b{k}"
      s := s ++ s!"/-- The body of section {k} (`{nameStr sec.name}`), emitted by the fast mode. -/
def b{k} : Body :=
  {(reprStr b).replace "\n" " "}

/-- **Stage 2**: the body of section {k}, kernel-checked. -/
theorem body_{k} : BodyIs F L {litSh sec.header} b{k} := bodyIs_of_pages hc (by decide +kernel)

"
    let forall2 := names.foldr (fun n acc => s!"(.cons {n} {acc})") ".nil"
    s := s ++ s!"/-- The loader view, emitted by the fast mode. -/
def ld : Loader := {litLoader ld}

/-- **The stages assemble to the whole parse** (`parses_assemble`; no further kernel run). -/
theorem parses : Parses F (L.assemble [{", ".intercalate bs.toList}] ld) :=
  parses_assemble layout
    {forall2}
    loader

"
  s := s ++ s!"end {o.ns}\n"
  IO.FS.writeFile out s
  IO.println s!"wrote {out}"


/-! ## Emitting an example: an object module and a leaf module -/

def litSym (s : Silmaril.Formats.ELF.ObjectSymbol) : String := s!"{litName s.name}"

/-- `emit-example`: the shared objects (layout, loader view, bodies, symbol indexes, the tiles
of one function) as small named definitions in `defsOut`, and the leaf theorems that check them
against the bytes in `thmsOut` (which imports `defsOut`'s module and the bytes). -/
def emitExample (path defsMod defsOut thmsOut : String) (o : EmitOpts) (fn : Option String) :
    IO Unit := do
  let a ← readFile path
  let src := fastRead a
  let L ← layoutOrFail src
  let some ld := (readLoader L.phdrs).run src | throw (IO.userError "loader view failed")
  let some cname := o.bytesConst | throw (IO.userError "emit-example needs --bytes-const")
  let ns := o.ns
  let hdr := s!"(generated by `elf-staged emit-example` from {path}, {a.size} bytes)"
  -- objects
  let mut d := s!"module

public import Silmaril.Elf.Staged.Symbols.Defs
import Silmaril.Elf.Staged.Leaf.Defs

/-! # Shared objects for the staged checks of `{path}`

Untrusted data {hdr}: each definition is a small certificate a leaf in
`{defsMod.replace ".Defs" ".Thms"}` checks against the file's bytes. Nothing here is believed
until a leaf checks it. -/

set_option maxRecDepth 100000

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged

/-- The stage-1 layout. -/
def L : Layout :=
{litLayout L}

/-- The loader view. -/
def ld : Loader := {litLoader ld}

"
  let mut t := s!"module

public import {defsMod}
public import Silmaril.Elf.Staged.Leaf.Thms
public import Silmaril.Elf.Shapes.Thms
{o.imports.foldl (fun acc m => acc ++ s!"public import {m}\n") ""}
/-! # Staged checks of `{path}`

Every theorem is one leaf (`Silmaril.Elf.Staged.Leaf`) run in the kernel on the 4 KiB pages
of the file (`Leaf.of_kernel`, `decide +kernel`) {hdr}. Under an acceleration
policy the same leaves run natively (`Leaf.of_native`) and conclude the same propositions. -/

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged
open Silmaril.Elf.Link.DynElf (pagesFrom ChunksOf)

/-- The file. -/
noncomputable abbrev F : Silmaril.X86.Link.Blob := blobOf {cname}

/-- Its 4 KiB pages. -/
noncomputable def pg := pagesFrom 4096 0 {a.size} (chunks_of% {cname})

theorem hc : ChunksOf F pg := Rows.pages_of_bytes rfl

/-- **Stage 1** (`elf.layout`). -/
theorem layout : LayoutIs F L := Leaf.layout.of_kernel hc (c := L) (by decide +kernel)

/-- **Stage 2'** (`elf.loader`). -/
theorem loader : LoaderIs F L ld := Leaf.loader.of_kernel hc (c := (L, ld)) (by decide +kernel)

"
  let mut names : Array String := #[]
  let mut bs : Array String := #[]
  for (sec, k) in L.sections.zipIdx do
    let some b := (Parse.body L.shs sec.header).run src | throw (IO.userError "body failed")
    names := names.push s!"body_{k}"
    bs := bs.push s!"b{k}"
    d := d ++ s!"/-- The body of section {k} (`{nameStr sec.name}`). -/
def b{k} : Body :=
  {(reprStr b).replace "\n" " "}

"
    t := t ++ s!"theorem body_{k} : BodyIs F L {litSh sec.header} b{k} :=
  Leaf.body.of_kernel hc (c := (L, {litSh sec.header}, b{k})) (by decide +kernel)

"
  let forall2 := names.foldr (fun n acc => s!"(.cons {n} {acc})") ".nil"
  d := d ++ s!"/-- The section bodies, in order. -/
def bodies : List Body := [{", ".intercalate bs.toList}]

"
  t := t ++ s!"/-- **The stages assemble to the whole parse** (`parses_assemble`; no further kernel run). -/
theorem parses : Parses F (L.assemble bodies ld) :=
  parses_assemble layout
    {forall2}
    loader

"
  -- symbol indexes over .symtab
  let symtab? := L.sections.find? (·.header.kind == SHT_SYMTAB)
  if let some st := symtab? then
    let some strs := L.shs[st.header.link]? | throw (IO.userError "symtab link")
    let tab : Symbols.Tab := ⟨strs, st.header⟩
    let syms := (List.range tab.count).filterMap fun i => ((tab.entry i).run src).map (i, ·)
    -- forward: first entry of each nonempty name, sorted by name
    let named := syms.filter (·.2.name ≠ [])
    let sorted := named.toArray.qsort (fun x y => Symbols.nameCmp x.2.name y.2.name == .lt) |>.toList
    let fwd := sorted.foldl (fun (acc : List (Nat × Silmaril.Formats.ELF.ObjectSymbol)) e =>
      match acc.head? with
      | some h => if Symbols.nameCmp h.2.name e.2.name == .eq then acc else e :: acc
      | none => [e]) [] |>.reverse
    let rev := (syms.filter (0 < ·.2.raw.size)).toArray.qsort (fun x y => x.2.raw.value < y.2.raw.value) |>.toList
    d := d ++ s!"/-- The symbol table `{nameStr st.name}` and its string table. -/
def symtab : Symbols.Tab := ⟨{litSh strs}, {litSh st.header}⟩

/-- **Forward index**: each named symbol's first entry, sorted by name. -/
def byName : Symbols.ByName := ⟨symtab, #[{", ".intercalate (fwd.map fun (i, s) => s!"({litSym s}, {i})")}]⟩

/-- **Reverse map**: `(value, size, entry)` of the symbols with a size, sorted by value. -/
def byAddr : Symbols.ByAddr := ⟨symtab, #[{", ".intercalate (rev.map fun (i, s) => s!"({s.raw.value}, {s.raw.size}, {i})")}]⟩

"
    t := t ++ s!"/-- `elf.symbols.byName`. -/
theorem byName_ok : byName.sorted = true ∧ byName.Sound F :=
  Leaf.byName.of_kernel hc (c := byName) (by decide +kernel)

/-- `elf.symbols.byAddr`. -/
theorem byAddr_ok : byAddr.sorted = true ∧ byAddr.Sound F :=
  Leaf.byAddr.of_kernel hc (c := byAddr) (by decide +kernel)

"
    -- one function, grounded in the file
    if let (some f, some tp) := (fn, o.tiles) then
      let some (i, s) := fwd.find? (fun e => e.2.name == nameOf f) | throw (IO.userError s!"no symbol {f}")
      let v := s.raw.value
      let some off := L.offsetOf v | throw (IO.userError "function not in a PT_LOAD")
      let ts := ((← readTiles tp).dropWhile (·.1 < off)).takeWhile (·.1 < off + s.raw.size)
      let lens := ts.map (·.2)
      d := d ++ s!"/-- The instruction boundaries of `{f}`, from a disassembler. -/
def {f}Tiles : List Nat := {lens}

"
      t := t ++ s!"/-- **`{f}` by name**: the forward index names entry {i}, and it is `{f}`. -/
theorem {f}_entry : ∃ s, Symbols.SymAt F symtab {i} s ∧ s.name = nameOf \"{f}\" :=
  Symbols.ByName.find_sound byName_ok.2 (n := nameOf \"{f}\") (by decide)

/-- **Its extent**: the reverse map sends its first address back to entry {i}. -/
theorem {f}_extent : ∃ s, Symbols.SymAt F symtab {i} s ∧ s.raw.value ≤ {v} ∧ {v} < s.raw.value + s.raw.size :=
  Symbols.ByAddr.find_sound byAddr_ok.2 (by decide)

/-- **Its code**: address {hex v} is file offset {hex off}, the tiles cover its {s.raw.size} bytes, and
each tile is one instruction of the local x86 model (`elf.tiles.x86`). -/
theorem {f}_code : L.offsetOf {v} = some {off} ∧ tilesCover ⟨{off}, {s.raw.size}⟩ {f}Tiles = true ∧
    TilesAt F x86Ok {off} {f}Tiles :=
  ⟨by decide, by decide, Leaf.tilesX86.of_kernel hc (c := ({off}, {f}Tiles)) (by decide +kernel)⟩

"
  d := d ++ s!"end {ns}\n"
  t := t ++ s!"end {ns}\n"
  IO.FS.writeFile defsOut d
  IO.FS.writeFile thmsOut t
  IO.println s!"wrote {defsOut} and {thmsOut}"


/-! ## Emitting the per-part reader modules (`emit-reader`) -/

/-- Read footprints merged into sorted spans (overlapping or adjacent reads join; a zero-width
read keeps a zero-length span so that the windowed run still answers it). -/
def mergeSpans (rs : List (Nat × Nat)) : List Span :=
  let xs := rs.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) |>.toList
  let out := xs.foldl (fun (acc : List (Nat × Nat)) (o, w) =>
    match acc with
    | (o', e) :: rest => if o ≤ e then (o', max e (o + w)) :: rest else (o, o + w) :: acc
    | [] => [(o, o + w)]) []
  out.reverse.map fun (o, e) => ⟨o, e - o⟩

def litSpans (ws : List Span) : String :=
  "[" ++ ", ".intercalate (ws.map fun s => s!"⟨{s.off}, {s.len}⟩") ++ "]"

/-- The windows of a reader: its exact footprint on the file. -/
def footprint {α : Type} (src : Silmaril.Elf.Check.Src) (p : Rd α) : List Span :=
  mergeSpans (Parse.trace src p)

/-- The byte ranges in `[0, len)` that no section occupies and no part's reader reads (`read`: the
footprint of the layout, so header bytes the reader skips, such as `e_ident`'s padding, are gaps). -/
def gaps (L : Layout) (len : Nat) (read : List Span) : List Span :=
  let used : List (Nat × Nat) :=
    read.map (fun s => (s.off, s.len)) ++ L.sections.map fun s => (s.span.off, s.span.len)
  let spans := mergeSpans (used.filter (0 < ·.2))
  let (acc, pos) := spans.foldl (fun (acc, pos) s =>
    (if pos < s.off then acc ++ [(⟨pos, s.off - pos⟩ : Span)] else acc, max pos (s.off + s.len)))
    (([] : List Span), 0)
  if pos < len then acc ++ [⟨pos, len - pos⟩] else acc

def allZero (a : ByteArray) (s : Span) : Bool :=
  (List.range s.len).all fun i => a.get! (s.off + i) == 0

/-! ## Function decompositions (`Decomp.lean`) -/

/-- Consecutive chunks of at most `n` elements. -/
def listChunks {α : Type} (n : Nat) (xs : List α) : List (List α) :=
  if h : xs = [] ∨ n = 0 then (if xs = [] then [] else [xs]) else
    have : (xs.drop n).length < xs.length := by
      cases xs with
      | nil => simp at h
      | cons x xs => simp only [List.length_drop, List.length_cons]; omega
    xs.take n :: listChunks n (xs.drop n)
termination_by xs.length

/-- A candidate function piece: symbol-table section, entry index, symbol. -/
structure Cand where
  k : Nat
  i : Nat
  s : ObjectSymbol

/-- Preference among symbols with the same extent: `STB_GLOBAL`, then `STB_WEAK`, then local; then
the lower entry index. -/
def Cand.rank (c : Cand) : Nat × Nat :=
  (match c.s.binding with | 1 => 0 | 2 => 1 | _ => 2, c.i)

/-- What the decomposition of one section is, and what it leaves out. -/
structure SecDecomp where
  x : Nat
  name : String
  sh : SectionHeader
  pieces : Array (Option Cand × Nat)   -- `(some c, size)` a function, `(none, n)` a gap
  aliases : Nat
  overlaps : Array Cand
  zeroSize : Nat

/-- Decompose section `x` along the function symbols of one symbol table `(k, es)`. -/
def decompSection (x : Nat) (sec : Sec) (k : Nat) (es : List ObjectSymbol) : SecDecomp := Id.run do
  let sh := sec.header
  let lo := sh.address
  let hi := sh.address + sh.size
  let fnKind (s : ObjectSymbol) : Bool := s.kind == 2 || s.kind == 10
  let mine := (es.zipIdx.filter fun (s, _) => fnKind s && s.raw.sectionIndex == x).map fun (s, i) => Cand.mk k i s
  let zeroSize := (mine.filter (·.s.raw.size == 0)).length
  let cs := (mine.filter (0 < ·.s.raw.size)).toArray.qsort fun a b =>
    a.s.raw.value < b.s.raw.value ||
      (a.s.raw.value == b.s.raw.value && (a.s.raw.size > b.s.raw.size ||
        (a.s.raw.size == b.s.raw.size && (a.rank.1 < b.rank.1 || (a.rank.1 == b.rank.1 && a.rank.2 < b.rank.2)))))
  let mut out : Array (Option Cand × Nat) := #[]
  let mut cur := lo
  let mut aliases := 0
  let mut overlaps : Array Cand := #[]
  let mut last : Option (Nat × Nat) := none
  for c in cs do
    let v := c.s.raw.value
    let z := c.s.raw.size
    if last == some (v, z) then aliases := aliases + 1
    else if cur ≤ v && v + z ≤ hi then
      if cur < v then out := out.push (none, v - cur)
      out := out.push (some c, z)
      cur := v + z
      last := some (v, z)
    else overlaps := overlaps.push c
  if cur < hi then out := out.push (none, hi - cur)
  pure { x, name := nameStr sec.name, sh, pieces := out, aliases, overlaps, zeroSize }

/-- The `Decomp.lean` module of a file: one `Decomposes` theorem per executable `SHT_PROGBITS`
section with at least one function symbol, along `.symtab` when the file has one and `.dynsym`
otherwise; and a report of what each leaves out. -/
def emitDecomp (ns title gen : String) (L : Layout) (bodies : Array Body) : String × String := Id.run do
  let tabs : List (Nat × Table × List ObjectSymbol) := (bodies.toList.zipIdx).filterMap fun
    | (.symbols t es, k) => some (k, t, es)
    | _ => none
  let tab? := (tabs.find? fun (_, t, _) => t == .symtab).orElse fun _ => tabs.head?
  let tabName := match tab? with | some (_, .symtab, _) => ".symtab" | some _ => ".dynsym" | none => "(none)"
  let execs := L.sections.zipIdx.filter fun (s, _) =>
    s.header.kind == SHT_PROGBITS && s.header.flags / SHF_EXECINSTR % 2 == 1
  let ds : List SecDecomp := match tab? with
    | none => []
    | some (k, _, es) => (execs.map fun (s, x) => decompSection x s k es).filter fun d =>
        d.pieces.any (·.1.isSome)
  let undec := execs.filter fun (_, x) => !(ds.any (·.x == x))
  let mut rep := s!"decomposition along {tabName}:"
  let mut tbl := "| section | bytes | functions | covered | gaps (bytes) | aliases | left out: overlapping | zero-size symbols |\n|---|---|---|---|---|---|---|---|\n"
  for d in ds do
    let nf := (d.pieces.filter (·.1.isSome)).size
    let cov := (d.pieces.filter (·.1.isSome)).foldl (· + ·.2) 0
    let gaps := d.pieces.filter (·.1.isNone)
    let gb := gaps.foldl (· + ·.2) 0
    let pct := if d.sh.size == 0 then 100 else cov * 1000 / d.sh.size
    tbl := tbl ++ s!"| `{d.name}` ({d.x}) | {d.sh.size} | {nf} | {cov} ({pct / 10}.{pct % 10}%) | {gaps.size} ({gb}) | {d.aliases} | {d.overlaps.size} | {d.zeroSize} |\n"
    rep := rep ++ s!" {d.name}: {nf} functions, {cov}/{d.sh.size} bytes, {gaps.size} gaps, {d.aliases} aliases, {d.overlaps.size} overlapping, {d.zeroSize} zero-size;"
  let undecS := if undec.isEmpty then "none" else ", ".intercalate (undec.map fun (s, x) => s!"`{nameStr s.name}` ({x})")
  let mut t := s!"module

public import {ns}.Functions
public import Silmaril.Elf.Staged.Decomp.Thms

/-! # {title}: its executable sections, decomposed into functions

{gen}

`Silmaril.Elf.Staged.Decomp.Decomposes F L x pieces_x`: section `x` is an executable
`SHT_PROGBITS` section, and `pieces_x` (functions of the symbol table, by entry, and explicit gaps)
tiles its address range exactly; every function piece is a defined `STT_FUNC`/`STT_GNU_IFUNC`
symbol of the section with nonzero size, read from the file by the checked symbol theorem of
`{ns}.Functions`. Closed by one `decide +kernel` run of the tiling check per section; no native
evaluation. Along {tabName}.

{tbl}
A **gap** is a byte range that no chosen function symbol covers: alignment padding, code with no
symbol (a stripped file has only exported symbols), or the extent of a symbol left out because it
overlaps a chosen one (an **alias** has the same extent as a chosen symbol and is not listed
again). Nothing here says that a function's bytes are instructions, or anything about what the
function does. Executable sections not decomposed (no function symbol): {undecS}. -/

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Decomp

"
  match tab? with
  | none => pure ()
  | some (k, _, _) =>
    let link := match L.shs[k]? with | some sh => sh.link | none => 0
    t := t ++ s!"theorem decomp_tab : L.shs[{k}]? = some sh{k} := rfl

theorem decomp_strs : L.shs[sh{k}.link]? = some sh{link} := rfl

"
  for d in ds do
    let chunks := (listChunks 128 d.pieces.toList).zipIdx
    for (ch, j) in chunks do
      let lits := ch.map fun
        | (some c, _) => s!".fn {c.k} {c.i} s{c.k}_{c.i}"
        | (none, n) => s!".gap {n}"
      t := t ++ s!"/-- Pieces {j * 128} to {j * 128 + ch.length - 1} of section {d.x} (`{d.name}`). -/
def pieces_{d.x}_{j} : List Piece :=
  [{",\n   ".intercalate lits}]

"
      let rd := ch.foldr (fun p acc => match p with
        | (some c, _) => s!"read_cons (symbolIs_of_partIs' decomp_tab (by decide) decomp_strs (by decide) (by decide) sym_{c.k}_{c.i})\n  ({acc})"
        | (none, _) => s!"read_cons trivial ({acc})") "read_nil"
      t := t ++ s!"theorem read_{d.x}_{j} : ∀ p ∈ pieces_{d.x}_{j}, p.Read F L :=\n  {rd}\n\n"
    let n := chunks.length
    let names := (List.range n).map (s!"pieces_{d.x}_{·}")
    -- `++` associates to the left; the reads below are nested to the right, so is the list
    let all := names.foldr (fun nm acc => if acc == "" then nm else s!"{nm} ++ ({acc})") ""
    let all := if n == 0 then "[]" else all
    let rdAll := (List.range n).foldr (fun j acc => if j + 1 == n then s!"read_{d.x}_{j}" else s!"(read_append read_{d.x}_{j} {acc})") "read_nil"
    let rdAll := if n == 0 then "read_nil" else rdAll
    t := t ++ s!"/-- The pieces of section {d.x} (`{d.name}`), in address order. -/
def pieces_{d.x} : List Piece := {all}

/-- **Section {d.x} (`{d.name}`) decomposes into the functions and gaps `pieces_{d.x}`.** -/
theorem decomp_{d.x} : Decomposes F L {d.x} pieces_{d.x} :=
  decomposes_of (sh := sh{d.x}) layout rfl ⟨by decide, by decide⟩ (by decide +kernel)
    {rdAll}

"
  t := t ++ s!"end {ns}\n"
  pure (t, rep)

/-- `emit-reader FILE NAME SHA256 DIR`: the modules `Silmaril.Elf.Staged.Pinned.NAME.{Bytes,Defs,Thms}`
(module docs there). -/
def emitReader (path name sha title dir : String) (nsOpt relOpt genOpt : Option String := none)
    (maxEntries : Option Nat := none) : IO Unit := do
  let a ← readFile path
  let src := fastRead a
  let L ← layoutOrFail src
  let some ld := (readLoader L.phdrs).run src | throw (IO.userError "loader view failed")
  let some A := Silmaril.Elf.read.run src | throw (IO.userError "the specification rejects the file")
  let ns := nsOpt.getD s!"Silmaril.Elf.Staged.Pinned.{name}"
  let rel := relOpt.getD ("../../../../../" ++ path)
  let gen := s!"GENERATED by `elf-staged emit-reader {path} {name} …` (`{genOpt.getD "scripts/elf-reader/gen.sh"}`); do not edit."
  let bytesMod := s!"module

public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Elf.Parse.Defs

/-! # {title}: the raw file and its kernel bytes

{gen}

`raw` is `{path}` ({a.size} bytes, SHA-256 `{sha}`) as `include_bytes`; `K` is the same file as
kernel bytes, with `K.toByteArray_eq : K.toByteArray = raw` (`kbytes_def … of_include`, checked
by the kernel without decoding a byte). `F` is the file the ELF specification reads. -/

@[expose] public section

namespace {ns}

/-- The file, as `include_bytes`. -/
noncomputable def raw : ByteArray := include_bytes \"{rel}\"

kbytes_def K of_include raw

/-- The file the specification reads. -/
noncomputable abbrev F : Silmaril.X86.Link.Blob := Silmaril.Elf.blobOf ⟨raw⟩

end {ns}
"
  let h := L.header
  let mut d := s!"module

public import Silmaril.Elf.Staged.Defs

/-! # {title}: the claimed parts

{gen}

Untrusted data: the parts of `{path}` as the compiled specification reads them. Nothing here
is believed until a theorem of `{ns}.Thms` checks it against the file's bytes. -/

set_option maxRecDepth 100000

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged
open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader NameBytes ObjectSymbol)

/-- The pinned file's path, from the repository root (`raw` in `{ns}.Bytes` includes it). -/
def path : String := \"{path}\"

/-- Its SHA-256 (`examples/elf/pin.sh --check`). -/
def sha256 : String := \"{sha}\"

/-- Its size in bytes. -/
def size : Nat := {a.size}

/-- The ELF header. -/
def hdr : Header := {litHeader h}

"
  let mut t := s!"module

public import {ns}.Bytes
public import {ns}.Defs
public import Silmaril.Elf.Staged.Reader.Thms

/-! # {title}: every part, checked against the file's bytes

{gen}

Each theorem is `PartIs F ws p v` (the specification's reader `p`, run on the bytes of the
pinned file **inside the windows `ws` only**, returns `v`) or `ZerosAt F o n` (padding), closed by
one `decide +kernel` run on the kernel bytes `K` (`Reader.partIs_of_kbytes`). The windows are the
exact footprint of the reader. `layout` and `parses` assemble the parts into the parse of the
whole file (`Silmaril.Elf.Parses`) with no further kernel run of the reader. -/

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader

/-- **The ELF header** (`e_ident`, type, machine, entry, table offsets and sizes). -/
theorem header : PartIs F {litSpans (footprint src Parse.header)} Parse.header hdr :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
  for (ph, i) in L.phdrs.zipIdx do
    let o := h.programOffset + 56 * i
    d := d ++ s!"/-- Program header {i}. -/\ndef ph{i} : ProgramHeader := {litPh ph}\n\n"
    t := t ++ s!"/-- **Program header {i}.** -/
theorem phdr_{i} : PartIs F {litSpans (footprint src (Parse.phdr o))} (Parse.phdr {o}) ph{i} :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
  let shs := L.shs
  let names? := shs[h.sectionNameIndex]?
  for (sec, i) in L.sections.zipIdx do
    let o := h.sectionOffset + 64 * i
    let nm := nameStr sec.name
    d := d ++ s!"/-- Section header {i} (`{nm}`). -/\ndef sh{i} : SectionHeader := {litSh sec.header}\n\n/-- The name of section {i}. -/\ndef n{i} : NameBytes := {litName sec.name}\n\n"
    t := t ++ s!"/-- **Section header {i}** (`{nm}`). -/
theorem shdr_{i} : PartIs F {litSpans (footprint src (Parse.shdr o))} (Parse.shdr {o}) sh{i} :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
    if let some names := names? then
      t := t ++ s!"/-- **The name of section {i}**: `{nm}`. -/
theorem name_{i} : PartIs F {litSpans (footprint src (Parse.strAt names sec.header.name))} (Parse.strAt sh{h.sectionNameIndex} {sec.header.name}) n{i} :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
  d := d ++ s!"/-- **The layout**: header, program headers, named sections. -/
def L : Layout :=
  ⟨hdr, [{", ".intercalate ((List.range L.phdrs.length).map (s!"ph{·}"))}],
    [{", ".intercalate ((List.range L.sections.length).map fun i => s!"⟨sh{i}, n{i}⟩")}]⟩

"
  t := t ++ s!"/-- **The layout** (stage 1 of `Silmaril.Elf.Staged`), one run over its footprint. -/
theorem layoutPart : PartIs F {litSpans (footprint src readLayout)} readLayout L :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

theorem layout : LayoutIs F L := layoutPart.layoutIs

"
  let mut bnames : Array String := #[]
  let mut fnThms : Array String := #[]
  let mut fns := s!"module

public import {ns}.Thms

/-! # {title}: its function symbols, one theorem each

{gen}

For every `STT_FUNC` or `STT_GNU_IFUNC` entry of a symbol table (defined or not), the entry as the
specification's reader `Parse.symbol` reads it from the 24-byte record and the name bytes in the
linked string table, and nothing else (`PartIs`, closed by `decide +kernel` on kernel bytes). A
row says what the symbol table says: its name, value, size, binding, type and section index. It
does not say that the bytes at `value` are a function, or anything about the System V ABI. -/

@[expose] public section

namespace {ns}

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader

"
  let mut bodyArr : Array Body := #[]
  let mut skipped : Array Nat := #[]
  for (sec, k) in L.sections.zipIdx do
    let some b := (Parse.body shs sec.header).run src | throw (IO.userError s!"body {k} failed")
    bodyArr := bodyArr.push b
    bnames := bnames.push s!"body_{k}.bodyIs"
    match b with
    | .symbols tab es =>
      let some strs := shs[sec.header.link]? | throw (IO.userError s!"symbol table {k}: no string table")
      for (e, i) in es.zipIdx do
        d := d ++ s!"def s{k}_{i} : ObjectSymbol := ⟨⟨{e.raw.name}, {e.raw.info}, {e.raw.other}, {e.raw.sectionIndex}, {e.raw.value}, {e.raw.size}⟩, {litName e.name}⟩\n"
        let ty := e.raw.info % 16
        if ty == 2 || ty == 10 then
          let o := sec.header.offset + 24 * i
          fnThms := fnThms.push s!"/-- `{nameStr e.name}` (section {k}, entry {i}). -/
theorem sym_{k}_{i} : PartIs F {litSpans (footprint src (Parse.symbol strs o))} (Parse.symbol sh{sec.header.link} {o}) s{k}_{i} :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
      let t' := if tab == .symtab then "symtab" else "dynsym"
      d := d ++ s!"\n/-- The body of section {k} (`{nameStr sec.name}`): {es.length} symbols. -/\ndef b{k} : Body :=\n  .symbols .{t'} [{", ".intercalate ((List.range es.length).map (s!"s{k}_{·}"))}]\n\n"
    | .relas es =>
      if maxEntries.isNone || es.length ≤ 4096 then
        d := d ++ s!"/-- The body of section {k} (`{nameStr sec.name}`). -/\ndef b{k} : Body :=\n  {(reprStr b).replace "\n" " "}\n\n"
      else
        -- a long table as consecutive chunks, so that no single literal nests too deeply
        let cs := listChunks 512 es
        let mut names : Array String := #[]
        for (c, j) in cs.zipIdx do
          d := d ++ s!"/-- Entries {j * 512} to {j * 512 + c.length - 1} of section {k} (`{nameStr sec.name}`). -/\ndef b{k}_{j} : List Silmaril.Formats.ELF.Rela :=\n  {(reprStr c).replace "\n" " "}\n\n"
          names := names.push s!"b{k}_{j}"
        let all := names.toList.foldr (fun nm acc => if acc == "" then nm else s!"{nm} ++ ({acc})") ""
        d := d ++ s!"/-- The body of section {k} (`{nameStr sec.name}`): {es.length} entries. -/\ndef b{k} : Body :=\n  .relas ({if all == "" then "[]" else all})\n\n"
    | _ =>
      d := d ++ s!"/-- The body of section {k} (`{nameStr sec.name}`). -/\ndef b{k} : Body :=\n  {(reprStr b).replace "\n" " "}\n\n"
    let big := match b, maxEntries with
      | .symbols _ es, some m => decide (m < es.length)
      | .relas es, some m => decide (4 * m < es.length)
      | _, _ => false
    if big then skipped := skipped.push k
    unless big do t := t ++ s!"/-- **The body of section {k}** (`{nameStr sec.name}`). -/
theorem body_{k} : PartIs F {litSpans (footprint src (Parse.body shs sec.header))} (Parse.body L.shs sh{k}) b{k} :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
  d := d ++ s!"/-- The section bodies, in order. -/
def bodies : List Body := [{", ".intercalate ((List.range L.sections.length).map (s!"b{·}"))}]

/-- **The loader's view**: `PT_DYNAMIC`, `PT_INTERP`, `DT_NEEDED`, soname, runpath. -/
def ld : Loader := {litLoader ld}

end {ns}
"
  let forall2 := bnames.foldr (fun n acc => s!"(.cons {n} {acc})") ".nil"
  t := t ++ s!"/-- **The loader's view** (`PT_DYNAMIC`, `PT_INTERP`, the `DT_STRTAB` names). -/
theorem loader : PartIs F {litSpans (footprint src (readLoader L.phdrs))} (readLoader L.phdrs) ld :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

" ++ (if skipped.isEmpty then s!"/-- **The parse of the whole file** (`Silmaril.Elf.Parses`), assembled from the parts. -/
theorem parses : Parses F (L.assemble bodies ld) :=
  parses_assemble layout
    {forall2}
    loader.loaderIs

" else s!"/-! No whole-file `parses` theorem: the tables of sections {skipped.toList} (symbol tables of more than
{maxEntries.getD 0} entries, relocation tables of more than {4 * maxEntries.getD 0}) have no whole-table body theorem, since one kernel run over such a table
exceeds the budget of a module. Their function entries are checked one by one (`Functions`), and the
layout, the loader view and every other body are checked here. -/

")
  let mut nz : Array Span := #[]
  for (g, k) in (gaps L a.size (footprint src readLayout)).zipIdx do
    if allZero a g then
      t := t ++ s!"/-- **Padding**: the {g.len} bytes at {hex g.off} are zero. -/
theorem pad_{k} : ZerosAt F {g.off} {g.len} :=
  zerosAt_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

"
    else nz := nz.push g
  t := t ++ s!"end {ns}\n"
  unless L.assemble ((List.range L.sections.length).filterMap fun k =>
      (L.sections[k]?).bind fun s => (Parse.body shs s.header).run src) ld == A do
    throw (IO.userError "the assembled parts differ from the whole parse")
  let base := s!"{dir}/{name}"
  IO.FS.createDirAll base
  IO.FS.writeFile s!"{base}/Bytes.lean" bytesMod
  IO.FS.writeFile s!"{base}/Defs.lean" d
  IO.FS.writeFile s!"{base}/Thms.lean" t
  if maxEntries.isSome && fnThms.size > 1500 then
    -- many function symbols: one module per 1500 theorems, so that they are checked in parallel
    let parts := listChunks 1500 fnThms.toList
    IO.FS.createDirAll s!"{base}/Functions"
    let hdr := fns.splitOn "\n" |>.drop 3 |> "\n".intercalate
    for (c, j) in parts.zipIdx do
      IO.FS.writeFile s!"{base}/Functions/Part{j}.lean"
        (s!"module\n\npublic import {ns}.Thms\n" ++ hdr ++ String.join c ++ s!"end {ns}\n")
    IO.FS.writeFile s!"{base}/Functions.lean"
      (s!"module\n\n" ++ String.join ((List.range parts.length).map (s!"public import {ns}.Functions.Part{·}\n")) ++
        s!"\n/-! # {title}: its function symbols, one theorem each, in {parts.length} parts\n\n{gen} -/\n")
  else
    IO.FS.writeFile s!"{base}/Functions.lean" (fns ++ String.join fnThms.toList ++ s!"end {ns}\n")
  let (dec, report) := emitDecomp ns title gen L bodyArr
  IO.FS.writeFile s!"{base}/Decomp.lean" dec
  IO.println s!"wrote {base}/(Bytes,Defs,Thms,Functions,Decomp).lean; non-zero gaps (no theorem): {nz.toList.map fun g => (hex g.off, g.len)}"
  IO.println report

def usage : String :=
  "usage: elf-staged layout FILE | emit-reader FILE NAME SHA256 TITLE DIR [--namespace NS --include-path REL --generator SCRIPT [--max-table-entries N]] | bench FILE [TILES] | emit-example FILE DEFS_MODULE DEFS.lean THMS.lean --bytes-const NAME [--import M] [--namespace NS] [--tiles TILES --function F] | emit FILE OUT.lean [--rela-windows N] [--rela-window N] [--tiles TILES] [--tile-count N] [--tile-from OFFSET] [--whole] [--bodies] [--bytes-const NAME] [--import MODULE] [--namespace NS]"

partial def parseOpts : List String → EmitOpts → EmitOpts
  | "--rela-windows" :: n :: rest, o => parseOpts rest { o with relaWindows := n.toNat! }
  | "--rela-window" :: n :: rest, o => parseOpts rest { o with relaWindow := n.toNat! }
  | "--tiles" :: p :: rest, o => parseOpts rest { o with tiles := some p }
  | "--bodies" :: rest, o => parseOpts rest { o with bodies := true }
  | "--bytes-const" :: c :: rest, o => parseOpts rest { o with bytesConst := some c }
  | "--import" :: m :: rest, o => parseOpts rest { o with imports := o.imports ++ [m] }
  | "--namespace" :: n :: rest, o => parseOpts rest { o with ns := n }
  | "--whole" :: rest, o => parseOpts rest { o with whole := true }
  | "--tile-count" :: n :: rest, o => parseOpts rest { o with tileCount := n.toNat! }
  | "--tile-from" :: n :: rest, o => parseOpts rest { o with tileFrom := some n.toNat! }
  | _, o => o

end ElfStaged

open ElfStaged in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["layout", path] =>
    let a ← readFile path
    let L ← layoutOrFail (fastRead a)
    printLayout L a.size
    pure 0
  | ["bench", path] => bench path none; pure 0
  | ["bench", path, tiles] => bench path (some tiles); pure 0
  | "emit" :: path :: out :: rest => emit path out (parseOpts rest {}); pure 0
  | "emit-example" :: path :: defsMod :: defsOut :: thmsOut :: rest =>
    let fn := match rest.dropWhile (· != "--function") with
      | _ :: f :: _ => some f
      | _ => none
    emitExample path defsMod defsOut thmsOut (parseOpts (rest.filter (· != "--function")) {}) fn
    pure 0
  | ["emit-reader", path, name, sha, title, dir] => emitReader path name sha title dir; pure 0
  | ["emit-reader", path, name, sha, title, dir, "--namespace", ns, "--include-path", rel, "--generator", g] =>
    emitReader path name sha title dir (some ns) (some rel) (some g); pure 0
  | ["emit-reader", path, name, sha, title, dir, "--namespace", ns, "--include-path", rel, "--generator", g, "--max-table-entries", n] =>
    emitReader path name sha title dir (some ns) (some rel) (some g) n.toNat?; pure 0
  | _ => IO.eprintln usage; pure 2
