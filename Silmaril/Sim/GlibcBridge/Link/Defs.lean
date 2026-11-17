module

public import Silmaril.Machine.Link.Blob.Defs
public import Silmaril.X86.Open9.Defs
public import Silmaril.X86.RelIsa.Safe.Defs

/-! # Dynamic linking: objects, an eager loader relation, library specs (DL1)

A first model of dynamically linked x86-64 processes.

**Objects.** `Obj` is what the loader needs from one ELF file (executable or `.so`): its
`DT_SONAME`, its `DT_NEEDED` names, the dynamic symbols it defines (`defines`, with the
`STT_GNU_IFUNC` bit), its dynamic relocations (`DT_RELA` and `DT_JMPREL`), and the file bytes of
its read-only `PT_LOAD` segments (`slice`). `Obj.ofBlob` reads all of it from a file through the
kernel-fast readers of `Silmaril.Machine.Link.Blob` (`readHeaderN`, `readProgramHeadersN`,
`readSectionHeadersN`, `readSymbolN`, `readRelaN`, each proved equal to the public reader there);
the dynamic-section walk itself (`dynEntries`, `vToOff`, `cstr`) is new and unverified against
any other reader. The symbol count comes from the `SHT_DYNSYM` section header (the loader uses
the hash table instead; on the pinned files the two agree, which nothing here proves).

**The loader.** A link map `LinkMap` is a list of objects with load bases, in global-scope
search order (the executable first, then the `DT_NEEDED` closure; `LD_PRELOAD` objects would come
second). Symbol lookup `resolveIn` takes the first object that defines the name: this *is* ELF
interposition, not an approximation of it. An ifunc definition resolves to `ifn (resolver
address)`, so the resolver's choice is a parameter of the model, not something it computes.
`relValue` covers `R_X86_64_RELATIVE` (8, `B + A`), `GLOB_DAT` (6) and `JUMP_SLOT` (7) (`S`, or 0
for an unresolved weak reference) and `IRELATIVE` (37, `ifn (B + A)`); any other kind has no value,
so `EagerLoaded` cannot hold for an object that uses one.

`EagerLoaded lm ifn mem` is the **eager-binding loader relation** (`DF_BIND_NOW`), a trusted
specified component rather than a verified loader: `mem` is a post-load memory in which the
`DT_NEEDED` closure is present and every object's `ObjImage` is in place: every relocation holds
its value as an 8-byte word at `base + r_offset`, and every read-only segment's file bytes are
mapped at `base + vaddr` with its permissions (no `DT_TEXTREL`). Not modelled: symbol versions (names only), TLS,
`DT_INIT`/`DT_INIT_ARRAY` order, lazy binding, `dlopen`, `COPY` relocations, the auxiliary
vector, and which bases the kernel and `ld.so` pick (every base is allowed).

**Specs.** `Contract` (a precondition on the entry state and a relation to the final state),
`Meets A P f c` (from every entry state at `f` meeting `c.pre`, with memory in `P`, `A` must reach
`c.post`, demonic `RelIsa.Must`), `LibSpec` (named contracts), `Sat A P addr S` (each name
resolves through `addr` to an address meeting its contract), `LibSpec.Le S T` (`T` is stronger: it has every name of `S`
with a contract that refines `S`'s), `Exports A L lb ifn S` (the library `L` loaded at `lb`
meets `S` with its own definitions). `ExtendsOpen9 A`: wherever `Open9.step` retires, `A`'s only
outcome is that state (true of `ofFun Open9.step` and of process machines that add syscalls).

**Kept here for the glibc bridge** (`Silmaril.Sim.GlibcBridge`): main retired this first study
(`Silmaril.Elf.Link.Dyn.{Defs,Thms}`, commit 822f87b73) in favour of the whole-process stack
`Silmaril.Elf.Link.Dyn.*`; the bridge's `ghelloLinkMap`/`got_puts` still use this loader
relation, so the definitions are copied unchanged into `Silmaril.Sim.GlibcBridge.Link` until the
bridge is ported to `Silmaril.Elf.Link.Dyn.Loader`.
-/

@[expose] public section

namespace Silmaril.Sim.GlibcBridge.Link

open Silmaril.X86 (Word Byte MState)
open Silmaril.Process (Memory)
open Silmaril.Formats.ELF (ProgramHeader)
open Silmaril.Machine.Link (Blob)
open Silmaril.X86 (RelIsa)

/-- A symbol or library name, as its bytes. -/
abbrev Name := List Nat

/-- The bytes of a string literal. -/
def nm (s : String) : Name := s.toList.map Char.toNat

/-! ## Objects -/

/-- A dynamic symbol definition: `st_value`, and whether it is `STT_GNU_IFUNC`. -/
structure Def where
  value : Nat
  ifunc : Bool
  deriving DecidableEq, Repr

/-- A dynamic relocation, with its symbol already looked up in the object's `.dynsym`. -/
structure Rel where
  offset : Nat
  kind : Nat
  sym : Name
  /-- The symbol is `STB_WEAK` (an unresolved weak reference becomes 0). -/
  weak : Bool
  addend : Int
  deriving DecidableEq, Repr

/-- What the loader needs from one ELF file. -/
structure Obj where
  soname : Option Name
  needed : List Name
  defines : Name → Option Def
  rels : List Rel
  /-- `slice v k`: the `k` file bytes at virtual address `v`, when they lie in one read-only
  `PT_LOAD` segment, with its `p_flags`. -/
  slice : Nat → Nat → Option (List Byte × Nat)

/-- A link map: objects with load bases, in global-scope search order. -/
abbrev LinkMap := List (Obj × Word)

/-! ## Reading an object from a file -/

namespace Read

/-- The `k` bytes at file offset `off`. -/
def bytesAt (b : Blob) (off k : Nat) : List Byte := (List.range k).map fun i => Blob.byteAt b.n (off + i)

/-- The NUL-terminated string at file offset `off` (at most `fuel` bytes). -/
def cstr (b : Blob) (off : Nat) (fuel : Nat := 64) : Name :=
  ((List.range fuel).map fun i => (Blob.byteAt b.n (off + i)).toNat).takeWhile (· ≠ 0)

/-- The file offset of virtual address `v`, through the `PT_LOAD` that maps it from the file. -/
def vToOff (phs : List ProgramHeader) (v : Nat) : Option Nat :=
  (phs.find? fun ph => ph.kind == 1 && ph.virtualAddress ≤ v && v < ph.virtualAddress + ph.fileSize).map
    fun ph => v - ph.virtualAddress + ph.offset

/-- The `(d_tag, d_val)` entries of `PT_DYNAMIC`, up to `DT_NULL`. -/
def dynEntries (b : Blob) (phs : List ProgramHeader) : List (Nat × Nat) :=
  match phs.find? (·.kind == 2) with
  | none => []
  | some ph =>
    ((List.range (ph.fileSize / 16)).filterMap fun i =>
      match Blob.readLEN b.n b.len (ph.offset + 16 * i) 8, Blob.readLEN b.n b.len (ph.offset + 16 * i + 8) 8 with
      | some t, some v => some (t, v)
      | _, _ => none).takeWhile (·.1 ≠ 0)

/-- The value of the first entry with tag `t`. -/
def tag (es : List (Nat × Nat)) (t : Nat) : Option Nat := (es.find? (·.1 == t)).map (·.2)

/-- The program headers of a file. -/
def phdrs (b : Blob) : List ProgramHeader :=
  ((Blob.readHeaderN b.n b.len).bind (Blob.readProgramHeadersN b.n b.len)).getD []

/-- The dynamic entries of a file. -/
def dyn (b : Blob) : List (Nat × Nat) := dynEntries b (phdrs b)

/-- File offset of the address in tag `t`. -/
def tagOff (b : Blob) (t : Nat) : Option Nat := (tag (dyn b) t).bind (vToOff (phdrs b))

/-- The string at `DT_STRTAB + i`. -/
def str (b : Blob) (i : Nat) : Name := match tagOff b 5 with
  | some s => cstr b (s + i)
  | none => []

/-- Dynamic symbol `i` (`DT_SYMTAB + 24 i`). -/
def sym (b : Blob) (i : Nat) : Option Silmaril.Formats.ELF.Symbol :=
  (tagOff b 6).bind fun s => Blob.readSymbolN b.n b.len (s + 24 * i)

/-- The number of dynamic symbols, from the `SHT_DYNSYM` section header. -/
def symCount (b : Blob) : Nat :=
  let shs := ((Blob.readHeaderN b.n b.len).bind (Blob.readSectionHeadersN b.n b.len)).getD []
  ((shs.find? (·.kind == 11)).map fun sh => sh.size / 24).getD 0

/-- The definition of `name`: a defined (`st_shndx ≠ 0`), global or weak, default-visibility
dynamic symbol with that name; `STT_GNU_IFUNC` is type 10. -/
def defines (b : Blob) (name : Name) : Option Def :=
  ((List.range (symCount b)).findSome? fun i => match sym b i with
    | some s => if s.sectionIndex ≠ 0 ∧ (s.binding = 1 ∨ s.binding = 2) ∧ s.other % 4 = 0 ∧
        str b s.name = name then some ⟨s.value, s.kind == 10⟩ else none
    | none => none)

/-- The `count` RELA entries at the address in tag `t`. -/
def relaAt (b : Blob) (t count : Nat) : List Rel :=
  match tagOff b t with
  | none => []
  | some off => (List.range count).filterMap fun i =>
    (Blob.readRelaN b.n b.len (off + 24 * i)).map fun r =>
      let s := sym b r.symbolIndex
      { offset := r.offset, kind := r.relocationType
        sym := if r.symbolIndex = 0 then [] else (s.map fun s => str b s.name).getD []
        weak := (s.map fun s => s.binding == 2).getD false
        addend := r.addend }

/-- `DT_RELA`/`DT_RELASZ` then `DT_JMPREL`/`DT_PLTRELSZ`. -/
def rels (b : Blob) : List Rel :=
  relaAt b 7 ((tag (dyn b) 8).getD 0 / 24) ++ relaAt b 23 ((tag (dyn b) 2).getD 0 / 24)

/-- The file bytes at `[v, v+k)` when they lie in one read-only `PT_LOAD`. -/
def slice (b : Blob) (v k : Nat) : Option (List Byte × Nat) :=
  ((phdrs b).find? fun ph => ph.kind == 1 && ph.flags % 4 / 2 == 0 && ph.virtualAddress ≤ v &&
      v + k ≤ ph.virtualAddress + ph.fileSize).map fun ph =>
    (bytesAt b (v - ph.virtualAddress + ph.offset) k, ph.flags)

end Read

/-- The loader's view of a file. -/
def Obj.ofBlob (b : Blob) : Obj where
  soname := (Read.tag (Read.dyn b) 14).map (Read.str b)
  needed := ((Read.dyn b).filter (·.1 == 1)).map fun e => Read.str b e.2
  defines := Read.defines b
  rels := Read.rels b
  slice := Read.slice b

/-! ## The eager loader relation -/

/-- **Symbol lookup in global scope**: the first object that defines `n`. -/
def resolveIn (ifn : Word → Option Word) : LinkMap → Name → Option Word
  | [], _ => none
  | (o, b) :: rest, n => match o.defines n with
    | some d => if d.ifunc then ifn (b + BitVec.ofNat 64 d.value) else some (b + BitVec.ofNat 64 d.value)
    | none => resolveIn ifn rest n

/-- The word a relocation of the object at base `b` holds after eager loading. -/
def relValue (lm : LinkMap) (ifn : Word → Option Word) (b : Word) (r : Rel) : Option Word :=
  if r.kind = 8 then some (b + BitVec.ofInt 64 r.addend)
  else if r.kind = 6 ∨ r.kind = 7 then
    match resolveIn ifn lm r.sym with
    | some v => some v
    | none => if r.weak then some 0 else none
  else if r.kind = 37 then ifn (b + BitVec.ofInt 64 r.addend)
  else none

/-- Every `DT_NEEDED` name is the `DT_SONAME` of some object of the map. -/
def Closed (lm : LinkMap) : Prop := ∀ e ∈ lm, ∀ n ∈ e.1.needed, ∃ e' ∈ lm, e'.1.soname = some n

/-- **One object's post-load image** in `mem`, for the link map `lm`: each relocation holds its
value as an 8-byte word at `base + r_offset`, and the file bytes of each read-only segment are
mapped at `base + vaddr`, fetchable if `PF_X`, readable if `PF_R`. -/
structure ObjImage (lm : LinkMap) (ifn : Word → Option Word) (e : Obj × Word) (mem : Memory) :
    Prop where
  relocated : ∀ r ∈ e.1.rels, ∃ v, relValue lm ifn e.2 r = some v ∧
    Silmaril.X86.Ext.loadN mem (e.2 + BitVec.ofNat 64 r.offset) 8 = some v
  code : ∀ v k bs fl, e.1.slice v k = some (bs, fl) → fl % 2 = 1 →
    Silmaril.X86.Ext.Loaded mem (e.2 + BitVec.ofNat 64 v) bs
  rodata : ∀ v k bs fl, e.1.slice v k = some (bs, fl) → fl / 4 % 2 = 1 →
    mem.readBytes (e.2 + BitVec.ofNat 64 v).toNat k = some bs

/-- **The eager-binding loader relation**: the closure is present and every object's image is
in place. -/
structure EagerLoaded (lm : LinkMap) (ifn : Word → Option Word) (mem : Memory) : Prop where
  closed : Closed lm
  image : ∀ e ∈ lm, ObjImage lm ifn e mem

/-! ## Machines and specs -/

/-- `A` takes exactly the `Open9` step wherever `Open9` retires. -/
def ExtendsOpen9 (A : RelIsa MState) : Prop :=
  ∀ m m', Silmaril.X86.Open9.step m = some m' → ∀ r, A.step m r ↔ r = .ok m'

/-- A function contract: a precondition on the entry state, a relation entry ↦ final state. -/
structure Contract where
  pre : MState → Prop
  post : MState → MState → Prop

/-- `d` refines `c`: it accepts more entry states and promises more. -/
def Contract.Le (c d : Contract) : Prop :=
  (∀ m, c.pre m → d.pre m) ∧ ∀ m m', c.pre m → d.post m m' → c.post m m'

/-- **The code at `f` meets `c` on `A`** from every entry state whose memory satisfies `P` (the
part of the post-load image the code relies on): every run reaches `post`. -/
def Meets (A : RelIsa MState) (P : Memory → Prop) (f : Word) (c : Contract) : Prop :=
  ∀ m, P m.memory → m.core.rip = f → c.pre m → RelIsa.Must A (fun _ => True) (c.post m) m

/-- A library spec: named contracts. -/
abbrev LibSpec := List (Name × Contract)

/-- Every name of `S` resolves through `addr` to code meeting its contract. -/
def Sat (A : RelIsa MState) (P : Memory → Prop) (addr : Name → Option Word) (S : LibSpec) :
    Prop :=
  ∀ p ∈ S, ∃ f, addr p.1 = some f ∧ Meets A P f p.2

/-- `T` is at least as strong as `S`: every entry of `S` has an entry of `T`, of the same
name, whose contract refines it. -/
def LibSpec.Le (S T : LibSpec) : Prop := ∀ p ∈ S, ∃ q ∈ T, q.1 = p.1 ∧ p.2.Le q.2

/-- **The library `L` at base `lb` meets `S` with its own definitions** (its export spec), in
every link map that contains it, from any memory holding its own post-load image. This is a
closed-world spec: it does not assume anything of what `L`'s own imports resolve to (the
import-conditioned `LibCorrect` form is future work, see the note). -/
def Exports (A : RelIsa MState) (L : Obj) (lb : Word) (ifn : Word → Option Word) (S : LibSpec) :
    Prop :=
  ∀ lm, (L, lb) ∈ lm → Sat A (ObjImage lm ifn (L, lb)) (resolveIn ifn [(L, lb)]) S

/-! ## Common contract pieces (SysV x86-64) -/

/-- `s` (no NUL) is a C string at `a`: `s ++ [0]` is readable there. -/
def CStr (mem : Memory) (a : Word) (s : List Byte) : Prop :=
  (∀ x ∈ s, x ≠ 0) ∧ mem.readBytes a.toNat (s.length + 1) = some (s ++ [0])

/-- The return address of a call whose entry state is `m`: the word `pop` reads at `[rsp]`. -/
def retAddr (m : MState) : Option Word := (Silmaril.X86.popWord m.core m.memory).map (·.1)

/-- `m` is a call entry: the return address is readable. -/
def CallFrame (m : MState) : Prop := (retAddr m).isSome

/-- `m'` is a return from the call whose entry state is `m`: `rip` is the return address and
`rsp` is 8 higher. -/
def RetTo (m m' : MState) : Prop :=
  ∃ ret, retAddr m = some ret ∧ m'.core.rip = ret ∧ m'.core.read .rsp = m.core.read .rsp + 8#64

end Silmaril.Sim.GlibcBridge.Link
