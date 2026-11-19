module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.Elf.Staged.Symbols.Defs

/-! # Function decompositions of executable sections (`Silmaril.Elf.Staged.Decomp`)

**`Decomposes F L x ps`**: section `x` of the ELF file `F` (whose layout is `L`) is an
executable `SHT_PROGBITS` section, and the **pieces** `ps`, in address order, tile its address
range `[sh_addr, sh_addr + sh_size)` exactly: every byte of the section lies in exactly one
piece. A piece is

* a **function** `.fn k i s`: entry `i` of the symbol table in section `k` of the file reads as
  `s` (`Symbols.SymAt`: the specification's `Parse.symbol` on the file's bytes), and `s` is a
  defined `STT_FUNC` or `STT_GNU_IFUNC` symbol of section `x`, with nonzero `st_size`, whose
  extent `[st_value, st_value + st_size)` is exactly the piece; or
* a **gap** `.gap n`: `n > 0` bytes that no chosen function symbol covers.

So a decomposition is a partition of the section's bytes into symbol-table function extents
and explicit gaps, checked against the file. It is what the symbol table says about where the
functions are, made exact and disjoint:

* it does **not** say that a function's bytes decode as instructions, that control stays inside
  the extent, or that the function meets any contract (those are separate statements: decoding
  `Silmaril.Elf.Asm`/`Staged.TilesAt`, semantics `silmaril.shapes.x86.*`);
* a gap may hold alignment padding, code without a symbol (stripped files keep only exported
  symbols in `.dynsym`), or code of a symbol left out because its extent overlaps another
  chosen one; the emitter reports which;
* aliases (several symbols with the same extent) are represented by one of them;
* it holds for any `e_machine` (the ELF reader records it, never interprets it), so the same
  statement serves x86-64, AArch64 and RISC-V files.

`tilesB` is the Boolean check of `Tiles` (`Thms.tilesB_iff`), and `decomposes_of` (in `Thms`)
assembles a decomposition from the layout, one `SymAt` fact per function piece (each from a
checked `PartIs` symbol theorem), and one kernel run of `tilesB`. Generated per file by
`elf-staged emit-reader` (`Decomp.lean` next to `Functions.lean`).
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Decomp

open Silmaril.Formats.ELF (SectionHeader ObjectSymbol)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.Elf.Staged.Symbols (Tab SymAt)
open Silmaril.X86.Link (Blob)

/-- `STT_FUNC`. -/
def STT_FUNC : Nat := 2

/-- `STT_GNU_IFUNC`. -/
def STT_GNU_IFUNC : Nat := 10

/-- A piece of a decomposition. -/
inductive Piece where
  /-- The function of entry `i` of the symbol table in section `k`, which reads as `s`. -/
  | fn (k i : Nat) (s : ObjectSymbol)
  /-- `len` bytes covered by no chosen function symbol. -/
  | gap (len : Nat)
  deriving DecidableEq, Repr

/-- The number of bytes a piece covers. -/
def Piece.len : Piece → Nat
  | .fn _ _ s => s.raw.size
  | .gap n => n

/-- **`s` is a defined function symbol of section `x` with a nonempty extent starting at `a`.** -/
abbrev FnAt (x a : Nat) (s : ObjectSymbol) : Prop :=
  s.raw.value = a ∧ 0 < s.raw.size ∧ s.raw.sectionIndex = x ∧
    (s.kind = STT_FUNC ∨ s.kind = STT_GNU_IFUNC)

/-- **The pieces `ps` tile `[a, e)`**, in order, each nonempty; a function piece of section `x`
starts where the previous piece ends. -/
def Tiles (x : Nat) : Nat → Nat → List Piece → Prop
  | a, e, [] => a = e
  | a, e, .gap n :: ps => 0 < n ∧ Tiles x (a + n) e ps
  | a, e, .fn _ _ s :: ps => FnAt x a s ∧ Tiles x (a + s.raw.size) e ps

/-- The Boolean check of `Tiles` (`Thms.tilesB_iff`); tail-recursive, so the kernel runs it on
thousands of pieces. -/
def tilesB (x : Nat) : Nat → Nat → List Piece → Bool
  | a, e, [] => a == e
  | a, e, .gap n :: ps => decide (0 < n) && tilesB x (a + n) e ps
  | a, e, .fn _ _ s :: ps => decide (FnAt x a s) && tilesB x (a + s.raw.size) e ps

/-- A section header of a symbol table (`SHT_SYMTAB` or `SHT_DYNSYM`). -/
abbrev IsSymTab (sh : SectionHeader) : Prop := sh.kind = SHT_SYMTAB ∨ sh.kind = SHT_DYNSYM

/-- **Entry `i` of the symbol table in section `k` of `L` reads as `s` in `F`**: section `k` is a
symbol table, its linked string table is section `sh_link`, and `Symbols.SymAt` holds. -/
def SymbolIs (F : Blob) (L : Layout) (k i : Nat) (s : ObjectSymbol) : Prop :=
  ∃ tab strs, L.shs[k]? = some tab ∧ IsSymTab tab ∧ L.shs[tab.link]? = some strs ∧
    SymAt F ⟨strs, tab⟩ i s

/-- What a piece claims about the file: a function piece, its symbol-table entry. -/
def Piece.Read (F : Blob) (L : Layout) : Piece → Prop
  | .fn k i s => SymbolIs F L k i s
  | .gap _ => True

/-- An executable `SHT_PROGBITS` section header (`SHF_EXECINSTR` set). -/
abbrev IsExec (sh : SectionHeader) : Prop := sh.kind = SHT_PROGBITS ∧ sh.flags / SHF_EXECINSTR % 2 = 1

/-- **Section `x` of `F` (layout `L`) decomposes into the functions and gaps `ps`.** -/
def Decomposes (F : Blob) (L : Layout) (x : Nat) (ps : List Piece) : Prop :=
  LayoutIs F L ∧ ∃ sh, L.shs[x]? = some sh ∧ IsExec sh ∧
    Tiles x sh.address (sh.address + sh.size) ps ∧ ∀ p ∈ ps, p.Read F L

/-- The function pieces. -/
def functions (ps : List Piece) : List (Nat × Nat × ObjectSymbol) :=
  ps.filterMap fun | .fn k i s => some (k, i, s) | .gap _ => none

/-- The bytes the function pieces cover. -/
def covered (ps : List Piece) : Nat :=
  (ps.map fun | .fn _ _ s => s.raw.size | .gap _ => 0).sum

end Silmaril.Elf.Staged.Decomp
