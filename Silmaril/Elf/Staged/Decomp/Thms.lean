module

public import Silmaril.Elf.Staged.Decomp.Defs
public import Silmaril.Elf.Staged.Reader.Thms
import Silmaril.Proofs.Elf.Staged.Decomp

/-! # Function decompositions: assembling one from checked parts

`decomposes_of` builds `Decomposes F L x ps` from the layout (`LayoutIs`), the section header,
one kernel run of `tilesB`, and `∀ p ∈ ps, p.Read F L`, which the `read_*` lemmas build from
the per-symbol `PartIs` theorems of a file's `Functions` module (`symbolIs_of_partIs`). -/

@[expose] public section

namespace Silmaril.Elf.Staged.Decomp

open Silmaril.Formats.ELF (SectionHeader ObjectSymbol)
open Silmaril.Elf.Staged.Reader (PartIs)
open Silmaril.Elf.Staged.Symbols (Tab SymAt)
open Silmaril.X86.Link (Blob)

/-- The Boolean tiling check is the tiling. -/
theorem tilesB_iff (x a e : Nat) (ps : List Piece) : tilesB x a e ps = true ↔ Tiles x a e ps :=
  Proofs.Elf.Staged.Decomp.tilesB_iff x a e ps

/-- **A symbol-table entry from a checked `PartIs` symbol theorem.** -/
theorem symbolIs_of_partIs {F : Blob} {L : Layout} {k i : Nat} {s : ObjectSymbol}
    {tab strs : SectionHeader} {ws : List Span}
    (hk : L.shs[k]? = some tab) (ht : IsSymTab tab) (hs : L.shs[tab.link]? = some strs)
    (hi : i < tab.size / 24) (h : PartIs F ws (Parse.symbol strs (tab.offset + 24 * i)) s) :
    SymbolIs F L k i s :=
  ⟨tab, strs, hk, ht, hs, hi, h.run⟩

/-- `symbolIs_of_partIs` with the entry's file offset given as a literal (`ho`, by `decide`). -/
theorem symbolIs_of_partIs' {F : Blob} {L : Layout} {k i o : Nat} {s : ObjectSymbol}
    {tab strs : SectionHeader} {ws : List Span}
    (hk : L.shs[k]? = some tab) (ht : IsSymTab tab) (hs : L.shs[tab.link]? = some strs)
    (hi : i < tab.size / 24) (ho : tab.offset + 24 * i = o) (h : PartIs F ws (Parse.symbol strs o) s) :
    SymbolIs F L k i s :=
  symbolIs_of_partIs hk ht hs hi (ho ▸ h)

theorem read_nil {F : Blob} {L : Layout} : ∀ p ∈ ([] : List Piece), p.Read F L :=
  fun _ h => nomatch h

theorem read_cons {F : Blob} {L : Layout} {p : Piece} {ps : List Piece} (h : p.Read F L)
    (t : ∀ q ∈ ps, q.Read F L) : ∀ q ∈ p :: ps, q.Read F L :=
  List.forall_mem_cons.2 ⟨h, t⟩

theorem read_append {F : Blob} {L : Layout} {ps qs : List Piece} (h : ∀ q ∈ ps, q.Read F L)
    (t : ∀ q ∈ qs, q.Read F L) : ∀ q ∈ ps ++ qs, q.Read F L :=
  List.forall_mem_append.2 ⟨h, t⟩

/-- **A decomposition from checked parts.** -/
theorem decomposes_of {F : Blob} {L : Layout} {x : Nat} {ps : List Piece} {sh : SectionHeader}
    (hL : LayoutIs F L) (hx : L.shs[x]? = some sh) (he : IsExec sh)
    (ht : tilesB x sh.address (sh.address + sh.size) ps = true) (hr : ∀ p ∈ ps, p.Read F L) :
    Decomposes F L x ps :=
  ⟨hL, sh, hx, he, (tilesB_iff _ _ _ _).1 ht, hr⟩

end Silmaril.Elf.Staged.Decomp
