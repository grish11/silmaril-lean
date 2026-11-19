module

public import Silmaril.Elf.Staged.Decomp.Defs

/-! # Function decompositions: the Boolean tiling check is the tiling (standard axioms) -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Staged.Decomp

open Silmaril.Elf.Staged.Decomp

theorem tilesB_iff (x : Nat) : ∀ (a e : Nat) (ps : List Piece), tilesB x a e ps = true ↔ Tiles x a e ps
  | a, e, [] => by simp [tilesB, Tiles]
  | a, e, .gap n :: ps => by
    simp only [tilesB, Tiles, Bool.and_eq_true, decide_eq_true_eq, tilesB_iff x (a + n) e ps]
  | a, e, .fn _ _ s :: ps => by
    simp only [tilesB, Tiles, Bool.and_eq_true, decide_eq_true_eq, tilesB_iff x (a + s.raw.size) e ps]

end Silmaril.Proofs.Elf.Staged.Decomp
