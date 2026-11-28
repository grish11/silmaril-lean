module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Defs

/-! # Materialize the existing numbered captured table as scoped flat syntax -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {n k exits : Nat} {β : BoundCtx τ n} {R : Fin k → τ} {L : LCtx τ} {A : τ}

omit [TypeFormers τ] in
theorem Target.index_lt (t : Target R L A) : t.index < k + L.length := by
  cases t with
  | «local» i => exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right ..)
  | exit typ =>
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp typ
    exact Nat.add_lt_add_left inside _

/-- The finite target bounds leave the original numbering intact. -/
def Target.flatIndex (length : L.length = exits) (t : Target R L A) : Fin (k + exits) :=
  ⟨t.index, length ▸ t.index_lt⟩

/-- The existing operands become literal flat operands. The captured
context remains in scope so the named checker can detect ambient block reads. -/
def Block.toFlat (length : L.length = exits) : Block Φ β R L A → Flat Φ (k + exits) (n + 1)
  | .jump a t => .br (t.flatIndex length) a.1
  | .case a l r => .case a.1 (.br (l.flatIndex length) (.bv 0)) (.br (r.flatIndex length) (.bv 0))

namespace Reverse

/-- Materialize the checked table without another numbering pass. -/
def CheckedTable.toFlat (c : CheckedTable Φ β L) (length : L.length = exits) :
    FiniteCFG Φ (c.size + 1) exits n :=
  ⟨.br (Fin.castAdd exits (0 : Fin (c.size + 1))) c.entry.1, fun i => (c.table.block i).toFlat length⟩

end Reverse
end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
