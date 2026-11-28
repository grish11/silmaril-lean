module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Defs

/-! # Identify the normalized syntax with an existing direct request tree -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns.BitFragment.Recursive
open Paper.WithCaseBind.BitQuery.RequestTree (Tree Slots inputSlots)
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live slots Direct)

private theorem slots_ext {Γ : List (Silmaril.Ty Empty)} {n : Nat} {s t : Slots Γ n}
    (h : s.index = t.index) : s = t := by
  cases s
  cases t
  cases h
  rfl

private theorem slots_bind (n : Nat) : (slots n).bind = slots (n + 1) :=
  slots_ext (funext (Fin.cases rfl (fun _ => rfl)))

private theorem input_slots : inputSlots = slots 1 := by
  apply slots_ext
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem written {n : Nat} (t : Normal 2 n) : t.tree.writtenRegion (slots n) = t.region := by
  induction t with
  | ret exit i => fin_cases exit <;> rfl
  | ask label i l r il ir =>
    change Region.case (request label (.read i)) (l.tree.writtenRegion (slots _).bind)
      (r.tree.writtenRegion (slots _).bind) = _
    rw [slots_bind, il, ir]
    rfl

theorem written_input (p : Program) : p.tree.writtenRegion inputSlots = (p.normalize id).region := by
  rw [input_slots]
  exact written (p.normalize id)

theorem direct {n : Nat} (t : Normal 2 n) : Direct t.tree := by
  induction t with
  | ret out i => exact .ret (out.val == 1) i
  | ask label i _ _ il ir => exact .var label i il ir

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive
