module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Routes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback (carryExit)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem carryExit_typed (R : LCtx τ) {Γ : VCtx τ} {X D : τ} {k : Nat} (hx : At Γ k X) :
    LSubst.ValueFamily Γ (R ++ [D])
      [coprod D (product X (packedExitType R))] (carryExit k R.length : Nat → Region Φ) := by
  intro i A hi
  by_cases internal : i < R.length
  · rw [carryExit, ite_eq_left internal]
    have localType : At R i A := (List.getElem?_append_left internal).symm.trans hi
    cases packExits_valueFamily (Φ := Φ) Γ R localType with
    | br ht value =>
      cases Option.some.inj ht
      exact .br (ℓ := 0) rfl (.inr (.pair (.var (i := k + 1) hx) value))
  · rw [carryExit, ite_eq_right internal]
    have outerType : At [D] (i - R.length) A :=
      (List.getElem?_append_right (Nat.le_of_not_gt internal)).symm.trans hi
    cases hs : i - R.length with
    | zero =>
      rw [hs] at outerType
      cases Option.some.inj outerType
      exact .br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))
    | succ j => simp [At, hs] at outerType

omit [TypeFormers τ] in
theorem outwardAt {n : Nat} (R : Fin n → τ) {L : LCtx τ} {j : Nat} {D : τ}
    (hi : At L j D) : At (List.ofFn R ++ L) (n + j) D := by
  have bound : (List.ofFn R).length ≤ n + j := by simp
  simpa only [At, List.getElem?_append_right bound, List.length_ofFn, Nat.add_sub_cancel_left] using hi


/-- Shifting outward labels preserves the guarded syntax. -/
theorem outwardEntry {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    (he : ValueBranches [X] e [D]) :
    ValueBranches [X] (e.renameLabels (n + ·)) (List.ofFn R ++ [D]) := by
  rw [renameLabels_eq_lsubst]
  exact he.lsubst (fun _ _ hi => .br (outwardAt R hi) (.var (i := 0) rfl))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback
