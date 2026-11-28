module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback

/-! # Native readback when the entry reaches only outward labels -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The written table equals its concrete captured dispatcher readback when
the entry is an outward shift of an arbitrary guarded region. The entry may
contain nested CFGs and effects. The table may have any arity or feedback
in its rows, since no local row is entered by this outer CFG. -/
theorem readback_outward
  {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ} {blocks : Fin n → Region Φ}
    (he : ValueBranches [X] e [D])
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R (outwardEntry R he) hb :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback.readback_outward pe R he hb

/-- An exact equality at the written entry transports the readback through
both the original table and the captured routing. The rows are used as written. -/
theorem readback_of_outward_eqv
    {n : Nat} (R : Fin n → τ) {X D : τ} {written e : Region Φ} {blocks : Fin n → Region Φ}
    (hw : ValueBranches [X] written (List.ofFn R ++ [D])) (he : ValueBranches [X] e [D])
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (route : Eqv pe [X] written (e.renameLabels (n + ·)) (List.ofFn R ++ [D])) :
    Readback pe R hw hb :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback.readback_of_outward_eqv
    pe R hw he hb route

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
