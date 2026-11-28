module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Routes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableRoutes

/-! # Exact interfaces of the routed entry and rows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.RetainedLet (unpackBody_typed)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A repeat retains the capture and tags its label. The outward exit
forwards its payload directly. -/
theorem carryExit_typed (R : LCtx τ) {Γ : VCtx τ} {X D : τ} {k : Nat} (hx : At Γ k X) :
    LSubst.ValueFamily Γ (R ++ [D])
      [coprod D (product X (packedExitType R))] (carryExit k R.length : Nat → Region Φ) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback.carryExit_typed R hx

/-- The written entry may itself contain guarded CFGs. -/
theorem entry_route {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D])) :
    ValueBranches [X] (e.lsubst (carryExit 0 n)) [coprod D (product X (packedExitType (List.ofFn R)))] := by
  simpa only [List.length_ofFn] using he.lsubst (carryExit_typed (List.ofFn R) (rfl : At [X] 0 X))

/-- The row uses slot 1 for its capture before the outgoing label adds a
payload binder. Unpacking the input gives the invocation expected by the
captured dispatcher. -/
theorem local_route {n : Nat} (R : Fin n → τ) {X D : τ} {blocks : Fin n → Region Φ}
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) (i : Fin n) :
    ValueBranches [product X (R i)] (Paper.RetainedLet.unpackBody ((blocks i).lsubst (carryExit 1 n)))
      [coprod D (product X (packedExitType (List.ofFn R)))] := by
  simpa only [List.length_ofFn] using
    unpackBody_typed ((hb i).lsubst (carryExit_typed (List.ofFn R) (rfl : At [R i, X] 1 X)))

/-- Keep the literal entry and every nested local label. Shift only its
outward labels beyond the enclosing table. -/
theorem outwardEntry {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    (he : ValueBranches [X] e [D]) :
    ValueBranches [X] (e.renameLabels (n + ·)) (List.ofFn R ++ [D]) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback.outwardEntry R he

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
