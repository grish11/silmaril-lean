module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction hiding Row Table
open OpenOperands.Silent (GuardedTable)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open CFG.Dependent.Native (sameRegion Typed jump routePacket packedRequestTo bind select)
open LambdaSSA.Region (packedExitType)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits exit_type)

universe u

variable {Φ : Type u} [DecidableEq Φ]

private theorem rename_self (r : LambdaSSA.Region Φ) (ok : sameRegion r r = true) (ρ : Nat → Nat) :
    sameRegion (r.renameLabels ρ) (r.renameLabels ρ) = true := by
  induction r generalizing ρ with
  | br => simp [sameRegion, LambdaSSA.Region.renameLabels]
  | case _ _ _ left right =>
    simp only [sameRegion, decide_true, Bool.true_and, Bool.and_eq_true] at ok
    simp [sameRegion, LambdaSSA.Region.renameLabels, left ok.1, right ok.2]
  | let₁ _ _ ih =>
    simp [sameRegion] at ok
    simp [sameRegion, LambdaSSA.Region.renameLabels, ih ok]
  | let₂ => simp [sameRegion] at ok
  | cfg _ _ _ entry blocks =>
    simp [sameRegion] at ok
    simp [sameRegion, LambdaSSA.Region.renameLabels, entry ok.1, fun i => blocks i (ok.2 i)]

variable [HasTy Φ Syntax.Ty] {Γ R L : List Syntax.Ty} {A B : Syntax.Ty}

private theorem subst_self (entry : Typed Φ Γ R) (ok : sameRegion entry.val entry.val = true)
    (branches : (i : Fin R.length) → Typed Φ (R.get i :: Γ) L)
    (arms : ∀ i, sameRegion (branches i).val (branches i).val = true) :
    sameRegion (nativeLsubst entry branches) (nativeLsubst entry branches) = true := by
  simp [nativeLsubst, sameRegion, ok, fun i => rename_self (branches i).val (arms i) (R.length + ·)]

private theorem jump_self (i : Fin L.length) (typed : L.get i = A) (arg : Syntax.Expr Γ A) :
    sameRegion (jump (Φ := Φ) i typed arg).val (jump (Φ := Φ) i typed arg).val = true := by
  simp [jump, sameRegion]

private theorem select_self (l : Typed Φ (A :: .coprod A B :: Γ) L)
    (r : Typed Φ (B :: .coprod A B :: Γ) L)
    (hl : sameRegion l.val l.val = true) (hr : sameRegion r.val r.val = true) :
    sameRegion (select l r).val (select l r).val = true := by
  unfold select
  apply subst_self
  · simp [Syntax.Program.caseRegion, sameRegion]
  · refine Fin.cases hl ?_
    intro i
    obtain rfl := Fin.eq_zero i
    exact hr

private theorem route_self (P : List Syntax.Ty) (target : Fin P.length → Fin L.length)
    (typed : ∀ i, L.get (target i) = P.get i) :
    sameRegion (routePacket (Φ := Φ) (Γ := Γ) target typed).val
      (routePacket (Φ := Φ) (Γ := Γ) target typed).val = true := by
  induction P generalizing Γ with
  | nil => simp [routePacket, LambdaSSA.Region.unpackExits, sameRegion]
  | cons A P ih =>
    rw [routePacket]
    exact select_self _ _ (jump_self _ _ _) (ih _ _)

private theorem cast_self (p : Typed Φ (A :: Γ) L) (h : A = B)
    (ok : sameRegion p.val p.val = true) :
    sameRegion (cast (congrArg (fun T => Typed Φ (T :: Γ) L) h) p).val
      (cast (congrArg (fun T => Typed Φ (T :: Γ) L) h) p).val = true := by
  cases h
  exact ok

private theorem packed_request_self (f : Φ) (operand : Syntax.Expr Γ (instrSrc f))
    (reply : instrTrg f = packedExitType R) (target : Fin R.length → Fin L.length)
    (typed : ∀ i, L.get (target i) = R.get i) :
    sameRegion (packedRequestTo f operand reply target typed).val
      (packedRequestTo f operand reply target typed).val = true := by
  unfold packedRequestTo CFG.Dependent.Native.bind
  apply subst_self
  · simp [Syntax.Program.requestRegion, sameRegion]
  · intro i
    obtain rfl := Fin.eq_zero i
    exact cast_self _ reply.symm (route_self R target typed)

theorem guarded_readback_self {S : RequestSignature Φ} (g : GuardedTable S R) :
    g.checkNative g.native = true := by
  have localSelf (i : Fin R.length) : sameRegion (g.blocks i).val (g.blocks i).val = true := by
    unfold OpenOperands.Table.blocks
    cases g.row i with
    | exit j => exact jump_self _ ((CFG.Dependent.external_type (R := R) (L := Exits) j).trans (exit_type j)) .unit
    | diverge => simp [OpenOperands.Row.native, CFG.Dependent.Native.diverge, nativeFeedback, jump, sameRegion]
    | request f operand next typed => exact packed_request_self f operand (S.target f) _ _
  simp [OpenOperands.Table.checkNative, OpenOperands.Table.native, nativeFeedback,
    sameRegion, OpenOperands.Table.entryRegion, jump, localSelf]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
