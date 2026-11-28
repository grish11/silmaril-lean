module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingGeneration

/-! # Generation in the existing tripling quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (returnOnce_typed)
open Paper.PackedBody (applyPacked_typed unpack_applyPacked)
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff iterateSum sumCofan whiskerLeftFunctor)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (Generated)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion T
local notation "Obj" => ofType T

/-- The selected returned terms use native sequencing and the existing pure
case-return equation. -/
theorem generated_returnFragment {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D}
    (h : Paper.WithCaseAndUnaryReturns.ReturnFragment pe ha) :
    Generated T (Lit (returnRegion_typed ha)) :=
  TriplingGeneration.generated_returnFragment pe h

/-- A computed primitive operand reduces to the generated call once that
specific returned call agrees with its explicit unary sequencing. -/
theorem generated_computedCall_of_rewrite {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p))
    (rewrite : Eqv pe [X] (returnRegion (.op p a))
      (returnRegion (.let₁ a (.op p (.var 0)))) [instrTrg p])
    (ga : Generated T (Lit (returnRegion_typed ha))) :
    Generated T (Lit (returnRegion_typed (.op (f := p) ha))) :=
  TriplingGeneration.generated_computedCall_of_rewrite pe p ha rewrite ga

/-- Induction on the guarded representative gives generation in the same quotient. -/
theorem generated_guardedFragment {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragment pe hr) : Generated T (Lit hr) :=
  TriplingGeneration.generated_guardedFragment pe h

/-- An explicit returned-scrutinee comparison suffices for this packed let. -/
theorem guarded_let₁_of_return {X A D : τ} {a : Tm Φ} {p : Region Φ}
    {ha : Tm.HasType [X] a A} {hp : ValueBranches [product X A] p [D]}
    (eq : Lit (returnRegion_typed ha) = Lit (returnOnce_typed ha))
    (producer : GuardedFragment pe (returnRegion_typed ha)) (body : GuardedFragment pe hp) :
    GuardedFragment pe (.let₁ ha (applyPacked_typed hp)) :=
  .let₁ (ha := ha) (hr := applyPacked_typed hp)
    (.eqv (hs := returnOnce_typed ha) ((ofRegion_eq_iff T _ _).mp eq) producer)
    (.eqv (hs := Paper.RetainedLet.unpackBody_typed (applyPacked_typed hp))
      (.paper (unpack_applyPacked hp).symm) body)

/-- The two scrutinee presentations are definitionally the same outside
the unary term binder. -/
theorem onceReturnAgreement_iff_let₁ :
    OnceReturnAgreement (τ := τ) (Φ := Φ) pe ↔
      (∀ {X A D : τ} {a b : Tm Φ} (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D),
        Lit (returnRegion_typed (.let₁ ha hb)) = Lit (returnOnce_typed (.let₁ ha hb))) := by
  unfold OnceReturnAgreement
  refine ⟨fun h {_ _ _ _ _} ha hb => h (.let₁ ha hb), ?_⟩
  intro h X A a ha
  cases ha <;> first | rfl | exact h ‹_› ‹_›

/-- The arbitrary-table constructor would follow from a quotient readback
to exact entry and dispatcher arrows with a packed captured state. -/
theorem generated_cfg_of_dispatcher_readback {n : Nat} {X D : τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : ValueBranches [X] entry (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    {start : Obj X ⟶ Obj (coprod D (product X (packedExitType (List.ofFn R))))}
    {step : Obj (product X (packedExitType (List.ofFn R))) ⟶ Obj (coprod D (product X (packedExitType (List.ofFn R))))}
    (gs : Generated T start) (gt : Generated T step)
    (readback : Lit (.cfg R he hb) = start ≫ exactCopair T (𝟙 (Obj D)) (iterateSum T step)) :
    Generated T (Lit (.cfg R he hb)) :=
  readback.symm ▸ .comp gs (.copair (.id D) (.iterate gt))

/-- Generated row arrows give a generated dispatcher at every finite label
list, including heterogeneous block payload types. -/
theorem generated_capturedDispatcher (X D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin L.length, Obj (product X (L.get i)) ⟶ Obj D)
    (generated : ∀ i, Generated T (rows i)) :
    Generated T (capturedDispatcher pe X L rows) :=
  TriplingGeneration.generated_capturedDispatcher pe X D L rows generated

/-- One retained-sum split selects the head row or the tail dispatcher.
The two routes preserve the captured product factor. -/
theorem capturedDispatcher_head_tail (X A D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin (A :: L).length, Obj (product X ((A :: L).get i)) ⟶ Obj D) :
    let whisker := whiskerLeftFunctor T (Obj X)
    let sum := sumCofan T A (packedExitType L)
    (whisker.map sum.inl ≫ capturedDispatcher pe X (A :: L) rows = rows 0) ∧
      (whisker.map sum.inr ≫ capturedDispatcher pe X (A :: L) rows =
        capturedDispatcher pe X L (fun i => rows i.succ)) :=
  TriplingGeneration.capturedDispatcher_head_tail pe X A D L rows

/-- The row hypotheses suffice for the transition assembly. The remaining
readback compares the original written CFG to the assembled iteration. -/
theorem generated_cfg_of_capturedRows_readback {n : Nat} {X D : τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : ValueBranches [X] entry (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    {start : Obj X ⟶ Obj (coprod D (product X (packedExitType (List.ofFn R))))}
    (rows : ∀ i : Fin (List.ofFn R).length, Obj (product X ((List.ofFn R).get i)) ⟶
      Obj (coprod D (product X (packedExitType (List.ofFn R)))))
    (gs : Generated T start) (gr : ∀ i, Generated T (rows i))
    (readback : Lit (.cfg R he hb) = start ≫
      exactCopair T (𝟙 (Obj D)) (iterateSum T (capturedDispatcher pe X (List.ofFn R) rows))) :
    Generated T (Lit (.cfg R he hb)) :=
  generated_cfg_of_dispatcher_readback pe R he hb gs
    (generated_capturedDispatcher pe X _ (List.ofFn R) rows gr) readback

/-- The full-quotient comparison's generation premise is exactly coverage of
the guarded representatives. -/
theorem generated_iff_representatives :
    (∀ {X D : τ} (f : Obj X ⟶ Obj D), Generated T f) ↔
    (∀ {X D : τ} {r : Region Φ} (hr : ValueBranches [X] r [D]), Generated T (Lit hr)) :=
  TriplingGeneration.generated_iff_representatives pe

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
