module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedRegion
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedLabels

/-! # Typing coherence via injective encoding of typed exits -/

public section

universe v q

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Agreement
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)

variable {κ : Type v} [AtomValues κ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel

variable [InstructionModel Φ (Ty κ) Bool m]
  (raw : Erasure.Primitive m Φ (Sigma (AtomValues.carrier (κ := κ))))

local notation "V" => AtomValues.carrier (κ := κ)
local notation "J" => typeJ (m := m)
local notation "T" => Categorical.ofMonadicTypeModel (τ := Ty κ)

local instance : LetIter.Semantics.Categorical.InstructionModel J T Φ :=
  LambdaSSA.Semantics.Categorical.ofMonadicInstructionModel (τ := Ty κ) (ε := Bool) (m := m)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [Iterate m] [LawfulElgotMonad m] in
private theorem encode_bind_injective {A B : Type v} (f : A → B)
    (hf : Function.Injective f) (a b : m A)
    (eq : (a >>= fun x => pure (f x)) = (b >>= fun x => pure (f x))) : a = b := by
  classical
  let decode (y : B) : m A := if h : ∃ x, f x = y then pure h.choose else a
  have retract (x : A) : decode (f x) = pure x := by
    unfold decode
    have hex : ∃ z, f z = f x := ⟨x, rfl⟩
    rw [dite_eq_left hex, hf hex.choose_spec]
  simpa only [bind_assoc, pure_bind, retract, bind_pure] using congrArg (· >>= decode) eq

private theorem encodesEnv_exists {Γ : VCtx (Ty κ)} (ρ : Monadic.Env Γ) :
    ∃ env, EncodesEnv ρ env := by
  classical
  let env : Env (Sigma V) := fun i =>
    if h : ∃ A, At Γ i A then encodeValue V h.choose (Monadic.Env.get ρ i h.choose_spec) else .unit
  refine ⟨env, ?_⟩
  intro i A hi
  have hex : ∃ A, At Γ i A := ⟨A, hi⟩
  have he : hex.choose = A := Option.some.inj (hex.choose_spec.symm.trans hi)
  unfold env
  rw [dite_eq_left hex]
  cases he
  rfl

private theorem envTo_from {Γ : VCtx (Ty κ)} (γ : Categorical.ctxObj T Γ) :
    envToCategorical (envFromCategorical γ) = γ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih =>
    simp only [envToCategorical, envFromCategorical, ih]
    rfl

theorem coherence_of_erasure (badTerm : m (Value (Sigma V))) (badRegion : m (Transfer (Sigma V)))
    (compat : ∀ f (x : Ty.denote V (instrSrc f)), raw f (encodeValue V _ x) =
      (InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := m) f x >>= fun y => pure (encodeValue V _ y))) :
    Categorical.RegionTypingCoherent (Φ := Φ) J T := by
  constructor
  intro Γ r L hr f g df dg
  apply Kleisli.hom_ext
  apply ConcreteCategory.hom_ext
  intro γ
  obtain ⟨env, h⟩ := encodesEnv_exists (envFromCategorical γ)
  have eq := (regionDenotes_erased raw badTerm badRegion compat df _ env h).trans (regionDenotes_erased raw badTerm badRegion compat dg _ env h).symm
  rw [envTo_from] at eq
  exact encode_bind_injective (m := m) (encodeCategoricalLabel L)
    ((encodeLabel_injective L).comp (Monadic.LabelValue.categoricalEquiv L).symm.injective) _ _ eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed
