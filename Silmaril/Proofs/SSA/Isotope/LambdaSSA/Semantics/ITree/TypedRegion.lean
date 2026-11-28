module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedTerm
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedLabels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedCfg

/-! # Erasure of exact categorical region denotations in Kleisli models -/

public section

universe v q

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Agreement
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ bind_of caseWithContext_of)
open Monadic (LabelValue)
open Silmaril.Isotope.Semantics (encodeValue)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

local notation "CatArrow" Γ:arg L:arg => Functor.obj J (Categorical.ctxObj T Γ) ⟶ Functor.obj J (Categorical.labelObj T L)

@[expose] noncomputable def encodeCategoricalLabel (L : LCtx (Ty κ)) (x : Categorical.labelObj T L) :
    Transfer (Sigma V) :=
  encodeLabel L ((LabelValue.categoricalEquiv L).symm x)

@[simp] theorem encodeCategoricalLabel_inject {L : LCtx (Ty κ)} {A : Ty κ}
    (i : Nat) (h : At L i A) (a : Ty.denote V A) :
    encodeCategoricalLabel L (Categorical.labelInject T i h a) = (i, Silmaril.Isotope.Semantics.encodeValue V A a) := by
  rw [encodeCategoricalLabel, ← LabelValue.categoricalEquiv_inject, Equiv.symm_apply_apply, encodeLabel_inject]

private noncomputable def readArrow {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)}
    (f : CatArrow Γ L) (ρ : Monadic.Env Γ) : m (LabelValue L) :=
  (show m _ from f.of (envToCategorical ρ)) >>= fun x => pure ((LabelValue.categoricalEquiv L).symm x)

omit [Iterate m] [LawfulElgotMonad m] in
private theorem readArrow_roundtrip {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)}
    (f : CatArrow Γ L) (ρ : Monadic.Env Γ) :
    f.of (envToCategorical ρ) = (readArrow f ρ >>= fun x => pure (LabelValue.categoricalEquiv L x)) := by
  simp only [readArrow, bind_assoc, pure_bind, Equiv.apply_symm_apply, bind_pure]

theorem regionDenotes_erased (badTerm : m (Value (Sigma V))) (badRegion : m (Transfer (Sigma V)))
    (compat : ∀ f (x : Ty.denote V (instrSrc f)), raw f (encodeValue V _ x) =
      (InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := m) f x >>= fun y => pure (encodeValue V _ y)))
    {Γ : VCtx (Ty κ)} {r : Region Φ} {L : LCtx (Ty κ)} {hr : Region.HasType Γ r L}
    {f : CatArrow Γ L} (d : Categorical.RegionDenotes J T hr f)
    (ρ : Monadic.Env Γ) (env : Env (Sigma V)) (h : EncodesEnv ρ env) :
    ((show m _ from f.of (envToCategorical ρ)) >>= fun x => pure (encodeCategoricalLabel L x)) = Erasure.region badTerm badRegion raw env r := by
  induction d generalizing env with
  | br dt =>
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight, bind_assoc, kleisli_map_of, pure_bind, encodeCategoricalLabel_inject,
      Erasure.region, ← termDenotes_erased raw badTerm compat dt ρ env h]
    rfl
  | case de dl dr ihl ihr =>
    rw [caseWithContext_of]
    simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight, bind_assoc, kleisli_map_of, pure_bind,
      Erasure.region, ← termDenotes_erased raw badTerm compat de ρ env h]
    apply bind_congr
    intro ab
    rw [coprod_hom_agrees]
    rcases ab with a | b
    · exact ihl (ρ, a) _ (encodesEnv_extend h a)
    · exact ihr (ρ, b) _ (encodesEnv_extend h b)
  | let₁ da db ih =>
    rw [bind_of]
    simp only [Bind.kleisliRight, bind_assoc, pure_bind,
      Erasure.region, ← termDenotes_erased raw badTerm compat da ρ env h]
    exact bind_congr (fun a => ih (ρ, a) _ (encodesEnv_extend h a))
  | let₂ da db ih =>
    rename_i Γ t A B ha fa r L hb fb
    rw [bind_of]
    simp only [Bind.kleisliRight, bind_assoc, pure_bind,
      Erasure.region, ← termDenotes_erased raw badTerm compat da ρ env h]
    apply bind_congr
    rintro ⟨a, b⟩
    rw [← Category.assoc, ← Functor.map_comp, Kleisli.Type.comp_of_eq_kleisliRight]
    change (((pure (envToCategorical (Γ := B :: A :: Γ) ((ρ, a), b)) : m _) >>= fun z =>
      (show m _ from fb.of z)) >>= _) = _
    rw [pure_bind]
    exact ih ((ρ, a), b) _ (encodesEnv_extend (encodesEnv_extend h a) b)
  | cfgZero he hb de ih =>
    exact (ih ρ env h).trans (by simp [Erasure.region, splitTransfer])
  | cfg he hb de db dc ihe ihb =>
    rename_i n R Γ L entry blocks FE FB FC
    let entryFn := readArrow FE
    let blockFn := fun i => readArrow (FB i)
    let collective : Monadic.Env Γ × Monadic.FiniteLabelDen R → m (LabelValue (List.ofFn R ++ L)) :=
      fun p => blockFn p.2.1 (p.1, p.2.2)
    have direct : Monadic.CollectiveDenotes Γ R L blockFn collective := ⟨fun _ _ _ => rfl⟩
    have dFC := collective_toCategorical direct (fun i ρ => readArrow_roundtrip (FB i) ρ)
    have hFC : FC = collectiveArrow collective :=
      Categorical.collective_ext J T _ _ _ fun i => (dc.restrict i).trans (dFC.restrict i).symm
    rw [hFC]
    rw [congrFun (cfgDenotation_agrees (R := R) (L := L) (fe := entryFn) (FE := FE)
      (funext (readArrow_roundtrip FE)) collective) ρ]
    simp only [bind_assoc, pure_bind, encodeCategoricalLabel, Equiv.symm_apply_apply]
    apply cfgDenotation_erased
    · simpa only [entryFn, readArrow, bind_assoc, pure_bind, encodeCategoricalLabel] using ihe ρ env h
    · rintro ⟨i, a⟩
      simpa only [collective, blockFn, readArrow, bind_assoc, pure_bind, encodeCategoricalLabel, encodeBlock]
        using ihb i (ρ, a) _ (encodesEnv_extend h a)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed
