module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Compiler.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open Silmaril.Logic.Institution.Examples

/-- Structural LFP preservation step. The hypothesis is the induction theorem
for the strictly smaller source body, at all recursive environments. -/
theorem lfp_correct {A : Signature} (M : Model A) {r k l} {P' : Fin (r+1) → Nat}
    {Γ : Fin l → TargetSort} (body : Pattern A P' (P' 0+k))
    (args : Fin (P' 0) → Term A k) (σ : Fin k → TargetTerm A Γ .value)
    (h : TargetTerm A Γ .heap) (η : RelEnv M (P' ∘ Fin.succ))
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ)
    (hbody : ∀ ζ (τ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) (tupleContext (P' 0) Γ)),
      τ ∈ (pattern body (bodyValues (P' 0) σ) (tupleHeap (P' 0) Γ)).denote (model M) (encodeRelEnv M ζ) ↔
      ((fun i => (bodyValues (P' 0) σ i).eval (model M).toStructure.toAlgebra τ),
        (tupleHeap (P' 0) Γ).eval (model M).toStructure.toAlgebra τ) ∈ body.denote M ζ) :
    θ ∈ (pattern (.lfp body args) σ h).denote (model M) (encodeRelEnv M η) ↔
      ((fun i => (σ i).eval (model M).toStructure.toAlgebra θ),
        h.eval (model M).toStructure.toAlgebra θ) ∈ (Pattern.lfp body args).denote M η := by
  let p := pattern body (bodyValues (P' 0) σ) (tupleHeap (P' 0) Γ)
  let ρ : Tuple M k := fun i => (σ i).eval (model M).toStructure.toAlgebra θ
  let F := bodyOperator M body η ρ
  let G := Silmaril.Logic.FirstOrderLFP.bodyOperator (model M) p (encodeRelEnv M η) θ
  have ht : tupleContext (P' 0) Γ ∘ Fin.castAdd l = (profile A (P' 0)).sorts := by
    funext i
    simp [tupleContext]
  have hp : tupleContext (P' 0) Γ ∘ Fin.natAdd (P' 0+1) = Γ := by
    funext i
    simp [tupleContext]
  have hc : ∀ Y y, y ∈ G Y ↔ (stateEquiv M (P' 0)).symm y ∈
      F {s | stateEquiv M (P' 0) s ∈ Y} := by
    intro Y y
    obtain ⟨τ,hτ,_⟩ := Silmaril.Logic.FirstOrderLFP.extends_exists_unique (model M) ht hp y θ
    change y ∈ Silmaril.Logic.FirstOrderLFP.bodyOperator (model M) p (encodeRelEnv M η) θ Y ↔ _
    rw [Silmaril.Logic.FirstOrderLFP.bodyOperator_iff (model M) ht hp p (encodeRelEnv M η) θ Y y τ hτ]
    rw [← insert_encode M P' η Y]
    rw [hbody]
    rw [eval_bodyValues M σ τ y θ hτ,eval_tupleHeap M τ y θ hτ]
    rfl
  have hf : G.lfp = {y | decodeState M y ∈ F.lfp} :=
    lfp_conjugate (stateEquiv M (P' 0)) F G hc
  change (fun j => (recursiveArgs h (fun j => term σ (args j)) j).eval
      (model M).toStructure.toAlgebra θ) ∈ G.lfp ↔
    ((fun j => (args j).eval M ρ),h.eval (model M).toStructure.toAlgebra θ) ∈ F.lfp
  rw [hf]
  change (decodeState M (fun j => (recursiveArgs h (fun j => term σ (args j)) j).eval
      (model M).toStructure.toAlgebra θ)) ∈ F.lfp ↔ _
  simp only [decodeState,recursiveArgs,Fin.cases_zero,Fin.cases_succ,eval_term]
  rfl

/-- Exact recursive semantic comparison on arbitrary resource models and
object contexts; positive recursion uses full powerset least fixed points. -/
theorem pattern_correct {A : Signature} (M : Model A) {r k} {P : Fin r → Nat}
    (p : Pattern A P k) (η : RelEnv M P) {l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value) (h : TargetTerm A Γ .heap)
    (θ : Silmaril.Logic.FirstOrderLFP.ObjEnv (model M) Γ) :
    θ ∈ (pattern p σ h).denote (model M) (encodeRelEnv M η) ↔
      ((fun i => (σ i).eval (model M).toStructure.toAlgebra θ),
        h.eval (model M).toStructure.toAlgebra θ) ∈ p.denote M η := by
  induction p generalizing l with
  | base p => exact assertion_correct M p σ h θ
  | pred i args =>
      change decodeState M (fun j => (recursiveArgs h (fun j => term σ (args j)) j).eval
        (model M).toStructure.toAlgebra θ) ∈ η i ↔ _
      simp only [decodeState,recursiveArgs,Fin.cases_zero,Fin.cases_succ,eval_term]
      rfl
  | conj p q hp hq =>
      change (θ ∈ (pattern p σ h).denote (model M) (encodeRelEnv M η) ∧
        θ ∈ (pattern q σ h).denote (model M) (encodeRelEnv M η)) ↔ _
      exact and_congr (hp η σ h θ) (hq η σ h θ)
  | disj p q hp hq =>
      change (θ ∈ (pattern p σ h).denote (model M) (encodeRelEnv M η) ∨
        θ ∈ (pattern q σ h).denote (model M) (encodeRelEnv M η)) ↔ _
      exact or_congr (hp η σ h θ) (hq η σ h θ)
  | sep p q hp hq =>
      let σ' := fun i => liftHeap (liftHeap (σ i))
      let θ' := fun a b => extendEnv (model M).toStructure .heap b
        (extendEnv (model M).toStructure .heap a θ)
      change (∃ a b, (joinFormula (.var 1) (.var 0) (liftHeap (liftHeap h))).Holds
          (model M).toStructure (θ' a b) ∧
        θ' a b ∈ (pattern p σ' (.var 1)).denote (model M) (encodeRelEnv M η) ∧
        θ' a b ∈ (pattern q σ' (.var 0)).denote (model M) (encodeRelEnv M η)) ↔ _
      simp only [holds_joinFormula,hp,hq,σ',θ',eval_liftHeap,EQ.Term.eval]
      rfl
  | wand p q hq =>
      classical
      let σ' := fun i => liftHeap (liftHeap (σ i))
      let θ' := fun a b => extendEnv (model M).toStructure .heap b
        (extendEnv (model M).toStructure .heap a θ)
      change (∀ a b, (¬ ((joinFormula (liftHeap (liftHeap h)) (.var 1) (.var 0)).Holds
          (model M).toStructure (θ' a b) ∧
          (assertion p σ' (.var 1)).Holds (model M).toStructure (θ' a b))) ∨
        θ' a b ∈ (pattern q σ' (.var 0)).denote (model M) (encodeRelEnv M η)) ↔ _
      simp only [holds_joinFormula,assertion_correct,hq,σ',θ',eval_liftHeap,EQ.Term.eval,
        or_iff_not_imp_left,not_not,and_imp]
      rfl
  | ex p ih =>
      change (∃ x, extendEnv (model M).toStructure .value x θ ∈
        (pattern p (boundValues σ) (liftTerm (S := (signature A).toSignature) TargetSort.value h)).denote
          (model M) (encodeRelEnv M η)) ↔ _
      simp only [ih,eval_liftValue,eval_boundValues]
      rfl
  | all p ih =>
      change (∀ x, extendEnv (model M).toStructure .value x θ ∈
        (pattern p (boundValues σ) (liftTerm (S := (signature A).toSignature) TargetSort.value h)).denote
          (model M) (encodeRelEnv M η)) ↔ _
      simp only [ih,eval_liftValue,eval_boundValues]
      rfl
  | lfp body args ih =>
      exact lfp_correct M body args σ h η θ (fun ζ τ => ih ζ _ _ τ)

end Silmaril.Logic.Separation.Parameterized.FirstOrder
