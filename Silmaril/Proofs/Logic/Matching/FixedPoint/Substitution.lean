module

public import Silmaril.Proofs.Logic.Matching.FixedPoint.Variables

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

theorem Pattern.denote_substituteSets (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Q : Fin l → S} (σ : ∀ i, Pattern A Q Γ (P i))
      (v : ObjEnv A M Γ) (η : SetEnv A M Q),
      (p.substituteSets σ).denote M v η = p.denote M v (fun i => (σ i).denote M v η) := by
  induction p with
  | base => intro l Q σ v η; rfl
  | setvar => intro l Q σ v η; rfl
  | app op args ih =>
      intro l Q σ v η
      change application M op (fun i => (substituteSets (args i) σ).denote M v η) = _
      simp only [ih]
      rfl
  | dualApp op args ih =>
      intro l Q σ v η
      change dualApplication M op (fun i => (substituteSets (args i) σ).denote M v η) = _
      simp only [ih]
      rfl
  | conj p q hp hq =>
      intro l Q σ v η
      exact congrArg₂ Set.inter (hp σ v η) (hq σ v η)
  | disj p q hp hq =>
      intro l Q σ v η
      exact congrArg₂ Set.union (hp σ v η) (hq σ v η)
  | ex bound p hp =>
      intro l Q σ v η
      change {x | ∃ a : M.carrier bound,
        x ∈ (p.substituteSets (fun i => (σ i).renameObjects (Ren.shift _ bound))).denote M (Fin.cases a v) η} = _
      simp only [hp, Pattern.denote_renameObjects]
      rfl
  | all bound p hp =>
      intro l Q σ v η
      change {x | ∀ a : M.carrier bound,
        x ∈ (p.substituteSets (fun i => (σ i).renameObjects (Ren.shift _ bound))).denote M (Fin.cases a v) η} = _
      simp only [hp, Pattern.denote_renameObjects]
      rfl
  | @mu r k P' Γ p hp =>
      show ∀ {l} {Q : Fin l → S} (σ : ∀ i, Pattern A Q Γ ((P' ∘ Fin.succ) i)) v η,
        ((Pattern.mu p).substituteSets σ).denote M v η =
          (Pattern.mu p).denote M v (fun i => (σ i).denote M v η)
      intro l Q σ v η
      apply congrArg OrderHom.lfp
      apply OrderHom.ext
      funext X
      let σ' : ∀ i, Pattern A (Fin.cases (P' 0) Q) Γ (P' i) :=
        Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0)))
      change (p.substituteSets σ').denote M v (Fin.cases X η) = _
      have he : (fun i => (σ' i).denote M v (Fin.cases X η)) =
          Fin.cases X (fun i => (σ i).denote M v η) := by
        funext i
        refine Fin.cases rfl ?_ i
        intro j
        exact (σ j).denote_renameSets M (Ren.shift Q (P' 0)) v (Fin.cases X η)
      exact (hp σ' v (Fin.cases X η)).trans (congrArg (fun env => p.denote M v env) he)
  | @nu r k P' Γ p hp =>
      show ∀ {l} {Q : Fin l → S} (σ : ∀ i, Pattern A Q Γ ((P' ∘ Fin.succ) i)) v η,
        ((Pattern.nu p).substituteSets σ).denote M v η =
          (Pattern.nu p).denote M v (fun i => (σ i).denote M v η)
      intro l Q σ v η
      apply congrArg OrderHom.gfp
      apply OrderHom.ext
      funext X
      let σ' : ∀ i, Pattern A (Fin.cases (P' 0) Q) Γ (P' i) :=
        Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0)))
      change (p.substituteSets σ').denote M v (Fin.cases X η) = _
      have he : (fun i => (σ' i).denote M v (Fin.cases X η)) =
          Fin.cases X (fun i => (σ i).denote M v η) := by
        funext i
        refine Fin.cases rfl ?_ i
        intro j
        exact (σ j).denote_renameSets M (Ren.shift Q (P' 0)) v (Fin.cases X η)
      exact (hp σ' v (Fin.cases X η)).trans (congrArg (fun env => p.denote M v env) he)

/-- Simultaneously substituting the variables themselves has the identity meaning. -/
theorem Pattern.denote_substituteSets_id (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s)
    (v : ObjEnv A M Γ) (η : SetEnv A M P) :
    (p.substituteSets (fun i => .setvar i)).denote M v η = p.denote M v η :=
  p.denote_substituteSets M _ v η

/-- Substitution composition is semantic composition, through both sorts of binder. -/
theorem Pattern.denote_substituteSets_comp (M : Model A) {r l m k : Nat}
    {P : Fin r → S} {Q : Fin l → S} {R : Fin m → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Γ (P i)) (τ : ∀ j, Pattern A R Γ (Q j))
    (v : ObjEnv A M Γ) (η : SetEnv A M R) :
    ((p.substituteSets σ).substituteSets τ).denote M v η =
      (p.substituteSets (fun i => (σ i).substituteSets τ)).denote M v η := by
  simp only [Pattern.denote_substituteSets]

end Silmaril.Logic.Matching.FixedPoint
