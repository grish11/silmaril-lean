module

public import Silmaril.Proofs.Logic.CTL.FixedPoint

@[expose] public section
namespace Silmaril.Logic.CTL
open CategoryTheory Silmaril.Logic.Institution

/-- Capture-safe translation agrees with CTL's independent path semantics. -/
theorem Formula.toMu_correct {S : Signature} (M : ModalMu.Model (muSignatures.obj S)) (p : Formula S) :
    ∀ w, w ∈ p.toMu.denote M ModalMu.emptyEnv ↔ p.Holds (forgetMu M) w := by
  classical
  induction p with
  | atom => intro w; rfl
  | bot => intro w; rfl
  | neg p hp =>
      show ∀ w, w ∈ (Formula.neg p).toMu.denote M ModalMu.emptyEnv ↔
        (Formula.neg p).Holds (forgetMu M) w
      intro w
      have he : (fun i : Fin 0 => (ModalMu.emptyEnv (W := M.World) i)ᶜ) = ModalMu.emptyEnv :=
        funext fun i => i.elim0
      have hd : p.toMu.dual.denote M ModalMu.emptyEnv = (p.toMu.denote M ModalMu.emptyEnv)ᶜ := by
        simpa only [he] using p.toMu.denote_dual M ModalMu.emptyEnv
      change w ∈ p.toMu.dual.denote M ModalMu.emptyEnv ↔ _
      rw [hd]
      exact not_congr (hp w)
  | conj p q hp hq => intro w; exact and_congr (hp w) (hq w)
  | ex p hp =>
      intro w
      change (∃ v, M.step () w v ∧ v ∈ p.toMu.denote M ModalMu.emptyEnv) ↔ _
      exact exists_congr fun v => and_congr Iff.rfl (hp v)
  | eu p q hp hq =>
      intro w
      let F := ModalMu.bodyMap M (.disj q.toMu.shift (.conj p.toMu.shift (.diamond () (.var 0)))) ModalMu.emptyEnv
      apply (until_iff_lfp (M.step ()) (p.Holds (forgetMu M)) (q.Holds (forgetMu M)) F ?_ w).symm
      intro X x
      change (x ∈ q.toMu.shift.denote M (ModalMu.extend ModalMu.emptyEnv X) ∨
        (x ∈ p.toMu.shift.denote M (ModalMu.extend ModalMu.emptyEnv X) ∧ ∃ v, M.step () x v ∧ v ∈ X)) ↔ _
      rw [ModalMu.Formula.denote_shift, ModalMu.Formula.denote_shift, hp, hq]
  | eg p hp =>
      intro w
      let F := ModalMu.bodyMap M (.conj p.toMu.shift (.diamond () (.var 0))) ModalMu.emptyEnv
      apply (globally_iff_gfp (M.step ()) (p.Holds (forgetMu M)) F ?_ w).symm
      intro X x
      change (x ∈ p.toMu.shift.denote M (ModalMu.extend ModalMu.emptyEnv X) ∧ ∃ v, M.step () x v ∧ v ∈ X) ↔ _
      rw [ModalMu.Formula.denote_shift, hp]

theorem Formula.toMu_map {S T : Signature} (f : S ⟶ T) (p : Formula S) :
    (p.map f).toMu = p.toMu.map (muSignatures.map f) := by
  induction p with
  | atom => rfl
  | bot => rfl
  | neg p hp =>
      change (p.map f).toMu.dual = _
      rw [hp, ModalMu.Formula.dual_map]
      rfl
  | conj p q hp hq => exact congrArg₂ ModalMu.Formula.conj hp hq
  | ex p hp => exact congrArg (ModalMu.Formula.diamond ()) hp
  | eu p q hp hq =>
      simp only [Formula.map, Formula.toMu, ModalMu.Formula.map, hp, hq,
        ModalMu.Formula.shift, ModalMu.Formula.renameVars_map]
      rfl
  | eg p hp =>
      simp only [Formula.map, Formula.toMu, ModalMu.Formula.map, hp,
        ModalMu.Formula.shift, ModalMu.Formula.renameVars_map]
      rfl

def muCorridor (S : Signature) : institution.obj S ⟶ ModalMu.institution.obj (muSignatures.obj S) where
  sen := Formula.toMu
  mod := muModels S
  sat := fun M p => p.toMu_correct M M.point

def muNatural : institution ⟶ muSignatures ⋙ ModalMu.institution where
  app := muCorridor
  naturality := by
    intro S T f
    apply Room.hom_ext (funext (Formula.toMu_map f))
    rfl

def ctlToMu : Inst.CoHom ⟨Signature, institution⟩ ⟨ModalMu.Signature, ModalMu.institution⟩ :=
  ⟨muSignatures, muNatural⟩

theorem forget_expandMu {S : Signature} (M : Model S) : forgetMu (expandMu M) = M := by
  cases M with | mk M => cases M; rfl

theorem ctlToMu_modelExpansive : ctlToMu.ModelExpansive :=
  fun _ M => ⟨expandMu M, forget_expandMu M⟩

theorem mu_entails_iff (S : Signature) (H : Set (Formula S)) (p : Formula S) :
    (institution.obj S).Entails H p ↔
      (ModalMu.institution.obj (muSignatures.obj S)).Entails (Formula.toMu '' H) p.toMu :=
  ctlToMu.entails_iff ctlToMu_modelExpansive S H p

end Silmaril.Logic.CTL
