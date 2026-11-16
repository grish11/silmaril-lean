module

public import Silmaril.Logic.Matching.FixedPoint.Modal.Defs
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {L K : ModalMu.Signature}

theorem application_atom (M : Model (modalSignature L)) (a : L.Atom) :
    application M (.atom a) (fun i => i.elim0) = M.operation (.atom a) (fun i => i.elim0) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨v, _, hv⟩
    have he : v = (fun i => i.elim0) := funext fun i => i.elim0
    exact he ▸ hv
  · intro h
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), h⟩

theorem application_action (M : Model (modalSignature L)) (a : L.Action)
    (X : Set (M.carrier ())) :
    application M (.action a) ![X] =
      {w | ∃ v, w ∈ M.operation (.action a) ![v] ∧ v ∈ X} := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨v, hv, ho⟩
    have he : v = ![v 0] := by funext i; fin_cases i; rfl
    exact ⟨v 0, he ▸ ho, hv 0⟩
  · rintro ⟨v, ho, hv⟩
    exact ⟨![v], (fun i => by fin_cases i; exact hv), ho⟩

theorem dualApplication_action (M : Model (modalSignature L)) (a : L.Action)
    (X : Set (M.carrier ())) :
    dualApplication M (.action a) ![X] =
      {w | ∀ v, w ∈ M.operation (.action a) ![v] → v ∈ X} := by
  classical
  have he : (fun i : Fin 1 => (![X] i)ᶜ) = ![Xᶜ] := by funext i; fin_cases i; rfl
  unfold dualApplication
  rw [he, application_action]
  apply Set.ext
  intro w
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and, not_not]

theorem encodeModal_denote (M : PointedModel () (modalSignature L)) {n : Nat}
    (p : ModalMu.Formula L n) :
    (encodeModal p).denote M.base (fun i => i.elim0) = p.denote (forgetModal M) := by
  induction p with
  | pos a =>
      apply OrderHom.ext
      funext η
      change application M.base (.atom a) _ = _
      exact (congrArg (application M.base (.atom a)) (funext fun i => i.elim0)).trans
        (application_atom M.base a)
  | neg a =>
      apply OrderHom.ext
      funext η
      change (application M.base (.atom a) _)ᶜ = _
      apply congrArg (fun X => Xᶜ)
      exact (congrArg (application M.base (.atom a)) (funext fun i => i.elim0)).trans
        (application_atom M.base a)
  | bot =>
      apply OrderHom.ext
      funext η
      exact FirstOrder.Model.denote_bottom M.base _
  | top =>
      apply OrderHom.ext
      funext η
      exact FirstOrder.Model.denote_top M.base _
  | var i => rfl
  | conj p q hp hq =>
      apply OrderHom.ext
      funext η
      change (encodeModal p).denote M.base _ η ∩ (encodeModal q).denote M.base _ η = _
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      apply OrderHom.ext
      funext η
      change (encodeModal p).denote M.base _ η ∪ (encodeModal q).denote M.base _ η = _
      rw [hp, hq]
      rfl
  | diamond a p hp =>
      show (encodeModal (ModalMu.Formula.diamond a p)).denote M.base (fun i => i.elim0) =
        (ModalMu.Formula.diamond a p).denote (forgetModal M)
      apply OrderHom.ext
      funext η
      change application M.base (.action a)
        (fun i => (![encodeModal p] i).denote M.base (fun i => i.elim0) η) = _
      have he : (fun i => (![encodeModal p] i).denote M.base (fun i => i.elim0) η) =
          ![(encodeModal p).denote M.base (fun i => i.elim0) η] := by
        funext i; fin_cases i; rfl
      rw [he]
      rw [hp, application_action]
      rfl
  | box a p hp =>
      show (encodeModal (ModalMu.Formula.box a p)).denote M.base (fun i => i.elim0) =
        (ModalMu.Formula.box a p).denote (forgetModal M)
      apply OrderHom.ext
      funext η
      change dualApplication M.base (.action a)
        (fun i => (![encodeModal p] i).denote M.base (fun i => i.elim0) η) = _
      have he : (fun i => (![encodeModal p] i).denote M.base (fun i => i.elim0) η) =
          ![(encodeModal p).denote M.base (fun i => i.elim0) η] := by
        funext i; fin_cases i; rfl
      rw [he]
      rw [hp, dualApplication_action]
      rfl
  | mu p hp =>
      apply OrderHom.ext
      funext η
      change (((encodeModal p).denote M.base _).comp (insert _ M.base η)).lfp = _
      rw [hp]
      rfl
  | nu p hp =>
      apply OrderHom.ext
      funext η
      change (((encodeModal p).denote M.base _).comp (insert _ M.base η)).gfp = _
      rw [hp]
      rfl

theorem encodeModal_map (f : L ⟶ K) {n : Nat} (p : ModalMu.Formula L n) :
    encodeModal (p.map f) = (encodeModal p).map (modalSignatureMap f) := by
  induction p with
  | pos a =>
      apply congrArg (Pattern.app (A := modalSignature K) (.atom (f.atom a)))
      funext i
      exact i.elim0
  | neg a =>
      apply congrArg (Pattern.dualApp (A := modalSignature K) (.atom (f.atom a)))
      funext i
      exact i.elim0
  | bot => rfl
  | top => rfl
  | var => rfl
  | conj p q hp hq => exact congrArg₂ Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ Pattern.disj hp hq
  | diamond a p hp => exact congrArg (Pattern.app (A := modalSignature K) (ModalOperation.action (f.action a))) (by funext i; fin_cases i; exact hp)
  | box a p hp => exact congrArg (Pattern.dualApp (A := modalSignature K) (ModalOperation.action (f.action a))) (by funext i; fin_cases i; exact hp)
  | mu p hp => exact congrArg Pattern.mu hp
  | nu p hp => exact congrArg Pattern.nu hp

def modalCorridor (L : ModalMu.Signature) :
    ModalMu.institution.obj L ⟶ (pointedInstitution ()).obj (modalSignature L) where
  sen := encodeModal
  mod := modalModels L
  sat := by
    intro M p
    change M.point ∈ (encodeModal p).denote M.base _ _ ↔ _
    exact Set.ext_iff.mp (congrArg (fun F => F (fun i => i.elim0)) (encodeModal_denote M p)) M.point

def modalNatural : ModalMu.institution ⟶ modalSignatures ⋙ pointedInstitution () where
  app := modalCorridor
  naturality := by
    intro L K f
    apply Room.hom_ext (funext (encodeModal_map f))
    exact rfl

def modalToMatching : Inst.CoHom ⟨ModalMu.Signature, ModalMu.institution⟩
    ⟨Signature Unit, pointedInstitution ()⟩ := ⟨modalSignatures, modalNatural⟩

theorem forget_expandModal (M : ModalMu.Model L) : forgetModal (expandModal M) = M := by
  cases M
  rfl

theorem modalToMatching_modelExpansive : modalToMatching.ModelExpansive :=
  fun _ M => ⟨expandModal M, forget_expandModal M⟩

theorem modal_entails_iff (L : ModalMu.Signature) (H : Set (ModalMu.Formula L 0))
    (p : ModalMu.Formula L 0) :
    (ModalMu.institution.obj L).Entails H p ↔
      ((pointedInstitution ()).obj (modalSignature L)).Entails (encodeModal '' H) (encodeModal p) :=
  modalToMatching.entails_iff modalToMatching_modelExpansive L H p

end Silmaril.Logic.Matching.FixedPoint
