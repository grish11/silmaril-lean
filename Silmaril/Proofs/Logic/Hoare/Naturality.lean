module

public import Silmaril.Logic.Hoare.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare
open CategoryTheory Silmaril.Logic.Institution
variable {C : Type} {A B : Signature C}

theorem body_reduct (f : A ⟶ B) (M : Model C B) (c : C) (w v : M.World) :
    (A.body c).Rel (ModalMu.reduct f.language M) w v ↔ (B.body c).Rel M w v := by
  rw [← PDL.Program.rel_map, f.body]

theorem phaseStep_reduct (f : A ⟶ B) (M : Model C B) :
    phaseStep C (ModalMu.reduct f.language M) = phaseStep C M := by
  have he (c : C) : (A.body c).Rel (ModalMu.reduct f.language M) = (B.body c).Rel M :=
    funext fun w => funext fun v => propext (body_reduct f M c w v)
  funext x y
  apply propext
  simp only [phaseStep, he]
  rfl

theorem expand_reduct (f : A ⟶ B) (M : Model C B) :
    Matching.FirstOrder.SignatureMap.reduct (reachSignaturesMap C f).algebra (expand C M) =
      expand C (ModalMu.reduct f.language M) := by
  have hr : phaseStep C (ModalMu.reduct f.language M) = phaseStep C M := phaseStep_reduct f M
  have hv : (fun a : Label C A => {x : Phase C M.World |
      x.1 = some a.1 ∧ x.2.1 = a.2.1 ∧ (a.2.2.map f.language).Holds M x.2.2}) =
    (fun a : Label C A => {x : Phase C M.World |
      x.1 = some a.1 ∧ x.2.1 = a.2.1 ∧ a.2.2.Holds (ModalMu.reduct f.language M) x.2.2}) := by
    funext a
    apply Set.ext
    intro x
    exact and_congr Iff.rfl (and_congr Iff.rfl (PDL.Formula.holds_map f.language M a.2.2 x.2.2))
  change Matching.FirstOrder.Model.mk _ _ _ = Matching.FirstOrder.Model.mk _ _ _
  congr 1
  funext n inputs output op args
  cases op with
  | atom a => exact congrArg (fun V => V a) hv
  | action a =>
      apply Set.ext
      intro x
      change phaseStep C M x (args 0) ↔ phaseStep C (ModalMu.reduct f.language M) x (args 0)
      rw [hr]

theorem atom_map (f : A ⟶ B) (a : Label C A) :
    (Reachability.atom a).map (reachSignaturesMap C f).algebra = Reachability.atom (labelMap C f a) := by
  change Matching.FirstOrder.Pattern.app (A := (reachSignaturesObj C B).algebra)
    (Matching.FixedPoint.ModalOperation.atom (labelMap C f a)) _ = _
  apply congrArg (Matching.FirstOrder.Pattern.app (A := (reachSignaturesObj C B).algebra)
    (Matching.FixedPoint.ModalOperation.atom (labelMap C f a)))
  funext i
  exact i.elim0

theorem encode_map (f : A ⟶ B) (t : Triple C A) :
    encode C (t.map C f) = (encode C t).map () (reachSignaturesMap C f) := by
  exact congrArg₂ (fun pre post => Reachability.Sentence.mk 0 Fin.elim0 .allPath pre post)
    (atom_map f (t.command, false, t.pre)).symm (atom_map f (t.command, true, t.post)).symm

end Silmaril.Logic.Hoare
