module

public import Silmaril.Logic.PDL.K.Defs

@[expose] public section
namespace Silmaril.Logic.PDL
open CategoryTheory Silmaril.Logic.Institution

 theorem encodeK_holds {S : Modal.Signature} (M : Model (ModalMu.kSignatures.obj S))
    (p : Modal.Formula S) (w : M.World) :
    (encodeK p).Holds M w ↔ p.Holds (ModalMu.forgetK M) w := by
  classical
  induction p generalizing w with
  | atom a => rfl
  | bot => rfl
  | imp p q hp hq =>
      change (¬ (encodeK p).Holds M w ∨ (encodeK q).Holds M w) ↔
        (p.Holds (ModalMu.forgetK M) w → q.Holds (ModalMu.forgetK M) w)
      rw [hp, hq]
      tauto
  | box p hp =>
      exact forall_congr' fun v => imp_congr_right fun _ => hp v

theorem encodeK_map {S T : Modal.Signature} (f : S ⟶ T) (p : Modal.Formula S) :
    encodeK (p.map f) = (encodeK p).map (ModalMu.kSignatures.map f) := by
  induction p <;> simp_all [Modal.Formula.map, encodeK, Formula.map] <;> rfl

def kCorridor (S : Modal.Signature) : Modal.institution.obj S ⟶ institution.obj (ModalMu.kSignatures.obj S) where
  sen := encodeK
  mod := ModalMu.kModels S
  sat := fun M p => encodeK_holds M p M.point

def kNatural : Modal.institution ⟶ ModalMu.kSignatures ⋙ institution where
  app := kCorridor
  naturality := by
    intro S T f
    apply Room.hom_ext (funext (encodeK_map f))
    refine Functor.ext (fun _ => rfl) ?_
    intro M N h
    cases h.down
    rfl

def kToPDL : Inst.CoHom ⟨Modal.Signature, Modal.institution⟩ ⟨Signature, institution⟩ :=
  ⟨ModalMu.kSignatures, kNatural⟩

theorem kToPDL_modelExpansive : kToPDL.ModelExpansive := fun _ M => ⟨ModalMu.expandK M, rfl⟩

theorem expandK_sat {S : Modal.Signature} (M : Modal.Model S) (p : Modal.Formula S) :
    Sat (ModalMu.expandK M) (encodeK p) ↔ Modal.Sat M p := encodeK_holds (ModalMu.expandK M) p M.point

end Silmaril.Logic.PDL
