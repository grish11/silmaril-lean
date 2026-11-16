module

public import Silmaril.Logic.ModalMu.K.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory Silmaril.Logic.Institution

theorem encodeK_holds {S : Modal.Signature} (M : Model (kSignatures.obj S))
    (p : Modal.Formula S) (w : M.World) (b : Bool) :
    w ∈ (encodeK b p).denote M emptyEnv ↔
      if b then ¬ p.Holds (forgetK M) w else p.Holds (forgetK M) w := by
  classical
  induction p generalizing w b with
  | atom a => cases b <;> rfl
  | bot =>
      cases b
      · rfl
      · change True ↔ ¬ False
        tauto
  | imp p q hp hq =>
      show w ∈ (encodeK b (.imp p q)).denote M emptyEnv ↔
        if b then ¬ (p.Holds (forgetK M) w → q.Holds (forgetK M) w)
        else (p.Holds (forgetK M) w → q.Holds (forgetK M) w)
      cases b
      · change (w ∈ (encodeK true p).denote M emptyEnv ∨
          w ∈ (encodeK false q).denote M emptyEnv) ↔
          (p.Holds (forgetK M) w → q.Holds (forgetK M) w)
        rw [hp, hq]
        tauto
      · change (w ∈ (encodeK false p).denote M emptyEnv ∧
          w ∈ (encodeK true q).denote M emptyEnv) ↔
          ¬ (p.Holds (forgetK M) w → q.Holds (forgetK M) w)
        rw [hp, hq]
        tauto
  | box p hp =>
      show w ∈ (encodeK b (.box p)).denote M emptyEnv ↔
        if b then ¬ (∀ v, M.step () w v → p.Holds (forgetK M) v)
        else (∀ v, M.step () w v → p.Holds (forgetK M) v)
      cases b
      · change (∀ v, M.step () w v → v ∈ (encodeK false p).denote M emptyEnv) ↔
          (∀ v, M.step () w v → p.Holds (forgetK M) v)
        simp_rw [hp]
        rfl
      · change (∃ v, M.step () w v ∧ v ∈ (encodeK true p).denote M emptyEnv) ↔
          ¬ (∀ v, M.step () w v → p.Holds (forgetK M) v)
        simp_rw [hp]
        simp only [↓reduceIte, not_forall, exists_prop]

theorem encodeK_map {S T : Modal.Signature} (f : S ⟶ T) (p : Modal.Formula S)
    (b : Bool) : encodeK b (p.map f) = (encodeK b p).map (kSignatures.map f) := by
  induction p generalizing b <;> cases b <;> simp_all [encodeK, Modal.Formula.map, Formula.map] <;> rfl

/-- Every K model has a concrete expansion with the identical reduct. -/
theorem forget_expandK {S : Modal.Signature} (M : Modal.Model S) : forgetK (expandK M) = M := rfl

def kCorridor (S : Modal.Signature) : Modal.institution.obj S ⟶ institution.obj (kSignatures.obj S) where
  sen := encodeK false
  mod := kModels S
  sat := fun M p => encodeK_holds M p M.point false

/-- Signature-natural satisfaction preservation, rather than only a graph label. -/
def kNatural : Modal.institution ⟶ kSignatures ⋙ institution where
  app := kCorridor
  naturality := by
    intro S T f
    apply Room.hom_ext (funext fun p => encodeK_map f p false)
    refine Functor.ext (fun _ => rfl) ?_
    intro M N h
    cases h.down
    rfl

def kToMu : Inst.CoHom ⟨Modal.Signature, Modal.institution⟩ ⟨Signature, institution⟩ :=
  ⟨kSignatures, kNatural⟩

/-- Surjectivity on actual model objects supplies model-expansiveness. -/
theorem kToMu_modelExpansive : kToMu.ModelExpansive :=
  fun _ M => ⟨expandK M, rfl⟩

theorem expandK_sat {S : Modal.Signature} (M : Modal.Model S) (p : Modal.Formula S) :
    Sat (expandK M) (encodeK false p) ↔ Modal.Sat M p :=
  encodeK_holds (expandK M) p M.point false

end Silmaril.Logic.ModalMu
