module

public import Silmaril.SSA.Peggy.Bridge.Theta.Defs
public import Silmaril.SSA.Peggy.Bridge.IR.Canonical
import Silmaril.Proofs.SSA.Peggy.Bridge.Theta.Naturality
import Silmaril.Proofs.SSA.Peggy.Bridge.Theta.Satisfaction

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Theta

open CategoryTheory
open Silmaril.Inst (Comorphism Institution Plain)
open Silmaril.Logic.Institution (Corridor)
open PEG.Bridge.Theta.Region.Relabel (opcode)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S T U : Signature Data}

theorem Side.map_id {carried : List (PEG.Ty Data)} (s : Side S carried) :
    s.map (𝟙 S) = s :=
  Proofs.side_id s

theorem Side.map_comp {carried : List (PEG.Ty Data)} (f : S ⟶ T) (g : T ⟶ U) (s : Side S carried) :
    s.map (f ≫ g) = (s.map f).map g :=
  Proofs.side_comp f g s

theorem Equation.map_id (e : Equation S) : e.map (𝟙 S) = e := Proofs.map_id e

theorem Equation.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Equation S) :
    e.map (f ≫ g) = (e.map f).map g := Proofs.map_comp f g e

theorem Equation.holds_map (f : S ⟶ T) (e : Equation S) (m : Model T) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) := Proofs.holds_map f e m

/-- The restricted model presentation reduces along the actual opcode map
of the numbered θ institution. -/
theorem theta_reduct (f : S ⟶ T) (m : Model T) :
    RVSDG.Institution.reduct (opcode (opMap f)) (thetaModel m) = thetaModel (reduct f m) :=
  Proofs.theta_reduct f m

/-- The sign-indexed θ sentence map preserves the compiled equation,
including the numbering, carried ports and both bodies. -/
theorem Equation.translate_map (f : S ⟶ T) (e : Equation S) :
    (e.map f).translate = e.translate.map (opcode (opMap f)) := rfl

theorem Equation.satisfaction (e : Equation S) (m : Model S) :
    e.translate.Holds (thetaModel m) ↔ e.Holds m :=
  Proofs.satisfaction m e

/-- Checked PEG equations with the total, marked-negation model family. -/
def pegPlain (Data : Type) : Plain.{1,0,0,1} (Signature Data) where
  Sen := Equation
  map f e := e.map f
  map_id _ e := e.map_id
  map_comp f g e := e.map_comp f g
  Mod := Model
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.Holds m
  sat_map f m e := e.holds_map f m

/-- Pull back the existing numbered θ institution along the generated
signature functor. -/
abbrev canonicalTheta (Data : Type) :=
  Institution.ofFunctor (thetaSignature Data ⋙
    (RVSDG.Theta.Institution.inst.{0,0,0} (PEG.Ty Data) PUnit).I)

/-- The canonical θ sentences and satisfaction in the induced model family. -/
def thetaPlain (Data : Type) : Plain.{1,0,0,1} (Signature Data) where
  Sen S := ((canonicalTheta Data).I.obj S).Sen
  map f := ((canonicalTheta Data).I.map f).sen
  map_id S e := congrFun (congrArg Corridor.sen ((canonicalTheta Data).I.map_id S)) e
  map_comp f g e := congrFun (congrArg Corridor.sen ((canonicalTheta Data).I.map_comp f g)) e
  Mod := Model
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.Holds (thetaModel m)
  sat_map f m e :=
    (RVSDG.Theta.Institution.Equation.satisfaction (opcode (opMap f)) e (thetaModel m)).trans
      (Iff.of_eq (congrArg e.Holds (theta_reduct f m)))

/-- The restriction is implemented by a corridor that sends each marked
model to its actual numbered θ interpretation. -/
def restrictThetaModels (Data : Type) :
    Comorphism (canonicalTheta Data) (IR.mathlibDiscrete (thetaPlain Data)) :=
  Comorphism.ofTranslationId (Sign := Signature Data) (I := (canonicalTheta Data).I)
    (J := (IR.mathlibDiscrete (thetaPlain Data)).I) (fun _ e => e)
    (fun S => Discrete.functor (fun m : Model S => Discrete.mk (thetaModel m)))
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun {_ T} f => CategoryTheory.Functor.ext (fun (m : Discrete (Model T)) =>
      congrArg Discrete.mk (theta_reduct f m.as)))

def peggyToThetaPlain (Data : Type) : Comorphism (pegPlain Data).toInst (thetaPlain Data).toInst :=
  Comorphism.ofPlain (P := pegPlain Data) (Q := thetaPlain Data) (𝟭 _)
    (fun _ e => e.translate) (fun _ m => m)
    (fun _ m e => e.satisfaction m)
    (fun f e => e.translate_map f) (fun _ _ => rfl)

/-- The bundled comorphism on the marked signature family, using discrete
model categories on both sides. The source model is the total PEG model
presenting the target interpretation. -/
def peggyToTheta (Data : Type) :
    Comorphism (IR.mathlibDiscrete (pegPlain Data)) (IR.mathlibDiscrete (thetaPlain Data)) :=
  IR.mathlibDiscreteComorphism (peggyToThetaPlain Data)

end Silmaril.SSA.Peggy.Bridge.Theta
