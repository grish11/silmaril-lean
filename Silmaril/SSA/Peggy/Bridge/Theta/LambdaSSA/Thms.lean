module

public import Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Defs
import Silmaril.Proofs.SSA.Peggy.Bridge.Theta.LambdaSSA.Naturality
import Silmaril.Proofs.SSA.Peggy.Bridge.Theta.LambdaSSA.Satisfaction

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA

open CategoryTheory
open Silmaril.Inst (Plain Comorphism)
open Silmaril.Logic.Institution (Inst)
open PEG.Bridge.Theta.Region.LambdaSSA (Primitive instruction Atom)
open Isotope (Value)
open RVSDG (Tuple)

universe u

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S T U : Signature Data}

theorem Native.Equation.map_id (e : Native.Equation S) : e.map (𝟙 S) = e :=
  Proofs.native_id e

theorem Native.Equation.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Native.Equation S) :
    e.map (f ≫ g) = (e.map f).map g :=
  Proofs.native_comp f g e

/-- Contravariant reduct precomposes only the primitive interpretation.
The same carriers, encodings, ambient state and structural test remain. -/
theorem instruction_reduct (f : S ⟶ T) (m : Model T) {σ : Type u}
    (op : Primitive S.dialect.ops) (input output : Value (Atom m.val)) (start finish : σ) :
    instruction m.val (Native.opcode f op) input start output finish ↔
      instruction (reduct f m).val op input start output finish :=
  Proofs.instruction_reduct f m op input output start finish

theorem Native.Code.returns_map (f : S ⟶ T) {carried : List (PEG.Ty Data)}
    (r : Native.Code S carried) (m : Model T) (input output : Tuple m.val.toPEG.Value carried) :
    (r.map f).Returns m input output ↔ r.Returns (reduct f m) input output :=
  Proofs.returns_map f r m input output

theorem Native.Equation.holds_map (f : S ⟶ T) (e : Native.Equation S) (m : Model T) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) :=
  Proofs.native_holds_map f e m

theorem CheckedEquation.map_id (e : CheckedEquation S) : e.map (𝟙 S) = e :=
  Proofs.checked_id e

theorem CheckedEquation.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : CheckedEquation S) :
    e.map (f ≫ g) = (e.map f).map g :=
  Proofs.checked_comp f g e

theorem ThetaImage.map_id (e : ThetaImage S) : e.map (𝟙 S) = e :=
  Proofs.image_id e

theorem ThetaImage.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : ThetaImage S) :
    e.map (f ≫ g) = (e.map f).map g :=
  Proofs.image_comp f g e

theorem CheckedEquation.toTheta_map (f : S ⟶ T) (e : CheckedEquation S) :
    (e.map f).toTheta = e.toTheta.map f :=
  Subtype.ext (Prod.ext (e.peg.translate_map f) rfl)

theorem CheckedEquation.satisfaction (e : CheckedEquation S) (m : Model S) :
    e.native.Holds m ↔ e.peg.Holds m :=
  Proofs.checked_satisfaction e m

/-- The real θ satisfaction relation on the admitted pair agrees with the
native equation's successful tuple relation. -/
theorem ThetaImage.satisfaction (e : ThetaImage S) (m : Model S) :
    e.val.2.Holds m ↔ e.val.1.Holds (thetaModel m) :=
  Proofs.image_satisfaction e m

/-- Native typed λSSA equations on the marked, fixed-sort signature family. -/
def nativePlain (Data : Type) : Plain.{1,0,0,1} (Signature Data) where
  Sen := Native.Equation
  map f e := e.map f
  map_id _ e := e.map_id
  map_comp f g e := e.map_comp f g
  Mod := Model
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.Holds m
  sat_map f m e := e.holds_map f m

/-- Use the existing Peggy satisfaction on sides equipped with both lowerings. -/
def checkedPlain (Data : Type) : Plain.{1,0,0,1} (Signature Data) where
  Sen := CheckedEquation
  map f e := e.map f
  map_id _ e := e.map_id
  map_comp f g e := e.map_comp f g
  Mod := Model
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.peg.Holds m
  sat_map f m e := e.peg.holds_map f m

/-- On the admitted θ presentation, use the real numbered θ satisfaction.
The native component supplies the executable choice of endpoint syntax. -/
def thetaImagePlain (Data : Type) : Plain.{1,0,0,1} (Signature Data) where
  Sen := ThetaImage
  map f e := e.map f
  map_id _ e := e.map_id
  map_comp f g e := e.map_comp f g
  Mod := Model
  reduct := reduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.val.1.Holds (thetaModel m)
  sat_map f m e := (thetaPlain Data).sat_map f m e.val.1

/-- Recover the original checked Peggy sentence and its model family. -/
def forgetPeggyCode (Data : Type) :
    Comorphism (IR.mathlibDiscrete (checkedPlain Data)) (IR.mathlibDiscrete (pegPlain Data)) :=
  IR.mathlibDiscreteComorphism <|
    Comorphism.ofPlain (P := checkedPlain Data) (Q := pegPlain Data) (𝟭 _)
      (fun _ e => e.peg) (fun _ m => m) (fun _ _ _ => Iff.rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)

/-- Forget the native representative, retaining the actual θ equation and
its marked total model family from the existing θ comorphism. -/
def forgetThetaImage (Data : Type) :
    Comorphism (IR.mathlibDiscrete (thetaImagePlain Data)) (IR.mathlibDiscrete (thetaPlain Data)) :=
  IR.mathlibDiscreteComorphism <|
    Comorphism.ofPlain (P := thetaImagePlain Data) (Q := thetaPlain Data) (𝟭 _)
      (fun _ e => e.val.1) (fun _ m => m) (fun _ _ _ => Iff.rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)

def peggyToThetaImage (Data : Type) :
    Comorphism (IR.mathlibDiscrete (checkedPlain Data)) (IR.mathlibDiscrete (thetaImagePlain Data)) :=
  IR.mathlibDiscreteComorphism <|
    Comorphism.ofPlain (P := checkedPlain Data) (Q := thetaImagePlain Data) (𝟭 _)
      (fun _ e => e.toTheta) (fun _ m => m) (fun _ m e => e.peg.satisfaction m)
      (fun f e => e.toTheta_map f) (fun _ _ => rfl)

def thetaImageToNative (Data : Type) :
    Comorphism (IR.mathlibDiscrete (thetaImagePlain Data)) (IR.mathlibDiscrete (nativePlain Data)) :=
  IR.mathlibDiscreteComorphism <|
    Comorphism.ofPlain (P := thetaImagePlain Data) (Q := nativePlain Data) (𝟭 _)
      (fun _ e => e.val.2) (fun _ m => m) (fun _ m e => e.satisfaction m)
      (fun _ _ => rfl) (fun _ _ => rfl)

/-- Checked Peggy to native λSSA, factoring through the θ presentation of
the paired compiler image. Both legs use the identity on marked signatures
and pull back native models to their original total primitive presentation. -/
def peggyToNative (Data : Type) :
    Comorphism (IR.mathlibDiscrete (checkedPlain Data)) (IR.mathlibDiscrete (nativePlain Data)) :=
  Inst.CoHom.comp (peggyToThetaImage Data) (thetaImageToNative Data)

theorem peggyToNative_signature (Data : Type) :
    (peggyToNative Data).Φ = 𝟭 (Signature Data) :=
  rfl

theorem peggyToNative_sentence (e : CheckedEquation S) :
    ((peggyToNative Data).ρ.app S).sen e = e.native :=
  rfl

/-- The paired presentation commutes with the existing Peggy-to-θ
comorphism after forgetting its companion code. -/
theorem thetaImage_agrees (Data : Type) :
    Inst.CoHom.comp (peggyToThetaImage Data) (forgetThetaImage Data) =
      Inst.CoHom.comp (forgetPeggyCode Data) (peggyToTheta Data) :=
  rfl

/-- Forgetting the native endpoint recovers the exact #4047 θ sentence. -/
theorem thetaImage_sentence (e : CheckedEquation S) :
    ((Inst.CoHom.comp (peggyToThetaImage Data) (forgetThetaImage Data)).ρ.app S).sen e =
      ((peggyToTheta Data).ρ.app S).sen e.peg :=
  rfl

theorem peggyToNative_model (m : Model S) :
    ((peggyToNative Data).ρ.app S).mod.obj (Discrete.mk m) = Discrete.mk m :=
  rfl

end Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA
