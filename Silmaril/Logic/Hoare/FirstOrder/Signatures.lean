module

public import Silmaril.Logic.Hoare.FirstOrder.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Hoare.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples

structure FixedSignature (S : Type) where
  operations : (n : Nat) → (Fin n → S) → S → Type
  relations : (n : Nat) → (Fin n → S) → Type

abbrev FixedSignature.fol {S : Type} (A : FixedSignature S) : FOL.Signature :=
  ⟨⟨S, A.operations⟩, A.relations⟩

structure FixedHom {S : Type} (A B : FixedSignature S) where
  operations : ∀ {n w s}, A.operations n w s → B.operations n w s
  relations : ∀ {n w}, A.relations n w → B.relations n w

instance {S : Type} : Category (FixedSignature S) where
  Hom := FixedHom
  id _ := ⟨fun o => o, fun r => r⟩
  comp f g := ⟨fun o => g.operations (f.operations o), fun r => g.relations (f.relations r)⟩

def FixedHom.fol {S} {A B : FixedSignature S} (f : A ⟶ B) : A.fol ⟶ B.fol :=
  ⟨⟨id, f.operations⟩, f.relations⟩

def toFOL (S : Type) : FixedSignature S ⥤ FOL.Signature where
  obj := FixedSignature.fol
  map := FixedHom.fol

variable {S : Type} {A B C : FixedSignature S}

def atomMap (f : A ⟶ B) : Atom A.fol → Atom B.fol
  | .eq Γ t u => .eq Γ (t.map f.fol.toHom) (u.map f.fol.toHom)
  | .rel Γ r args => .rel Γ (f.relations r) (fun j => (args j).map f.fol.toHom)

def languageMap (f : A ⟶ B) : language A.fol ⟶ language B.fol := ⟨atomMap f, id⟩

theorem atomMap_id (a : Atom A.fol) : atomMap (𝟙 A) a = a := by
  cases a with
  | eq Γ t u => exact congrArg₂ (Atom.eq Γ) (EQ.Term.map_id t) (EQ.Term.map_id u)
  | rel Γ r args => exact congrArg (Atom.rel Γ r) (funext fun j => EQ.Term.map_id (args j))

theorem atomMap_comp (f : A ⟶ B) (g : B ⟶ C) (a : Atom A.fol) :
    atomMap (f ≫ g) a = atomMap g (atomMap f a) := by
  cases a with
  | eq Γ t u =>
      exact congrArg₂ (Atom.eq (A := C.fol) Γ)
        (EQ.Term.map_comp f.fol.toHom g.fol.toHom t) (EQ.Term.map_comp f.fol.toHom g.fol.toHom u)
  | rel Γ r args =>
      exact congrArg (Atom.rel (A := C.fol) Γ (g.relations (f.relations r)))
        (funext fun j => EQ.Term.map_comp f.fol.toHom g.fol.toHom (args j))

def nativeSignatureMap (f : A ⟶ B) : signature A.fol ⟶ signature B.fol :=
  ⟨languageMap f, fun c => by cases c <;> rfl⟩

def toNative (S : Type) : FixedSignature S ⥤ Hoare.Signature (Command S) where
  obj A := signature A.fol
  map := nativeSignatureMap
  map_id _ := Hoare.Signature.Hom.ext _ _ _ (by
    change ModalMu.Renaming.mk _ _ = ModalMu.Renaming.mk _ _
    congr 1
    exact funext atomMap_id)
  map_comp f g := Hoare.Signature.Hom.ext _ _ _ (by
    change ModalMu.Renaming.mk _ _ = ModalMu.Renaming.mk _ _
    congr 1
    exact funext (atomMap_comp f g))


end Silmaril.Logic.Hoare.FirstOrder
