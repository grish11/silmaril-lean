module

public import Silmaril.Logic.Separation.FirstOrder.Compiler

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.FirstOrder
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

def atomMap (f : A ⟶ B) : signature A.fol ⟶ signature B.fol
  | .cell n s => .cell n s
  | .eq Γ t u => .eq Γ (t.map f.fol.toHom) (u.map f.fol.toHom)
  | .rel Γ r args => .rel Γ (f.relations r) (fun j => (args j).map f.fol.toHom)

theorem atomMap_id (a : Atom A.fol) : atomMap (𝟙 A) a = a := by
  cases a with
  | cell => rfl
  | eq Γ t u => exact congrArg₂ (Atom.eq Γ) (EQ.Term.map_id t) (EQ.Term.map_id u)
  | rel Γ r args => exact congrArg (Atom.rel Γ r) (funext fun j => EQ.Term.map_id (args j))

theorem atomMap_comp (f : A ⟶ B) (g : B ⟶ C) (a : Atom A.fol) :
    atomMap (f ≫ g) a = atomMap g (atomMap f a) := by
  cases a with
  | cell => rfl
  | eq Γ t u =>
      exact congrArg₂ (Atom.eq (A := C.fol) Γ)
        (EQ.Term.map_comp f.fol.toHom g.fol.toHom t) (EQ.Term.map_comp f.fol.toHom g.fol.toHom u)
  | rel Γ r args =>
      exact congrArg (Atom.rel (A := C.fol) Γ (g.relations (f.relations r)))
        (funext fun j => EQ.Term.map_comp f.fol.toHom g.fol.toHom (args j))

def toNative (S : Type) : FixedSignature S ⥤ Separation.Signature where
  obj A := signature A.fol
  map := atomMap
  map_id _ := funext atomMap_id
  map_comp f g := funext (atomMap_comp f g)

theorem native_reduct (f : A ⟶ B) (M : FOL.Structure B.fol) :
    native ((FOL.Structure.reduct f.fol).obj M) = Separation.reduct (atomMap f) (native M) := by
  apply congrArg (Separation.Model.mk (resource (Value M)))
  funext a
  apply Set.ext
  intro h
  cases a with
  | cell => rfl
  | eq Γ t u =>
      change (∃ ρ, Encodes _ Γ ρ h ∧ _) ↔ (∃ ρ, Encodes M Γ ρ h ∧ _)
      apply exists_congr
      intro ρ
      exact and_congr Iff.rfl (Iff.of_eq (congrArg₂ Eq
        (EQ.Term.eval_map f.fol.toHom M.toAlgebra ρ t)
        (EQ.Term.eval_map f.fol.toHom M.toAlgebra ρ u)).symm)
  | rel Γ r args =>
      change (∃ ρ, Encodes _ Γ ρ h ∧ _) ↔ (∃ ρ, Encodes M Γ ρ h ∧ _)
      apply exists_congr
      intro ρ
      exact and_congr Iff.rfl (Iff.of_eq (congrArg (M.rel (f.relations r))
        (funext fun j => EQ.Term.eval_map f.fol.toHom M.toAlgebra ρ (args j))).symm)

theorem nativeHom_hext {D : Separation.Signature} {M M' N N' : Separation.Model D}
    (hm : M = M') (hn : N = N') (f : Separation.Model.Hom M N)
    (g : Separation.Model.Hom M' N') (h : HEq f.map g.map) : HEq f g := by
  cases hm
  cases hn
  exact heq_of_eq (Separation.Model.Hom.ext _ _ (eq_of_heq h))

/-- Actual native model arrows commute with signature reduct, not merely object satisfaction. -/
theorem realization_naturality (f : A ⟶ B) :
    realization B.fol ⋙ Separation.reductFunctor (atomMap f) =
      FOL.Structure.reduct f.fol ⋙ realization A.fol := by
  apply Functor.hext (fun M => (native_reduct f M).symm)
  intro M N g
  exact nativeHom_hext (native_reduct f M).symm (native_reduct f N).symm _ _ HEq.rfl

theorem compile_naturality (f : A ⟶ B) {k} {Γ : Fin k → A.fol.S} (φ : FOL.Formula A.fol Γ) :
    (compile φ).map (atomMap f) = compile (φ.map f.fol) := by
  induction φ with
  | eq => rfl
  | rel => rfl
  | tt => rfl
  | not φ ih => exact congrArg Assertion.neg ih
  | and φ ψ hp hq => exact congrArg₂ Assertion.conj hp hq
  | all hc φ ih => exact congrArg (Assertion.wand (A := signature B.fol) (.atom (Atom.cell _ _))) ih

theorem sentence_naturality (f : A ⟶ B) (φ : FOL.Sentence A.fol) :
    (sentence φ).map (atomMap f) = sentence (φ.map f.fol) :=
  congrArg (BaseSentence.mk .emp) (compile_naturality f φ.formula)

end Silmaril.Logic.Separation.FirstOrder
