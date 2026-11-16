module

public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Representation
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
variable {A B C : Signature}

theorem literalReduct_id (L : LiteralModel A) : L.reduct (𝟙 A) = L := by
  cases L
  rfl

theorem literalReduct_comp (f : A ⟶ B) (g : B ⟶ C) (L : LiteralModel C) :
    L.reduct (f ≫ g) = (L.reduct g).reduct f := rfl

private theorem literalHom_hext {L L' K K' : LiteralModel A}
    (hL : L = L') (hK : K = K') (f : L ⟶ K) (g : L' ⟶ K')
    (h : HEq f.map g.map) : HEq f g := by
  cases hL
  cases hK
  cases f
  cases g
  cases eq_of_heq h
  rfl

theorem literalReductFunctor_id : literalReductFunctor (𝟙 A) = 𝟭 (LiteralModel A) := by
  apply Functor.hext literalReduct_id
  intro L K h
  apply literalHom_hext (literalReduct_id L) (literalReduct_id K)
  rfl

theorem literalReductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    literalReductFunctor (f ≫ g) = literalReductFunctor g ⋙ literalReductFunctor f := by
  apply Functor.hext (literalReduct_comp f g)
  intro L K h
  apply literalHom_hext (literalReduct_comp f g L) (literalReduct_comp f g K)
  rfl

/-- The compiled algebra of a literal reduct is exactly the ordinary EQ reduct. -/
theorem literalAlgebra_reduct (f : A ⟶ B) (L : LiteralModel B) :
    (L.reduct f).algebra = (EQ.Algebra.reduct (compileMap f)).obj L.algebra := by
  change EQ.Algebra.mk _ _ = EQ.Algebra.mk _ _
  congr 1
  funext n w s o args
  cases o <;> rfl

/-- Literal evaluation obeys the actual existing sentence/signature translation. -/
theorem literal_satisfaction (f : A ⟶ B) (L : LiteralModel B) (e : Sentence A) :
    (sentenceMap f e).Holds L.algebra ↔ e.Holds (L.reduct f).algebra := by
  rw [literalAlgebra_reduct]
  exact EQ.Equation.holds_map (compileMap f) L.algebra e

/-- The literal-subset institution retains every existing monotone signature map
and every actual sorted homomorphism. -/
def literalInstitution : Signature ⥤ Room.{0,0,1} where
  obj A := ⟨Sentence A, Cat.of (LiteralModel A), fun L e => e.Holds L.algebra⟩
  map f := ⟨sentenceMap f, literalReductFunctor f, literal_satisfaction f⟩
  map_id _ := Room.hom_ext (funext sentenceMap_id) literalReductFunctor_id
  map_comp f g := Room.hom_ext (funext (sentenceMap_comp f g)) (literalReductFunctor_comp f g)

def literalInst : Inst := ⟨Signature, literalInstitution⟩

theorem compile_reduct (f : A ⟶ B) (L : LiteralModel B) :
    (L.reduct f).model = reduct f L.model := by
  apply Model.ext
  exact literalAlgebra_reduct f L

private theorem compiledHom_hext {M M' N N' : Model A}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : HEq f.map g.map) : HEq f g := by
  cases hM
  cases hN
  cases f
  cases g
  cases eq_of_heq h
  rfl

/-- Compilation commutes with reducts on the entire model functor, including
all sorted morphisms; ambient values are not changed or chosen. -/
theorem compile_reductFunctor (f : A ⟶ B) :
    literalReductFunctor f ⋙ compileFunctor = compileFunctor ⋙ reductFunctor f := by
  apply Functor.hext (compile_reduct f)
  intro L K h
  apply compiledHom_hext (compile_reduct f L) (compile_reduct f K)
  rfl

/-- Sentences translate identically; target literal models compile backward to
coherent explicit-coercion models. This has the actual comorphism variance. -/
def toLiteralNat : institution ⟶ literalInstitution where
  app A := ⟨id, compileFunctor, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · rfl
    · exact (compile_reductFunctor f).symm

def toLiteral : Inst.CoHom inst literalInst := ⟨𝟭 Signature, toLiteralNat⟩

/-- Signature-natural compilation does not require filtered source sorts.
Local filtration is used only for the converse semantic representation. -/
theorem literal_theory_satisfiable_iff (filtered : LocallyFiltered A)
    (H : Set (Sentence A)) :
    (∃ M : Model A, ∀ e ∈ H, e.Holds M.algebra) ↔
      ∃ L : LiteralModel A, ∀ e ∈ H, e.Holds L.algebra :=
  theory_satisfiable_iff filtered H

theorem literal_theory_entails_iff (filtered : LocallyFiltered A)
    (H : Set (Sentence A)) (e : Sentence A) :
    (∀ M : Model A, (∀ h ∈ H, h.Holds M.algebra) → e.Holds M.algebra) ↔
      ∀ L : LiteralModel A, (∀ h ∈ H, h.Holds L.algebra) → e.Holds L.algebra :=
  theory_entails_iff filtered H e

/-- At a locally filtered signature, each coherent model is reached up to
actual model isomorphism by the public corridor API. -/
theorem toLiteral_isoExpansive (filtered : LocallyFiltered A) :
    Corridor.IsoExpansive (toLiteral.ρ.app A) := by
  intro M
  exact ⟨represent filtered M, ⟨(modelRepresentationIso filtered M).symm⟩⟩

/-- The reduct of the representation satisfies exactly the original equations. -/
theorem toLiteral_elemExpansive (filtered : LocallyFiltered A) :
    Corridor.ElemExpansive (toLiteral.ρ.app A) := by
  intro M
  exact ⟨represent filtered M, fun e => satisfies_represent_iff filtered M e⟩

/-- Public faithful-corridor borrowing reflects arbitrary-theory consequence. -/
theorem toLiteral_faithful (filtered : LocallyFiltered A) :
    Corridor.Faithful (toLiteral.ρ.app A) :=
  (toLiteral_elemExpansive filtered).faithful

/-- Exact semantic consequence in the actual institution rooms, using the
existing public elementary-expansiveness borrowing theorem. -/
theorem toLiteral_room_entails_iff (filtered : LocallyFiltered A)
    (H : Set (Sentence A)) (e : Sentence A) :
    (institution.obj A).Entails H e ↔
      (literalInstitution.obj A).Entails
        ((toLiteral.ρ.app A).sen '' H) ((toLiteral.ρ.app A).sen e) :=
  Corridor.entails_map_iff_of_elemExpansive (toLiteral_elemExpansive filtered) H e

end Silmaril.Logic.Algebraic.OrderSorted.Representation
