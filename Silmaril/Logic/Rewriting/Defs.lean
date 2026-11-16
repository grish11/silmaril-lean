module

public import Silmaril.Logic.Algebraic.ManySorted.Defs

/-! The thin (preordered) unconditional fragment of rewriting logic. Equations
remain equality of objects; rewrites are directed arrows. This forgets proof
identity and therefore does not claim the full categorical concurrency semantics. -/
@[expose] public section
namespace Silmaril.Logic.Rewriting
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {A B C : Algebraic.ManySorted.Signature S}

structure Model (A : Algebraic.ManySorted.Signature S) where
  algebra : Algebraic.ManySorted.Model A
  reaches : ∀ s, algebra.carrier s → algebra.carrier s → Prop
  refl : ∀ s x, reaches s x x
  trans : ∀ s {x y z}, reaches s x y → reaches s y z → reaches s x z
  congruence : ∀ {n inputs output} (op : A.operations n inputs output) x y,
    (∀ i, reaches (inputs i) (x i) (y i)) →
    reaches output (algebra.operation op x) (algebra.operation op y)

structure Model.Hom (M N : Model A) where
  algebra : Algebraic.ManySorted.Model.Hom M.algebra N.algebra
  monotone : ∀ s {x y}, M.reaches s x y → N.reaches s (algebra.map s x) (algebra.map s y)

@[ext] theorem Model.Hom.ext {M N : Model A} (f g : Model.Hom M N)
    (h : f.algebra = g.algebra) : f = g := by cases f; cases g; cases h; rfl

def Model.Hom.id (M : Model A) : Model.Hom M M :=
  ⟨𝟙 M.algebra, fun _ {_ _} h => h⟩

def Model.Hom.comp {M N P : Model A} (f : Model.Hom M N) (g : Model.Hom N P) : Model.Hom M P :=
  { algebra :=
      { map := fun s x => g.algebra.map s (f.algebra.map s x)
        operation := by
          intro n inputs output op args
          rw [f.algebra.operation, g.algebra.operation] }
    monotone := fun s {_ _} h => g.monotone s (f.monotone s h) }

instance : Category (Model A) where
  Hom := Model.Hom
  id := Model.Hom.id
  comp := Model.Hom.comp
  id_comp _ :=  Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)
  comp_id _ :=  Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)
  assoc _ _ _ := Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)

def reduct (f : A ⟶ B) (M : Model B) : Model A where
  algebra := Algebraic.ManySorted.Signature.Hom.reduct f M.algebra
  reaches := M.reaches
  refl := M.refl
  trans := M.trans
  congruence op := M.congruence (f.operations op)

def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := ⟨(Algebraic.ManySorted.Signature.Hom.reductFunctor f).map h.algebra, h.monotone⟩
  map_id _ := Model.Hom.ext _ _ rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl

private theorem hom_hext {M M' N N' : Model A} (hM : M = M') (hN : N = N')
    (f : Model.Hom M N) (g : Model.Hom M' N') (h : HEq f.algebra.map g.algebra.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ (eq_of_heq h)))

theorem reduct_id (M : Model A) : reduct (𝟙 A) M = M := by cases M; rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext reduct_id
  intro M N f
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl

/-- A presentation can impose equations E separately from directed rules R. -/
inductive Sentence (A : Algebraic.ManySorted.Signature S) where
  | equation : Algebraic.ManySorted.Equation A → Sentence A
  | rewrite : Algebraic.ManySorted.Equation A → Sentence A

def Sentence.map (f : A ⟶ B) : Sentence A → Sentence B
  | .equation e => .equation (e.map f)
  | .rewrite e => .rewrite (e.map f)

def Sentence.Satisfies (M : Model A) : Sentence A → Prop
  | .equation e => e.Satisfies M.algebra
  | .rewrite e => ∀ v, M.reaches e.sort (M.algebra.eval v e.lhs) (M.algebra.eval v e.rhs)

@[simp] theorem Sentence.map_id (p : Sentence A) : p.map (𝟙 A) = p := by
  cases p <;> simp [map]

@[simp] theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by cases p <;> simp [map]

theorem Sentence.satisfaction (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Satisfies M (p.map f) ↔ Satisfies (reduct f M) p := by
  cases p with
  | equation e => exact Algebraic.ManySorted.Equation.satisfaction f M.algebra e
  | rewrite e => simp only [Satisfies, map, Algebraic.ManySorted.Equation.map, Algebraic.ManySorted.Signature.Hom.eval_map]; rfl

def institution (S : Type) : Algebraic.ManySorted.Signature S ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, reductFunctor f, Sentence.satisfaction f⟩
  map_id _ := by
    apply Room.hom_ext
    · funext p; exact Sentence.map_id p
    · exact reductFunctor_id
  map_comp f g := by
    apply Room.hom_ext
    · funext p; exact Sentence.map_comp f g p
    · exact reductFunctor_comp f g

abbrev Presentation (S : Type) := Silmaril.Logic.Institution.Presentation (institution S)
abbrev Theory (S : Type) := Silmaril.Logic.Institution.Theory (institution S)

end Silmaril.Logic.Rewriting
