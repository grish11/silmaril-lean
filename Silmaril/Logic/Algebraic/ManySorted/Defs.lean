module

public import Silmaril.Logic.Institution.Theory
public import Silmaril.Logic.Institution.Morphism

/-! Finitary many-sorted equational logic, with a fixed arbitrary set of sorts.
Signature maps preserve operation profiles. Nullary operations and empty carriers
are allowed. Models and their homomorphisms are genuine sorted algebras.
See Goguen–Burstall (1992), equational-logic institution example. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted
open CategoryTheory Silmaril.Logic.Institution

variable (S : Type)

structure Signature where
  operations : (n : Nat) → (Fin n → S) → S → Type

structure Signature.Hom (A B : Signature S) where
  operations : ∀ {n inputs output}, A.operations n inputs output → B.operations n inputs output

@[ext] theorem Signature.Hom.ext {A B : Signature S} (f g : Signature.Hom S A B)
    (h : ∀ n inputs output op, @f.operations n inputs output op = @g.operations n inputs output op) : f = g := by
  cases f; cases g; congr; funext n inputs output op; exact h n inputs output op

instance : Category (Signature S) where
  Hom := Signature.Hom S
  id _ := ⟨fun op => op⟩
  comp f g := ⟨fun op => g.operations (f.operations op)⟩
  id_comp _ := Signature.Hom.ext S _ _ (fun _ _ _ _ => rfl)
  comp_id _ := Signature.Hom.ext S _ _ (fun _ _ _ _ => rfl)
  assoc _ _ _ := Signature.Hom.ext S _ _ (fun _ _ _ _ => rfl)

variable {S} (A : Signature S)

inductive Term {k : Nat} (Γ : Fin k → S) : S → Type where
  | var (i : Fin k) : Term Γ (Γ i)
  | app {n inputs output} (op : A.operations n inputs output)
      (args : (i : Fin n) → Term Γ (inputs i)) : Term Γ output

structure Model where
  carrier : S → Type
  operation : ∀ {n inputs output}, A.operations n inputs output →
    ((i : Fin n) → carrier (inputs i)) → carrier output

namespace Model
variable {A}
structure Hom (M N : Model A) where
  map : ∀ s, M.carrier s → N.carrier s
  operation : ∀ {n inputs output} (op : A.operations n inputs output) args,
    map output (M.operation op args) = N.operation op (fun i => map (inputs i) (args i))

@[ext] theorem Hom.ext {M N : Model A} (f g : Hom M N) (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

instance : Category (Model A) where
  Hom := Hom
  id M := ⟨fun _ x => x, fun _ _ => rfl⟩
  comp f g := ⟨fun s x => g.map s (f.map s x), by
    intro n inputs output op args
    rw [f.operation, g.operation]⟩
  id_comp _ := Hom.ext _ _ rfl
  comp_id _ := Hom.ext _ _ rfl
  assoc _ _ _ := Hom.ext _ _ rfl

def eval (M : Model A) {k} {Γ : Fin k → S} (v : ∀ i, M.carrier (Γ i))
    {s} : Term A Γ s → M.carrier s
  | .var i => v i
  | .app op args => M.operation op (fun i => M.eval v (args i))
end Model

namespace Term
variable {A} {B C : Signature S} {k} {Γ : Fin k → S} {s}
def map (f : A ⟶ B) {s : S} : Term A Γ s → Term B Γ s
  | .var i => .var i
  | .app op args => .app (f.operations op) (fun i => map f (args i))

@[simp] theorem map_id (t : Term A Γ s) : map (𝟙 A) t = t := by
  induction t with
  | var => rfl
  | app op args ih => simp only [map]; congr; funext i; exact ih i

@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (t : Term A Γ s) :
    map (f ≫ g) t = map g (map f t) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Term.app (g.operations (f.operations op))) (funext ih)
end Term

namespace Signature.Hom
variable {A} {B C : Signature S}
def reduct (f : A ⟶ B) (M : Model B) : Model A where
  carrier := M.carrier
  operation op args := M.operation (f.operations op) args

def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := ⟨h.map, fun op args => h.operation (f.operations op) args⟩
  map_id _ := Model.Hom.ext _ _ rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl

theorem eval_map (f : A ⟶ B) (M : Model B) {k} {Γ : Fin k → S}
    (v : ∀ i, M.carrier (Γ i)) {s} (t : Term A Γ s) :
    M.eval v (Term.map f t) = (reduct f M).eval v t := by
  induction t with
  | var => rfl
  | app op args ih => simp only [Term.map, Model.eval]; congr; funext i; exact ih i

private theorem hom_hext {M M' N N' : Model A} (hM : M = M') (hN : N = N')
    (f : Model.Hom M N) (g : Model.Hom M' N') (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (Model.Hom.ext _ _ (eq_of_heq h))

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
end Signature.Hom

/-- An equation with universally quantified, sort-correct finite context. -/
structure Equation where
  variableCount : Nat
  context : Fin variableCount → S
  sort : S
  lhs : Term A context sort
  rhs : Term A context sort

namespace Equation
variable {A} {B C : Signature S}
def map (f : A ⟶ B) (e : Equation A) : Equation B :=
  ⟨e.variableCount, e.context, e.sort, Term.map f e.lhs, Term.map f e.rhs⟩
def Satisfies (M : Model A) (e : Equation A) : Prop :=
  ∀ v : (i : Fin e.variableCount) → M.carrier (e.context i), M.eval v e.lhs = M.eval v e.rhs
@[simp] theorem map_id (e : Equation A) : map (𝟙 A) e = e := by cases e; simp [map]
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    map (f ≫ g) e = map g (map f e) := by cases e; simp [map]
theorem satisfaction (f : A ⟶ B) (M : Model B) (e : Equation A) :
    Satisfies M (map f e) ↔ Satisfies (Signature.Hom.reduct f M) e := by
  simp only [Satisfies, map, Signature.Hom.eval_map]
  rfl
end Equation

/-- Equational logic over all signatures on the fixed sort set S. -/
def institution (S : Type) : Signature S ⥤ Room where
  obj A := ⟨Equation A, Cat.of (Model A), Equation.Satisfies⟩
  map f := ⟨Equation.map f, Signature.Hom.reductFunctor f, Equation.satisfaction f⟩
  map_id _ := by
    apply Room.hom_ext
    · funext e; exact Equation.map_id e
    · exact Signature.Hom.reductFunctor_id
  map_comp f g := by
    apply Room.hom_ext
    · funext e; exact Equation.map_comp f g e
    · exact Signature.Hom.reductFunctor_comp f g

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst (S : Type) := (⟨Signature S, institution S⟩ : Silmaril.Logic.Institution.Inst)

/-- Actual axiom presentations reuse the shared institution category. -/
abbrev Presentation (S : Type) := Silmaril.Logic.Institution.Presentation (institution S)
abbrev Theory (S : Type) := Silmaril.Logic.Institution.Theory (institution S)

end Silmaril.Logic.Algebraic.ManySorted
