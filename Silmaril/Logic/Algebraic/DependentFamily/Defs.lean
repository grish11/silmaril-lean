module

public import Silmaril.Logic.Institution.Theory
public import Silmaril.Logic.Institution.Morphism

/-! A bounded dependent algebraic fragment. Sort constructors take variables of
one base sort; operations can depend on those variables and take indexed fiber
arguments. There are no operations returning the base sort, dependencies on
fiber terms, type equations, or general iterated dependent contexts here. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.DependentFamily
open CategoryTheory Silmaril.Logic.Institution

variable (S : Type) (arity : S → Nat)

/-- A dependent sort expression in a context of base variables. -/
structure SortExpr (k : Nat) where
  symbol : S
  arguments : Fin (arity symbol) → Fin k

namespace SortExpr
variable {S arity} {k l : Nat}
def rename (ρ : Fin k → Fin l) (t : SortExpr S arity k) : SortExpr S arity l :=
  ⟨t.symbol, fun i => ρ (t.arguments i)⟩
end SortExpr

structure Signature where
  operations : (k n : Nat) → (Fin n → SortExpr S arity k) → SortExpr S arity k → Type

structure Signature.Hom (A B : Signature S arity) where
  operations : ∀ {k n inputs output}, A.operations k n inputs output → B.operations k n inputs output

@[ext] theorem Signature.Hom.ext {A B : Signature S arity} (f g : Signature.Hom S arity A B)
    (h : ∀ k n inputs output op, @f.operations k n inputs output op = @g.operations k n inputs output op) : f = g := by
  cases f; cases g; congr; funext k n inputs output op; exact h k n inputs output op

instance : Category (Signature S arity) where
  Hom := Signature.Hom S arity
  id _ := ⟨fun op => op⟩
  comp f g := ⟨fun op => g.operations (f.operations op)⟩
  id_comp _ := Signature.Hom.ext S arity _ _ (fun _ _ _ _ _ => rfl)
  comp_id _ := Signature.Hom.ext S arity _ _ (fun _ _ _ _ _ => rfl)
  assoc _ _ _ := Signature.Hom.ext S arity _ _ (fun _ _ _ _ _ => rfl)

variable {S arity} (A : Signature S arity)

/-- Fiber terms may instantiate universally quantified base arguments. -/
inductive Term {k n : Nat} (Γ : Fin n → SortExpr S arity k) : SortExpr S arity k → Type where
  | var (i : Fin n) : Term Γ (Γ i)
  | app {b m inputs output} (op : A.operations b m inputs output)
      (ρ : Fin b → Fin k)
      (args : (i : Fin m) → Term Γ ((inputs i).rename ρ)) : Term Γ (output.rename ρ)

/-- The base carrier varies between models; fibers genuinely depend on its elements. -/
structure Model where
  Base : Type
  carrier : (s : S) → (Fin (arity s) → Base) → Type
  operation : ∀ {k n inputs output}, A.operations k n inputs output →
    (base : Fin k → Base) →
    ((i : Fin n) → carrier (inputs i).symbol (fun j => base ((inputs i).arguments j))) →
    carrier output.symbol (fun j => base (output.arguments j))

namespace Model
variable {A}
abbrev Fiber (M : Model A) {k} (base : Fin k → M.Base) (t : SortExpr S arity k) :=
  M.carrier t.symbol (fun j => base (t.arguments j))

/-- Homomorphisms map the base carrier and the corresponding dependent fibers. -/
structure Hom (M N : Model A) where
  base : M.Base → N.Base
  map : ∀ s index, M.carrier s index → N.carrier s (fun i => base (index i))
  operation : ∀ {k n inputs output} (op : A.operations k n inputs output) b args,
    map output.symbol (fun j => b (output.arguments j)) (M.operation op b args) =
      N.operation op (fun j => base (b j))
        (fun i => map (inputs i).symbol (fun j => b ((inputs i).arguments j)) (args i))

@[ext] theorem Hom.ext {M N : Model A} (f g : Hom M N)
    (hb : f.base = g.base) (hm : HEq f.map g.map) : f = g := by
  cases f; cases g; cases hb; cases eq_of_heq hm; rfl

instance : Category (Model A) where
  Hom := Hom
  id _ := ⟨fun x => x, fun _ _ x => x, fun _ _ _ => rfl⟩
  comp f g := ⟨fun x => g.base (f.base x),
    fun s i x => g.map s _ (f.map s i x), by
      intro k n inputs output op b args
      rw [f.operation]
      exact g.operation op (fun j => f.base (b j))
        (fun i => f.map (inputs i).symbol (fun j => b ((inputs i).arguments j)) (args i))⟩
  id_comp _ := Hom.ext _ _ rfl HEq.rfl
  comp_id _ := Hom.ext _ _ rfl HEq.rfl
  assoc _ _ _ := Hom.ext _ _ rfl HEq.rfl

def eval (M : Model A) {k n} {Γ : Fin n → SortExpr S arity k}
    (base : Fin k → M.Base) (v : ∀ i, M.Fiber base (Γ i))
    {s} : Term A Γ s → M.Fiber base s
  | .var i => v i
  | .app op ρ args => M.operation op (fun j => base (ρ j)) (fun i => M.eval base v (args i))
end Model

namespace Term
variable {A} {B C : Signature S arity} {k n} {Γ : Fin n → SortExpr S arity k} {s}
def map (f : A ⟶ B) {s} : Term A Γ s → Term B Γ s
  | .var i => .var i
  | .app op ρ args => .app (f.operations op) ρ (fun i => map f (args i))

@[simp] theorem map_id (t : Term A Γ s) : map (𝟙 A) t = t := by
  induction t with
  | var => rfl
  | app op ρ args ih => simp only [map]; congr; funext i; exact ih i

@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (t : Term A Γ s) :
    map (f ≫ g) t = map g (map f t) := by
  induction t with
  | var => rfl
  | app op ρ args ih => exact congrArg (fun a => Term.app (g.operations (f.operations op)) ρ a) (funext ih)
end Term

namespace Signature.Hom
variable {A} {B C : Signature S arity}
def reduct (f : A ⟶ B) (M : Model B) : Model A where
  Base := M.Base
  carrier := M.carrier
  operation op base args := M.operation (f.operations op) base args

def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map {X Y} h := (⟨h.base, h.map, fun op b args => h.operation (f.operations op) b args⟩ :
    Model.Hom (reduct f X) (reduct f Y))
  map_id _ := Model.Hom.ext _ _ rfl HEq.rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl HEq.rfl

theorem eval_map (f : A ⟶ B) (M : Model B) {k n} {Γ : Fin n → SortExpr S arity k}
    (base : Fin k → M.Base) (v : ∀ i, M.Fiber base (Γ i)) {s} (t : Term A Γ s) :
    M.eval base v (Term.map f t) = (reduct f M).eval base v t := by
  induction t with
  | var => rfl
  | app op ρ args ih => simp only [Term.map, Model.eval]; congr; funext i; exact ih i

theorem reduct_id (M : Model A) : reduct (𝟙 A) M = M := by cases M; rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl
private theorem hom_hext {M M' N N' : Model A} (hM : M = M') (hN : N = N')
    (f : Model.Hom M N) (g : Model.Hom M' N')
    (hb : HEq f.base g.base) (hm : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (Model.Hom.ext _ _ (eq_of_heq hb) hm)

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext reduct_id
  intro M N f
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl HEq.rfl
end Signature.Hom

/-- Both base variables and fiber variables are universally quantified. -/
structure Equation where
  baseCount : Nat
  variableCount : Nat
  context : Fin variableCount → SortExpr S arity baseCount
  sort : SortExpr S arity baseCount
  lhs : Term A context sort
  rhs : Term A context sort

namespace Equation
variable {A} {B C : Signature S arity}
def map (f : A ⟶ B) (e : Equation A) : Equation B :=
  ⟨e.baseCount, e.variableCount, e.context, e.sort, Term.map f e.lhs, Term.map f e.rhs⟩
def Satisfies (M : Model A) (e : Equation A) : Prop :=
  ∀ (base : Fin e.baseCount → M.Base) (v : (i : Fin e.variableCount) → M.Fiber base (e.context i)),
    M.eval base v e.lhs = M.eval base v e.rhs
@[simp] theorem map_id (e : Equation A) : map (𝟙 A) e = e := by cases e; simp [map]
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    map (f ≫ g) e = map g (map f e) := by cases e; simp [map]
theorem satisfaction (f : A ⟶ B) (M : Model B) (e : Equation A) :
    Satisfies M (map f e) ↔ Satisfies (Signature.Hom.reduct f M) e := by
  simp only [Satisfies, map, Signature.Hom.eval_map]
  rfl
end Equation

/-- The institution of this finite, one-layer dependent-family fragment. -/
def institution (S : Type) (arity : S → Nat) : Signature S arity ⥤ Room where
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

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst (S : Type) (arity : S → Nat) := (⟨Signature S arity, institution S arity⟩ : Silmaril.Logic.Institution.Inst)

abbrev Presentation (S : Type) (arity : S → Nat) :=
  Silmaril.Logic.Institution.Presentation (institution S arity)

end Silmaril.Logic.Algebraic.DependentFamily
