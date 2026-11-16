module

public import Silmaril.Logic.Institution.Examples.Equational

/-! The non-overloaded coherent-coercion fragment of order-sorted algebra.
The explicit inclusion operations follow Goguen–Meseguer (1992), §4.1.
Carriers are types linked by injections, not definitionally identified subsets.
Operation symbols retain their unique public EQ profiles. -/
@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

structure Signature where
  base : EQ.Signature
  order : PartialOrder base.S

instance (A : Signature) : PartialOrder A.base.S := A.order

structure Signature.Hom (A B : Signature) where
  base : A.base ⟶ B.base
  monotone : Monotone base.sorts

@[ext] theorem Signature.Hom.ext {A B : Signature} (f g : Signature.Hom A B)
    (h : f.base = g.base) : f = g := by cases f; cases g; cases h; rfl

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨𝟙 _, fun _ _ h => h⟩
  comp f g := ⟨f.base ≫ g.base, fun _ _ h => g.monotone (f.monotone h)⟩
  id_comp _ := Signature.Hom.ext _ _ rfl
  comp_id _ := Signature.Hom.ext _ _ rfl
  assoc _ _ _ := Signature.Hom.ext _ _ rfl

/-- Existing profile-indexed operations, plus an inclusion at every comparable pair. -/
inductive Operation (A : Signature) : (n : Nat) → (Fin n → A.base.S) → A.base.S → Type where
  | base {n w s} (op : A.base.Op n w s) : Operation A n w s
  | inclusion (s t : A.base.S) (h : s ≤ t) : Operation A 1 (fun _ => s) t

abbrev compiled (A : Signature) : EQ.Signature := ⟨A.base.S, Operation A⟩

def compileMap {A B : Signature} (f : A ⟶ B) : compiled A ⟶ compiled B where
  sorts := f.base.sorts
  ops := fun op => match op with
    | .base o => .base (f.base.ops o)
    | .inclusion s t h => .inclusion (f.base.sorts s) (f.base.sorts t) (f.monotone h)

@[simp] theorem compileMap_id (A : Signature) : compileMap (𝟙 A) = 𝟙 (compiled A) := by
  change EQ.Signature.Hom.mk _ _ = EQ.Signature.Hom.mk _ _
  congr 1
  funext n w s op
  cases op <;> rfl

@[simp] theorem compileMap_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    compileMap (f ≫ g) = compileMap f ≫ compileMap g := by
  change EQ.Signature.Hom.mk _ _ = EQ.Signature.Hom.mk _ _
  congr 1
  funext n w s op
  cases op <;> rfl

/-- Actual many-sorted signature, suitable for the public EQ evaluator. -/
def compiledSignatures : Signature ⥤ EQ.Signature where
  obj := compiled
  map := compileMap
  map_id := compileMap_id
  map_comp := compileMap_comp

abbrev Algebra (A : Signature) := EQ.Algebra (compiled A)

def Algebra.coerce {A : Signature} (M : Algebra A) {s t : A.base.S} (h : s ≤ t)
    (x : M.carrier s) : M.carrier t := M.op (.inclusion s t h) (fun _ => x)

/-- Identity, conditional injectivity and transitivity: §4.1, equations J(1–3).
There is no shared-name overloading in this fragment, hence no J(4) obligation. -/
structure Coherent {A : Signature} (M : Algebra A) : Prop where
  identity : ∀ s (x : M.carrier s), M.coerce (le_refl s) x = x
  injective : ∀ {s t} (h : s ≤ t), Function.Injective (M.coerce h)
  composition : ∀ {s t u} (h : s ≤ t) (k : t ≤ u) (x : M.carrier s),
    M.coerce k (M.coerce h x) = M.coerce (le_trans h k) x

structure Model (A : Signature) where
  algebra : Algebra A
  coherent : Coherent algebra

@[ext] theorem Model.ext {A : Signature} (M N : Model A) (h : M.algebra = N.algebra) : M = N := by
  cases M; cases N; cases h; rfl

/-- Genuine sorted homomorphisms also commute with all inclusion operations. -/
instance (A : Signature) : Category (Model A) where
  Hom M N := EQ.Algebra.Hom M.algebra N.algebra
  id M := 𝟙 M.algebra
  comp f g := ⟨fun s x => g.map s (f.map s x), by
    intro n w s o args
    rw [f.map_op, g.map_op]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem Model.hom_coerce {A : Signature} {M N : Model A} (f : M ⟶ N)
    {s t : A.base.S} (h : s ≤ t) (x : M.algebra.carrier s) :
    f.map t (M.algebra.coerce h x) = N.algebra.coerce h (f.map s x) :=
  f.map_op (.inclusion s t h) (fun _ => x)

abbrev Sentence (A : Signature) := EQ.Equation (compiled A)

def reduct {A B : Signature} (f : A ⟶ B) (M : Model B) : Model A where
  algebra := (EQ.Algebra.reduct (compileMap f)).obj M.algebra
  coherent := {
    identity := fun s x => M.coherent.identity (f.base.sorts s) x
    injective := fun h => M.coherent.injective (f.monotone h)
    composition := fun h k x => M.coherent.composition (f.monotone h) (f.monotone k) x }

def reductFunctor {A B : Signature} (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := (EQ.Algebra.reduct (compileMap f)).map h
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.Algebraic.OrderSorted
