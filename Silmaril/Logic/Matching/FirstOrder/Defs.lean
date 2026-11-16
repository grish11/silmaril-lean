module

public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fin.Basic

/-! Roșu's 2017 many-sorted first-order matching patterns (Definitions 2.1–2.5).
Binders use sorted de Bruijn contexts. Operations return arbitrary sets, including
empty and nondeterministic results; every sort carrier is nonempty as in the paper.
This is the first-order core, without the 2019 μ/set-variable extension. -/
@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {S : Type} (A : Signature S)

inductive Pattern : {k : Nat} → (Fin k → S) → S → Type where
  | var {k : Nat} {Γ : Fin k → S} (i : Fin k) : Pattern Γ (Γ i)
  | app {k : Nat} {Γ : Fin k → S} {n : Nat} {inputs : Fin n → S} {output : S} (op : A.operations n inputs output)
      (args : (i : Fin n) → Pattern Γ (inputs i)) : Pattern Γ output
  | neg {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern (k := k) Γ s) : Pattern Γ s
  | conj {k : Nat} {Γ : Fin k → S} {s : S} (p q : Pattern (k := k) Γ s) : Pattern Γ s
  | ex {k : Nat} {Γ : Fin k → S} {s : S} (bound : S) (body : Pattern (k := k+1) (Fin.cases bound Γ) s) :
      Pattern (k := k) Γ s

structure Model where
  carrier : S → Type
  nonempty : ∀ s, Nonempty (carrier s)
  operation : ∀ {n inputs output}, A.operations n inputs output →
    ((i : Fin n) → carrier (inputs i)) → Set (carrier output)

namespace Model
variable {A}
/-- Relational homomorphisms preserve operation-graph membership; they need not
preserve denotation of complements or global satisfaction. -/
structure Hom (M N : Model A) where
  map : ∀ s, M.carrier s → N.carrier s
  operation : ∀ {n inputs output} (op : A.operations n inputs output) args result,
    result ∈ M.operation op args →
      map output result ∈ N.operation op (fun i => map (inputs i) (args i))
@[ext] theorem Hom.ext {M N : Model A} (f g : Hom M N) (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl
instance : Category (Model A) where
  Hom := Hom
  id _ := ⟨fun _ x => x, fun _ _ _ h => h⟩
  comp f g := ⟨fun s x => g.map s (f.map s x), fun op args result h =>
    g.operation op _ _ (f.operation op args result h)⟩
  id_comp _ := Hom.ext _ _ rfl
  comp_id _ := Hom.ext _ _ rfl
  assoc _ _ _ := Hom.ext _ _ rfl

/-- Set extension of operation symbols and existential union are explicit. -/
def denote (M : Model A) {k : Nat} {Γ : Fin k → S} {s : S} (v : (i : Fin k) → M.carrier (Γ i)) :
    Pattern A Γ s → Set (M.carrier s)
  | .var i => {v i}
  | .app op args => {result | ∃ values,
      (∀ i, values i ∈ M.denote v (args i)) ∧ result ∈ M.operation op values}
  | .neg p => (M.denote v p)ᶜ
  | .conj p q => M.denote v p ∩ M.denote v q
  | .ex bound body => {result | ∃ value : M.carrier bound,
      result ∈ M.denote (Fin.cases value v) body}
end Model

namespace Pattern
variable {A} {B C : Signature S}
def map (f : A ⟶ B) {k : Nat} {Γ : Fin k → S} {s : S} : Pattern (k := k) A Γ s → Pattern B Γ s
  | .var i => .var i
  | .app op args => .app (f.operations op) (fun i => map f (args i))
  | .neg p => .neg (map f p)
  | .conj p q => .conj (map f p) (map f q)
  | .ex bound body => .ex bound (map f body)
@[simp] theorem map_id {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern (k := k) A Γ s) : map (𝟙 A) p = p := by
  induction p with
  | var => rfl
  | app op args ih => exact congrArg (Pattern.app op) (funext ih)
  | neg p ih => exact congrArg Pattern.neg ih
  | conj p q ihp ihq => exact congrArg₂ Pattern.conj ihp ihq
  | ex bound body ih => exact congrArg (Pattern.ex bound) ih
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern (k := k) A Γ s) :
    map (f ≫ g) p = map g (map f p) := by
  induction p with
  | var => rfl
  | app op args ih => exact congrArg (Pattern.app (g.operations (f.operations op))) (funext ih)
  | neg p ih => exact congrArg Pattern.neg ih
  | conj p q ihp ihq => exact congrArg₂ Pattern.conj ihp ihq
  | ex bound body ih => exact congrArg (Pattern.ex bound) ih
end Pattern

namespace SignatureMap
variable {A} {B C : Signature S}
def reduct (f : A ⟶ B) (M : Model B) : Model A :=
  ⟨M.carrier, M.nonempty, fun op args => M.operation (f.operations op) args⟩
def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := ⟨h.map, fun op args result member => h.operation (f.operations op) args result member⟩
  map_id _ := Model.Hom.ext _ _ rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl

theorem denote_map (f : A ⟶ B) (M : Model B) {k : Nat} {Γ : Fin k → S} {s : S} (p : Pattern (k := k) A Γ s) :
    ∀ v : (i : Fin k) → M.carrier (Γ i),
      M.denote v (Pattern.map f p) = (reduct f M).denote v p := by
  induction p with
  | var => intro v; rfl
  | app op args ih => intro v; simp only [Pattern.map, Model.denote, ih]; rfl
  | neg p ih => intro v; exact congrArg (fun x => xᶜ) (ih v)
  | conj p q ihp ihq => intro v; exact congrArg₂ Set.inter (ihp v) (ihq v)
  | ex bound body ih => intro v; simp only [Pattern.map, Model.denote, ih]; rfl

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
end SignatureMap

/-- A pattern together with its finite free-variable context and result sort. -/
structure Sentence where
  variableCount : Nat
  context : Fin variableCount → S
  sort : S
  pattern : Pattern A context sort
namespace Sentence
variable {A} {B C : Signature S}
def map (f : A ⟶ B) (p : Sentence A) : Sentence B :=
  ⟨p.variableCount,p.context,p.sort,Pattern.map f p.pattern⟩
/-- Definition 2.5: every result matches, under every element valuation. -/
def Satisfies (M : Model A) (p : Sentence A) : Prop :=
  ∀ v : (i : Fin p.variableCount) → M.carrier (p.context i),
    ∀ result : M.carrier p.sort, result ∈ M.denote v p.pattern
@[simp] theorem map_id (p : Sentence A) : map (𝟙 A) p = p := by cases p; simp [map]
@[simp] theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    map (f ≫ g) p = map g (map f p) := by cases p; simp [map]
theorem satisfaction (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Satisfies M (map f p) ↔ Satisfies (SignatureMap.reduct f M) p := by
  simp only [Satisfies,map,SignatureMap.denote_map]
  rfl
end Sentence

def institution (S : Type) : Signature S ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, SignatureMap.reductFunctor f, Sentence.satisfaction f⟩
  map_id _ := by
    apply Room.hom_ext
    · funext p; exact Sentence.map_id p
    · exact SignatureMap.reductFunctor_id
  map_comp f g := by
    apply Room.hom_ext
    · funext p; exact Sentence.map_comp f g p
    · exact SignatureMap.reductFunctor_comp f g
abbrev Presentation (S : Type) := Silmaril.Logic.Institution.Presentation (institution S)
abbrev Theory (S : Type) := Silmaril.Logic.Institution.Theory (institution S)
/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst (S : Type) := (⟨Signature S, institution S⟩ : Silmaril.Logic.Institution.Inst)
end Silmaril.Logic.Matching.FirstOrder
