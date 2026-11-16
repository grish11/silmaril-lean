module

public import Silmaril.Logic.Institution.Borrowing
public import Mathlib.Order.FixedPoints

/-! Propositional classical separation logic over arbitrary relational partial
commutative monoids. Recursive occurrences will be positive by construction.
No finite-heap, parameter-passing or step-indexed Iris semantics is assumed. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation
open CategoryTheory Silmaril.Logic.Institution

structure Resource where
  carrier : Type
  unit : carrier
  join : carrier → carrier → carrier → Prop
  functional : ∀ {a b c d}, join a b c → join a b d → c = d
  unit_join : ∀ a b, join unit a b ↔ a = b
  comm : ∀ a b c, join a b c ↔ join b a c
  assoc : ∀ a b c d,
    (∃ ab, join a b ab ∧ join ab c d) ↔ ∃ bc, join b c bc ∧ join a bc d

structure Signature where
  Atom : Type

instance : Category Signature where
  Hom A B := A.Atom → B.Atom
  id _ := id
  comp f g := g ∘ f

structure Model (A : Signature) where
  resource : Resource
  atom : A.Atom → Set resource.carrier

structure Model.Hom {A : Signature} (M N : Model A) where
  map : M.resource.carrier → N.resource.carrier
  unit : map M.resource.unit = N.resource.unit
  join : ∀ {a b c}, M.resource.join a b c → N.resource.join (map a) (map b) (map c)
  atom : ∀ a {h}, h ∈ M.atom a → map h ∈ N.atom a

@[ext] theorem Model.Hom.ext {A : Signature} {M N : Model A} (f g : Model.Hom M N)
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

def Model.Hom.id {A : Signature} (M : Model A) : Model.Hom M M :=
  ⟨(fun x => x), rfl, fun {_ _ _} h => h, fun _ {_} h => h⟩

def Model.Hom.comp {A : Signature} {M N P : Model A} (f : Model.Hom M N) (g : Model.Hom N P) :
    Model.Hom M P where
  map := g.map ∘ f.map
  unit := by change g.map (f.map M.resource.unit) = _; rw [f.unit, g.unit]
  join h := g.join (f.join h)
  atom a {_} h := g.atom a (f.atom a h)

instance (A : Signature) : Category (Model A) where
  Hom := Model.Hom
  id := Model.Hom.id
  comp := Model.Hom.comp
  id_comp _ := Model.Hom.ext _ _ rfl
  comp_id _ := Model.Hom.ext _ _ rfl
  assoc _ _ _ := Model.Hom.ext _ _ rfl

variable {A B C : Signature}

def reduct (f : A ⟶ B) (M : Model B) : Model A := ⟨M.resource, M.atom ∘ f⟩

def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := ⟨h.map, h.unit, h.join, fun a => h.atom (f a)⟩
  map_id _ := Model.Hom.ext _ _ rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl

private theorem hom_hext {M M' N N' : Model A} (hm : M = M') (hn : N = N')
    (f : Model.Hom M N) (g : Model.Hom M' N') (h : HEq f.map g.map) : HEq f g := by
  cases hm; cases hn
  exact heq_of_eq (Model.Hom.ext _ _ (eq_of_heq h))

theorem reduct_id (M : Model A) : reduct (𝟙 A) M = M := by cases M; rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext reduct_id
  intro M N h
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl

def Resource.sep (R : Resource) (P Q : Set R.carrier) : Set R.carrier :=
  {h | ∃ a b, R.join a b h ∧ a ∈ P ∧ b ∈ Q}

def Resource.wand (R : Resource) (P Q : Set R.carrier) : Set R.carrier :=
  {h | ∀ a b, R.join h a b → a ∈ P → b ∈ Q}

inductive Assertion (A : Signature) where
  | atom : A.Atom → Assertion A
  | emp : Assertion A
  | neg : Assertion A → Assertion A
  | conj : Assertion A → Assertion A → Assertion A
  | sep : Assertion A → Assertion A → Assertion A
  | wand : Assertion A → Assertion A → Assertion A

def Assertion.map (f : A ⟶ B) : Assertion A → Assertion B
  | .atom a => .atom (f a)
  | .emp => .emp
  | .neg p => .neg (p.map f)
  | .conj p q => .conj (p.map f) (q.map f)
  | .sep p q => .sep (p.map f) (q.map f)
  | .wand p q => .wand (p.map f) (q.map f)

def Assertion.denote (M : Model A) : Assertion A → Set M.resource.carrier
  | .atom a => M.atom a
  | .emp => {M.resource.unit}
  | .neg p => (p.denote M)ᶜ
  | .conj p q => p.denote M ∩ q.denote M
  | .sep p q => M.resource.sep (p.denote M) (q.denote M)
  | .wand p q => M.resource.wand (p.denote M) (q.denote M)

def Assertion.Satisfies (M : Model A) (p : Assertion A) : Prop := ∀ h, h ∈ p.denote M

/-- Recursion is positive. Wand antecedents are recursion-independent. -/
inductive Pattern (A : Signature) : Nat → Type where
  | base {r} : Assertion A → Pattern A r
  | var {r} : Fin r → Pattern A r
  | conj {r} : Pattern A r → Pattern A r → Pattern A r
  | disj {r} : Pattern A r → Pattern A r → Pattern A r
  | sep {r} : Pattern A r → Pattern A r → Pattern A r
  | wand {r} : Assertion A → Pattern A r → Pattern A r
  | mu {r} : Pattern A (r+1) → Pattern A r

abbrev Env (M : Model A) (r : Nat) := Fin r → Set M.resource.carrier

def insert (M : Model A) {r} (η : Env M r) : Set M.resource.carrier →o Env M (r+1) where
  toFun X := Fin.cases X η
  monotone' := fun _ _ h i => Fin.cases h (fun _ => le_rfl) i

theorem Resource.sep_mono (R : Resource) {P Q P' Q' : Set R.carrier} (hp : P ⊆ P') (hq : Q ⊆ Q') :
    R.sep P Q ⊆ R.sep P' Q' := fun _ ⟨a,b,h,ha,hb⟩ => ⟨a,b,h,hp ha,hq hb⟩

theorem Resource.wand_mono (R : Resource) (P : Set R.carrier) {Q Q' : Set R.carrier} (hq : Q ⊆ Q') :
    R.wand P Q ⊆ R.wand P Q' := fun _ h a b hj ha => hq (h a b hj ha)

/-- Independent monotone heap-predicate semantics; μ is the actual least fixed point. -/
def Pattern.denote (M : Model A) {r} (p : Pattern A r) : Env M r →o Set M.resource.carrier := by
  induction p with
  | base p => exact ⟨fun _ => p.denote M, fun _ _ _ => le_rfl⟩
  | var i => exact ⟨fun η => η i, fun _ _ h => h i⟩
  | conj p q dp dq => exact ⟨fun η => dp η ∩ dq η, fun _ _ h _ hx => ⟨dp.monotone h hx.1, dq.monotone h hx.2⟩⟩
  | disj p q dp dq => exact ⟨fun η => dp η ∪ dq η, fun _ _ h _ hx => hx.elim (fun hp => Or.inl (dp.monotone h hp)) (fun hq => Or.inr (dq.monotone h hq))⟩
  | sep p q dp dq => exact ⟨fun η => M.resource.sep (dp η) (dq η), fun _ _ h => M.resource.sep_mono (dp.monotone h) (dq.monotone h)⟩
  | wand p q dq => exact ⟨fun η => M.resource.wand (p.denote M) (dq η), fun _ _ h => M.resource.wand_mono _ (dq.monotone h)⟩
  | mu body dp => exact ⟨fun η => (dp.comp (insert M η)).lfp, by
      intro η ζ h
      apply OrderHom.lfp.monotone
      intro X
      exact dp.monotone (fun i => Fin.cases le_rfl (fun j => h j) i)⟩

def Pattern.map (f : A ⟶ B) {r} : Pattern A r → Pattern B r
  | .base p => .base (p.map f)
  | .var i => .var i
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)
  | .sep p q => .sep (p.map f) (q.map f)
  | .wand p q => .wand (p.map f) (q.map f)
  | .mu p => .mu (p.map f)

def Pattern.Satisfies (M : Model A) (p : Pattern A 0) : Prop :=
  ∀ h, h ∈ p.denote M (fun i => i.elim0)

end Silmaril.Logic.Separation
