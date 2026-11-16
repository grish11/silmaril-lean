module

public import Silmaril.Logic.Prolog.Definite.Thms
public import Silmaril.Logic.Egg.Core.Defs

@[expose] public section

namespace Silmaril.Logic.Egglog.Core

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Constructors are total operations. Custom functions are partial tables with a declared
input profile and output sort. Relations have no output column. -/
structure Signature extends toFOL : FOL.Signature where
  Function : (n : Nat) → (Fin n → S) → S → Type

structure Signature.Hom (S T : Signature) extends toFOL : FOL.Signature.Hom S.toFOL T.toFOL where
  functions : ∀ {n w s}, S.Function n w s → T.Function n (sorts ∘ w) (sorts s)

instance : Category Signature where
  Hom := Signature.Hom
  id _ := { sorts := id, ops := fun o => o, rels := fun r => r, functions := fun f => f }
  comp f g :=
    { sorts := g.sorts ∘ f.sorts
      ops := fun o => g.ops (f.ops o)
      rels := fun r => g.rels (f.rels r)
      functions := fun t => g.functions (f.functions t) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- An equality-table model. Rows are genuinely partial; functionality allows at most one
result, not necessarily a result. Constructor interpretations need not be injective or disjoint. -/
structure Model (S : Signature) extends toFOL : FOL.Structure S.toFOL where
  row : ∀ {n w s}, S.Function n w s → (∀ i, carrier (w i)) → carrier s → Prop
  functional : ∀ {n w s} (f : S.Function n w s) args x y, row f args x → row f args y → x = y

structure Model.Hom {S : Signature} (M N : Model S) where
  map : ∀ s, M.carrier s → N.carrier s
  map_op : ∀ {n w s} (o : S.Op n w s) args,
    map s (M.op o args) = N.op o (fun i => map (w i) (args i))
  map_rel : ∀ {n w} (r : S.Rel n w) args, M.rel r args →
    N.rel r (fun i => map (w i) (args i))
  row : ∀ {n w s} (f : S.Function n w s) args x, M.row f args x →
    N.row f (fun i => map (w i) (args i)) (map s x)

@[ext] theorem Model.Hom.ext {S : Signature} {M N : Model S} (f g : Model.Hom M N)
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance {S : Signature} : Category (Model S) where
  Hom := Model.Hom
  id _ :=
    { map := fun _ x => x
      map_op := fun _ _ => rfl
      map_rel := fun _ _ h => h
      row := fun _ _ _ h => h }
  comp f g :=
    { map := fun s x => g.map s (f.map s x)
      map_op := fun o args => by rw [f.map_op, g.map_op]
      map_rel := fun r args h => g.map_rel r _ (f.map_rel r args h)
      row := fun t args x h => g.row t _ _ (f.row t args x h) }
  id_comp f := Model.Hom.ext _ _ rfl
  comp_id f := Model.Hom.ext _ _ rfl
  assoc f g h := Model.Hom.ext _ _ rfl

def Model.reduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj M :=
    { carrier := fun s => M.carrier (f.sorts s)
      op := fun o => M.op (f.ops o)
      rel := fun r => M.rel (f.rels r)
      row := fun t => M.row (f.functions t)
      functional := fun t args x y => M.functional (f.functions t) args x y }
  map h :=
    { map := fun s => h.map (f.sorts s)
      map_op := fun o => h.map_op (f.ops o)
      map_rel := fun r => h.map_rel (f.rels r)
      row := fun t => h.row (f.functions t) }

/-- Relational normalization of egglog queries. A partial expression call contributes a row
atom; it is not silently turned into a total constructor. -/
inductive Atom (S : Signature) {k : Nat} (Γ : Fin k → S.S) where
  | equal (e : Silmaril.Logic.Egg.Core.Equality S.toSignature Γ)
  | relation {n w} (r : S.Rel n w) (args : ∀ i, EQ.Term S.toSignature Γ (w i))
  | row {n w s} (f : S.Function n w s) (args : ∀ i, EQ.Term S.toSignature Γ (w i))
      (value : EQ.Term S.toSignature Γ s)

namespace Atom
variable {S T U : Signature} {k : Nat} {Γ : Fin k → S.S}

def Holds (M : Model S) (ρ : ∀ i, M.carrier (Γ i)) : Atom S Γ → Prop
  | .equal e => e.Holds M.toAlgebra ρ
  | .relation r args => M.rel r (fun i => (args i).eval M.toAlgebra ρ)
  | .row f args value => M.row f (fun i => (args i).eval M.toAlgebra ρ)
      (value.eval M.toAlgebra ρ)

def map (f : S ⟶ T) : Atom S Γ → Atom T (f.sorts ∘ Γ)
  | .equal e => .equal (e.map f.toHom)
  | .relation r args => .relation (f.rels r) (fun i => (args i).map f.toHom)
  | .row t args value => .row (f.functions t) (fun i => (args i).map f.toHom)
      (value.map f.toHom)

@[simp] theorem map_id (a : Atom S Γ) : a.map (𝟙 S) = a := by
  cases a with
  | equal e => exact congrArg Atom.equal (Silmaril.Logic.Egg.Core.Equality.map_id e)
  | relation r args =>
    exact congrArg (Atom.relation r) (funext (fun i => EQ.Term.map_id (args i)))
  | row t args value =>
    exact congrArg₂ (Atom.row t) (funext (fun i => EQ.Term.map_id (args i))) (EQ.Term.map_id value)

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (a : Atom S Γ) :
    a.map (f ≫ g) = (a.map f).map g := by
  cases a with
  | equal e => exact congrArg Atom.equal (Silmaril.Logic.Egg.Core.Equality.map_comp f.toHom g.toHom e)
  | relation r args =>
    exact congrArg (Atom.relation (g.rels (f.rels r)))
      (funext (fun i => EQ.Term.map_comp f.toHom g.toHom (args i)))
  | row t args value =>
    exact congrArg₂ (Atom.row (g.functions (f.functions t)))
      (funext (fun i => EQ.Term.map_comp f.toHom g.toHom (args i)))
      (EQ.Term.map_comp f.toHom g.toHom value)

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T)
    (ρ : ∀ i, M.carrier (f.sorts (Γ i))) (a : Atom S Γ) :
    (a.map f).Holds M ρ ↔ a.Holds ((Model.reduct f).obj M) ρ := by
  cases a <;> simp only [map, Holds, Silmaril.Logic.Egg.Core.Equality.holds_map, EQ.Term.eval_map] <;> rfl
end Atom

/-- A normalized rule has positive queries and one insert/set/union conclusion.
A multi-action rule is represented by one clause per conclusion, with explicit action-local
bindings normalized into terms/rows. This is not a proof of the raw frontend transformation. -/
structure Rule (S : Signature) where
  scope : Nat
  context : Fin scope → S.S
  body : List (Atom S context)
  head : Atom S context

namespace Rule
variable {S T U : Signature}

def Holds (M : Model S) (r : Rule S) : Prop :=
  ∀ ρ, (∀ a ∈ r.body, a.Holds M ρ) → r.head.Holds M ρ

def map (f : S ⟶ T) (r : Rule S) : Rule T :=
  ⟨r.scope, f.sorts ∘ r.context, r.body.map (Atom.map f), r.head.map f⟩

@[simp] theorem map_id (r : Rule S) : r.map (𝟙 S) = r := by
  have hm : (Atom.map (𝟙 S) : Atom S r.context → _) = id := funext Atom.map_id
  cases r
  simp only [map, hm, List.map_id, Atom.map_id]
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (r : Rule S) :
    r.map (f ≫ g) = (r.map f).map g := by
  have hm : (Atom.map (f ≫ g) : Atom S r.context → _) = Atom.map g ∘ Atom.map f :=
    funext (Atom.map_comp f g)
  cases r
  simp only [map, hm, List.map_map, Atom.map_comp]
  rfl

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T) (r : Rule S) :
    (r.map f).Holds M ↔ r.Holds ((Model.reduct f).obj M) := by
  constructor
  · intro h ρ hb
    apply (Atom.holds_map f M ρ r.head).mp
    apply h ρ
    intro a ha
    obtain ⟨original, ho, heq⟩ := List.mem_map.mp ha
    subst a
    exact (Atom.holds_map f M ρ original).mpr (hb original ho)
  · intro h ρ hb
    apply (Atom.holds_map f M ρ r.head).mpr
    apply h ρ
    intro a ha
    exact (Atom.holds_map f M ρ a).mp (hb _ (List.mem_map.mpr ⟨a,ha,rfl⟩))
end Rule

/-- Query variables, including unused ones, are existential. Partial calls remain row goals. -/
structure Query (S : Signature) where
  scope : Nat
  context : Fin scope → S.S
  goals : List (Atom S context)

namespace Query
variable {S T U : Signature}

def Holds (M : Model S) (q : Query S) : Prop :=
  ∃ ρ, ∀ a ∈ q.goals, a.Holds M ρ

def map (f : S ⟶ T) (q : Query S) : Query T :=
  ⟨q.scope, f.sorts ∘ q.context, q.goals.map (Atom.map f)⟩

@[simp] theorem map_id (q : Query S) : q.map (𝟙 S) = q := by
  have hm : (Atom.map (𝟙 S) : Atom S q.context → _) = id := funext Atom.map_id
  cases q
  simp only [map, hm, List.map_id]
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (q : Query S) :
    q.map (f ≫ g) = (q.map f).map g := by
  have hm : (Atom.map (f ≫ g) : Atom S q.context → _) = Atom.map g ∘ Atom.map f :=
    funext (Atom.map_comp f g)
  cases q
  simp only [map, hm, List.map_map]
  rfl

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T) (q : Query S) :
    (q.map f).Holds M ↔ q.Holds ((Model.reduct f).obj M) := by
  apply exists_congr
  intro ρ
  constructor
  · intro h a ha
    exact (Atom.holds_map f M ρ a).mp (h _ (List.mem_map.mpr ⟨a,ha,rfl⟩))
  · intro h a ha
    obtain ⟨original, ho, heq⟩ := List.mem_map.mp ha
    subst a
    exact (Atom.holds_map f M ρ original).mpr (h original ho)
end Query

inductive Sentence (S : Signature) where
  | rule : Rule S → Sentence S
  | query : Query S → Sentence S

namespace Sentence
variable {S T U : Signature}

def Holds (M : Model S) : Sentence S → Prop
  | .rule r => r.Holds M
  | .query q => q.Holds M

def map (f : S ⟶ T) : Sentence S → Sentence T
  | .rule r => .rule (r.map f)
  | .query q => .query (q.map f)

@[simp] theorem map_id (s : Sentence S) : s.map (𝟙 S) = s := by
  cases s <;> simp only [map, Rule.map_id, Query.map_id]

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (s : Sentence S) :
    s.map (f ≫ g) = (s.map f).map g := by
  cases s <;> simp only [map, Rule.map_comp, Query.map_comp]

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T) (s : Sentence S) :
    (s.map f).Holds M ↔ s.Holds ((Model.reduct f).obj M) := by
  cases s with
  | rule r => exact Rule.holds_map f M r
  | query q => exact Query.holds_map f M q
end Sentence

def room (S : Signature) : Room.{0,0,1} := ⟨Sentence S, Cat.of (Model S), fun M s => s.Holds M⟩

def corridor {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨Sentence.map f, Model.reduct f, Sentence.holds_map f⟩

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext Sentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

end Silmaril.Logic.Egglog.Core
