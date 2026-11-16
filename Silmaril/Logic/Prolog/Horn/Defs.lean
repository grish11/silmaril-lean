module

public import Silmaril.Logic.Prolog.Definite.Defs

/-!
# Declarative constraint Horn programs

Positive equality and predicate premises imply an optional positive head.
An absent head means false, so integrity constraints and inconsistent theories
are expressible. Queries existentially close all context variables. Models and
all signature maps are the public many-sorted FOL types, including empty sorts.
This is classical declarative semantics, not operational Prolog search.
-/

@[expose] public section

namespace Silmaril.Logic.Prolog.Horn

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

abbrev Signature := FOL.Signature
abbrev Model := FOL.Structure

/-- A typed equality or a predicate atom in the same finite context. -/
inductive Atom (S : Signature) {k : Nat} (Γ : Fin k → S.S) where
  | equal (sort : S.S) (lhs rhs : EQ.Term S.toSignature Γ sort)
  | predicate (atom : Definite.Atom S Γ)

namespace Atom

variable {S T U : Signature} {k : Nat} {Γ : Fin k → S.S}

def formula : Atom S Γ → FOL.Formula S Γ
  | .equal _ lhs rhs => .eq lhs rhs
  | .predicate a => a.formula

def Holds (M : Model S) (ρ : ∀ i, M.carrier (Γ i)) (a : Atom S Γ) : Prop :=
  a.formula.Holds M ρ

def map (f : S ⟶ T) : Atom S Γ → Atom T (f.sorts ∘ Γ)
  | .equal sort lhs rhs => .equal (f.sorts sort) (lhs.map f.toHom) (rhs.map f.toHom)
  | .predicate a => .predicate (a.map f)

@[simp] theorem formula_map (f : S ⟶ T) (a : Atom S Γ) :
    (a.map f).formula = a.formula.map f := by cases a <;> rfl

@[simp] theorem map_id (a : Atom S Γ) : a.map (𝟙 S) = a := by
  cases a with
  | equal sort lhs rhs =>
    change Atom.equal sort (lhs.map (𝟙 S.toSignature)) (rhs.map (𝟙 S.toSignature)) = _
    simp only [EQ.Term.map_id]
  | predicate a => simp only [map, Definite.Atom.map_id]

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (a : Atom S Γ) :
    a.map (f ≫ g) = (a.map f).map g := by
  cases a with
  | equal sort lhs rhs =>
    change Atom.equal (g.sorts (f.sorts sort))
      (lhs.map (f.toHom ≫ g.toHom)) (rhs.map (f.toHom ≫ g.toHom)) = _
    simp only [EQ.Term.map_comp, map]
  | predicate a => simp only [map, Definite.Atom.map_comp]

theorem holds_map (f : S ⟶ T) (M : Model T)
    (ρ : ∀ i, M.carrier (f.sorts (Γ i))) (a : Atom S Γ) :
    (a.map f).Holds M ρ ↔ a.Holds ((FOL.Structure.reduct f).obj M) ρ := by
  unfold Holds
  rw [formula_map]
  exact FOL.Formula.holds_map f M a.formula ρ

end Atom

/-- An absent head is false; every context variable is universally quantified. -/
structure Clause (S : Signature) where
  scope : Nat
  context : Fin scope → S.S
  body : List (Atom S context)
  head : Option (Atom S context)

/-- Query variables are existentially quantified, including variables not in a goal. -/
structure Query (S : Signature) where
  scope : Nat
  context : Fin scope → S.S
  goals : List (Atom S context)

def conjunction {S : Signature} {k : Nat} {Γ : Fin k → S.S} :
    List (Atom S Γ) → FOL.Formula S Γ
  | [] => .tt
  | a :: rest => .and a.formula (conjunction rest)

theorem conjunction_holds {S : Signature} {k : Nat} {Γ : Fin k → S.S}
    (M : Model S) (ρ : ∀ i, M.carrier (Γ i)) (atoms : List (Atom S Γ)) :
    (conjunction atoms).Holds M ρ ↔ ∀ a ∈ atoms, a.Holds M ρ := by
  induction atoms with
  | nil => simp [conjunction, FOL.Formula.Holds]
  | cons a rest ih =>
    change (a.Holds M ρ ∧ (conjunction rest).Holds M ρ) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem conjunction_map {S T : Signature} (f : S ⟶ T) {k : Nat}
    {Γ : Fin k → S.S} (atoms : List (Atom S Γ)) :
    conjunction (atoms.map (Atom.map f)) = (conjunction atoms).map f := by
  induction atoms with
  | nil => rfl
  | cons a rest ih =>
    change FOL.Formula.and (a.map f).formula _ = FOL.Formula.and (a.formula.map f) _
    rw [Atom.formula_map, ih]

namespace Clause

variable {S T U : Signature}

def map (f : S ⟶ T) (c : Clause S) : Clause T :=
  ⟨c.scope, f.sorts ∘ c.context, c.body.map (Atom.map f), c.head.map (Atom.map f)⟩

def Holds (M : Model S) (c : Clause S) : Prop :=
  ∀ ρ : ∀ i, M.carrier (c.context i),
    (∀ a ∈ c.body, a.Holds M ρ) →
      match c.head with
      | none => False
      | some a => a.Holds M ρ

def headFormula {k : Nat} {Γ : Fin k → S.S} : Option (Atom S Γ) → FOL.Formula S Γ
  | none => .not .tt
  | some a => a.formula

@[simp] theorem headFormula_map (f : S ⟶ T) {k : Nat} {Γ : Fin k → S.S}
    (head : Option (Atom S Γ)) :
    headFormula (head.map (Atom.map f)) = (headFormula head).map f := by
  cases head with
  | none => rfl
  | some a => exact Atom.formula_map f a

/-- `body → head` is encoded as `¬(body ∧ ¬head)` before universal closure. -/
def encode (c : Clause S) : FOL.Sentence S :=
  EQtoFOL.closeAll c.context (.not (.and (conjunction c.body) (.not (headFormula c.head))))

@[simp] theorem map_id (c : Clause S) : c.map (𝟙 S) = c := by
  rcases c with ⟨n, Γ, body, head⟩
  have hm : @Atom.map S S n Γ (𝟙 S) = id := funext Atom.map_id
  simp only [map, hm, List.map_id, Option.map_id]
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (c : Clause S) :
    c.map (f ≫ g) = (c.map f).map g := by
  rcases c with ⟨n, Γ, body, head⟩
  have hm : @Atom.map S U n Γ (f ≫ g) = Atom.map g ∘ Atom.map f :=
    funext (Atom.map_comp f g)
  simp only [map, hm, List.map_map, Option.map_map]
  rfl

theorem encode_holds (M : Model S) (c : Clause S) : c.encode.Holds M ↔ c.Holds M := by
  classical
  cases hh : c.head <;>
    simp only [encode, EQtoFOL.holds_closeAll, FOL.Formula.Holds,
      conjunction_holds, headFormula, hh, Holds, Atom.Holds, not_and, not_not,
      not_true_eq_false, imp_false]

theorem encode_map (f : S ⟶ T) (c : Clause S) :
    (c.map f).encode = c.encode.map f := by
  rw [encode, encode, EQtoFOL.map_closeAll]
  exact congrArg (EQtoFOL.closeAll (f.sorts ∘ c.context))
    (congrArg FOL.Formula.not
      (congrArg₂ FOL.Formula.and (conjunction_map f c.body)
        (congrArg FOL.Formula.not (headFormula_map f c.head))))

theorem holds_map (f : S ⟶ T) (M : Model T) (c : Clause S) :
    (c.map f).Holds M ↔ c.Holds ((FOL.Structure.reduct f).obj M) := by
  rw [← encode_holds, encode_map, FOL.Sentence.holds_map, encode_holds]

end Clause

namespace Query

variable {S T U : Signature}

def map (f : S ⟶ T) (q : Query S) : Query T :=
  ⟨q.scope, f.sorts ∘ q.context, q.goals.map (Atom.map f)⟩

def Holds (M : Model S) (q : Query S) : Prop :=
  ∃ ρ : ∀ i, M.carrier (q.context i), ∀ a ∈ q.goals, a.Holds M ρ

/-- Existential closure is `¬∀ variables. ¬goals`, using classical semantics. -/
def encode (q : Query S) : FOL.Sentence S :=
  let closed := EQtoFOL.closeAll q.context (.not (conjunction q.goals))
  ⟨closed.ctx, .not closed.formula⟩

@[simp] theorem map_id (q : Query S) : q.map (𝟙 S) = q := by
  rcases q with ⟨n, Γ, goals⟩
  have hm : @Atom.map S S n Γ (𝟙 S) = id := funext Atom.map_id
  simp only [map, hm, List.map_id]
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (q : Query S) :
    q.map (f ≫ g) = (q.map f).map g := by
  rcases q with ⟨n, Γ, goals⟩
  have hm : @Atom.map S U n Γ (f ≫ g) = Atom.map g ∘ Atom.map f :=
    funext (Atom.map_comp f g)
  simp only [map, hm, List.map_map]
  rfl

theorem encode_holds (M : Model S) (q : Query S) : q.encode.Holds M ↔ q.Holds M := by
  classical
  change (¬ (EQtoFOL.closeAll q.context (.not (conjunction q.goals))).Holds M) ↔ _
  rw [EQtoFOL.holds_closeAll]
  change (¬ ∀ ρ, ¬ (conjunction q.goals).Holds M ρ) ↔ _
  rw [not_forall]
  apply exists_congr
  intro ρ
  exact not_not.trans (conjunction_holds M ρ q.goals)

theorem encode_map (f : S ⟶ T) (q : Query S) :
    (q.map f).encode = q.encode.map f := by
  have hc : EQtoFOL.closeAll (f.sorts ∘ q.context)
      (.not (conjunction (q.goals.map (Atom.map f)))) =
      (EQtoFOL.closeAll q.context (.not (conjunction q.goals))).map f := by
    rw [EQtoFOL.map_closeAll, conjunction_map]
    rfl
  exact congrArg (fun c : FOL.Sentence T => FOL.Sentence.mk c.ctx (.not c.formula)) hc

theorem holds_map (f : S ⟶ T) (M : Model T) (q : Query S) :
    (q.map f).Holds M ↔ q.Holds ((FOL.Structure.reduct f).obj M) := by
  rw [← encode_holds, encode_map, FOL.Sentence.holds_map, encode_holds]

end Query

/-- Clauses and existential queries share one model interface. -/
inductive Sentence (S : Signature) where
  | clause : Clause S → Sentence S
  | query : Query S → Sentence S

namespace Sentence

def map {S T : Signature} (f : S ⟶ T) : Sentence S → Sentence T
  | .clause c => .clause (c.map f)
  | .query q => .query (q.map f)

def Holds {S : Signature} (M : Model S) : Sentence S → Prop
  | .clause c => c.Holds M
  | .query q => q.Holds M

def encode {S : Signature} : Sentence S → FOL.Sentence S
  | .clause c => c.encode
  | .query q => q.encode

@[simp] theorem map_id {S : Signature} (s : Sentence S) : s.map (𝟙 S) = s := by
  cases s <;> simp only [map, Clause.map_id, Query.map_id]

@[simp] theorem map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (s : Sentence S) : s.map (f ≫ g) = (s.map f).map g := by
  cases s <;> simp only [map, Clause.map_comp, Query.map_comp]

theorem encode_holds {S : Signature} (M : Model S) (s : Sentence S) :
    s.encode.Holds M ↔ s.Holds M := by
  cases s with
  | clause c => exact c.encode_holds M
  | query q => exact q.encode_holds M

theorem encode_map {S T : Signature} (f : S ⟶ T) (s : Sentence S) :
    (s.map f).encode = s.encode.map f := by
  cases s with
  | clause c => exact c.encode_map f
  | query q => exact q.encode_map f

theorem holds_map {S T : Signature} (f : S ⟶ T) (M : Model T) (s : Sentence S) :
    (s.map f).Holds M ↔ s.Holds ((FOL.Structure.reduct f).obj M) := by
  rw [← encode_holds, encode_map, FOL.Sentence.holds_map, encode_holds]

end Sentence

def room (S : Signature) : Room.{0, 0, 1} :=
  ⟨Sentence S, Cat.of (Model S), fun M s => s.Holds M⟩

def corridor {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨Sentence.map f, FOL.Structure.reduct f, Sentence.holds_map f⟩

def institution : Signature ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id _S := Room.hom_ext (funext Sentence.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) rfl

def inst : Inst.{1, 0, 0, 0, 1} := ⟨Signature, institution⟩

/-- Universal clauses and existential queries translated to ordinary first-order logic. -/
def toFirstOrder : Inst.CoHom inst FOL.inst where
  Φ := 𝟭 _
  ρ :=
    { app := fun S => ⟨Sentence.encode, 𝟭 (FOL.room S).Mod, Sentence.encode_holds⟩
      naturality := by
        intro S T f
        exact Room.hom_ext (funext (Sentence.encode_map f)) rfl }

end Silmaril.Logic.Prolog.Horn
