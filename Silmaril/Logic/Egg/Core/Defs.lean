module

public import Silmaril.Logic.Institution.Examples.Comorphisms

@[expose] public section

namespace Silmaril.Logic.Egg.Core

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Declared operators carry fixed arity, input sorts and output sort. -/
abbrev Signature := EQ.Signature
abbrev Model := EQ.Algebra

structure Equality (S : Signature) {n : Nat} (Γ : Fin n → S.S) where
  sort : S.S
  lhs : EQ.Term S Γ sort
  rhs : EQ.Term S Γ sort

namespace Equality
variable {S T U : Signature} {n : Nat} {Γ : Fin n → S.S}

def Holds (M : Model S) (ρ : ∀ i, M.carrier (Γ i)) (e : Equality S Γ) : Prop :=
  e.lhs.eval M ρ = e.rhs.eval M ρ

def map (f : S ⟶ T) (e : Equality S Γ) : Equality T (f.sorts ∘ Γ) :=
  ⟨f.sorts e.sort, e.lhs.map f, e.rhs.map f⟩

@[simp] theorem map_id (e : Equality S Γ) : e.map (𝟙 S) = e := by
  cases e
  simp only [map, EQ.Term.map_id]
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Equality S Γ) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [map, EQ.Term.map_comp]
  rfl

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T) (ρ : ∀ i, M.carrier (f.sorts (Γ i)))
    (e : Equality S Γ) : (e.map f).Holds M ρ ↔ e.Holds ((EQ.Algebra.reduct f).obj M) ρ := by
  simp only [Holds, map, EQ.Term.eval_map]
  rfl

def formula (e : Equality S Γ) : FOL.Formula (EQtoFOL.sig S) Γ := .eq e.lhs e.rhs

@[simp] theorem formula_map (f : S ⟶ T) (e : Equality S Γ) :
    (e.map f).formula = e.formula.map (EQtoFOL.sigFunctor.map f) := rfl
end Equality

/-- A declared rule is a conditional equation; search direction does not change its meaning.
Guard callbacks require their own justification before supplying these equality premises. -/
structure Rule (S : Signature) where
  scope : Nat
  context : Fin scope → S.S
  guards : List (Equality S context)
  conclusion : Equality S context

namespace Rule
variable {S T U : Signature}

def Holds (M : Model S) (r : Rule S) : Prop :=
  ∀ ρ, (∀ e ∈ r.guards, e.Holds M ρ) → r.conclusion.Holds M ρ

def map (f : S ⟶ T) (r : Rule S) : Rule T :=
  ⟨r.scope, f.sorts ∘ r.context, r.guards.map (Equality.map f), r.conclusion.map f⟩

@[simp] theorem map_id (r : Rule S) : r.map (𝟙 S) = r := by
  have hm : (Equality.map (𝟙 S) : Equality S r.context → _) = id :=
    funext Equality.map_id
  cases r
  simp only [map, hm, List.map_id, Equality.map_id]
  rfl

@[simp] theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (r : Rule S) :
    r.map (f ≫ g) = (r.map f).map g := by
  have hm : (Equality.map (f ≫ g) : Equality S r.context → _) =
      Equality.map g ∘ Equality.map f := funext (Equality.map_comp f g)
  cases r
  simp only [map, hm, List.map_map, Equality.map_comp]
  rfl

@[simp] theorem holds_map (f : S ⟶ T) (M : Model T) (r : Rule S) :
    (r.map f).Holds M ↔ r.Holds ((EQ.Algebra.reduct f).obj M) := by
  simp only [Holds, map]
  constructor
  · intro h ρ hg
    apply (Equality.holds_map f M ρ r.conclusion).mp
    apply h ρ
    intro e he
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp he
    subst e
    exact (Equality.holds_map f M ρ original).mpr (hg original horiginal)
  · intro h ρ hg
    apply (Equality.holds_map f M ρ r.conclusion).mpr
    apply h ρ
    intro e he
    exact (Equality.holds_map f M ρ e).mp (hg _ (List.mem_map.mpr ⟨e, he, rfl⟩))
end Rule

/-- A rule room uses actual algebras and algebra homomorphisms. -/
def room (S : Signature) : Room.{0,0,1} := ⟨Rule S, Cat.of (Model S), fun M r => r.Holds M⟩

def corridor {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨Rule.map f, EQ.Algebra.reduct f, Rule.holds_map f⟩

def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext Rule.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Rule.map_comp f g)) rfl

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

/-- Public equation syntax embeds as an unguarded rewrite declaration. -/
def ofEquation {S : Signature} (e : EQ.Equation S) : Rule S :=
  ⟨e.k, e.ctx, [], ⟨e.sort, e.lhs, e.rhs⟩⟩

theorem ofEquation_holds {S : Signature} (M : Model S) (e : EQ.Equation S) :
    (ofEquation e).Holds M ↔ e.Holds M := by
  constructor
  · intro h ρ
    exact h ρ (fun _ h => by cases h)
  · intro h ρ _
    exact h ρ

/-- Exact equation-to-rule comorphism: model data is retained. -/
def fromEquations : Inst.CoHom EQ.inst inst where
  Φ := 𝟭 _
  ρ :=
    { app := fun S => ⟨ofEquation, 𝟭 (EQ.room S).Mod, ofEquation_holds⟩
      naturality := by intro S T f; exact Room.hom_ext rfl rfl }

end Silmaril.Logic.Egg.Core
