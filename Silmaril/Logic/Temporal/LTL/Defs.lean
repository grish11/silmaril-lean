module

public import Silmaril.Logic.Institution.Examples.Comorphisms

/-!
# Linear temporal logic on infinite traces

The time domain is Nat with its usual successor. Until is strong until: its
right operand must eventually hold. Models are infinite traces, not transition
systems with an implicit path quantifier. CTL and CTL* require separate model
and sentence interfaces. Atom renamings act on the complete trace.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.LTL

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

variable {P Q R : Type}

inductive Formula (P : Type) where
  | atom : P → Formula P
  | bot : Formula P
  | not : Formula P → Formula P
  | imp : Formula P → Formula P → Formula P
  | and : Formula P → Formula P → Formula P
  | or : Formula P → Formula P → Formula P
  | next : Formula P → Formula P
  | until : Formula P → Formula P → Formula P

namespace Formula

def top : Formula P := .not .bot
def eventually (p : Formula P) : Formula P := .until top p
def always (p : Formula P) : Formula P := .not (eventually (.not p))
def release (p q : Formula P) : Formula P := .not (.until (.not p) (.not q))
def weakUntil (p q : Formula P) : Formula P := .or (.until p q) (always p)

def map (f : P → Q) : Formula P → Formula Q
  | .atom p => .atom (f p)
  | .bot => .bot
  | .not p => .not (p.map f)
  | .imp p q => .imp (p.map f) (q.map f)
  | .and p q => .and (p.map f) (q.map f)
  | .or p q => .or (p.map f) (q.map f)
  | .next p => .next (p.map f)
  | .until p q => .until (p.map f) (q.map f)

end Formula

/-- A model gives the truth of every atom at every natural-number instant. -/
def Model (P : Type) : Type 1 := ULift.{1} (Nat → P → Prop)

def Model.val (M : Model P) : Nat → P → Prop := M.down

/-- Pointwise preservation of atom truth; no preservation of negation is assumed. -/
instance (P : Type) : Category.{0} (Model P) where
  Hom M N := PLift (∀ n p, M.val n p → N.val n p)
  id _ := ⟨fun _ _ h => h⟩
  comp f g := ⟨fun n p h => g.down n p (f.down n p h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def Model.reduct (f : P → Q) : Model Q ⥤ Model P where
  obj M := ULift.up (fun n p => M.val n (f p))
  map h := ⟨fun n p => h.down n (f p)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def Formula.Holds (M : Model P) : Formula P → Nat → Prop
  | .atom p, n => M.val n p
  | .bot, _ => False
  | .not p, n => ¬ p.Holds M n
  | .imp p q, n => p.Holds M n → q.Holds M n
  | .and p q, n => p.Holds M n ∧ q.Holds M n
  | .or p q, n => p.Holds M n ∨ q.Holds M n
  | .next p, n => p.Holds M (n + 1)
  | .until p q, n => ∃ d : Nat, q.Holds M (n + d) ∧
      ∀ i : Nat, i < d → p.Holds M (n + i)

def Sat (M : Model P) (p : Formula P) : Prop := p.Holds M 0

namespace Formula

@[simp] theorem map_id (p : Formula P) : p.map id = p := by
  induction p <;> simp_all only [map, id_eq]

@[simp] theorem map_comp (f : P → Q) (g : Q → R) (p : Formula P) :
    p.map (g ∘ f) = (p.map f).map g := by
  induction p <;> simp_all only [map, Function.comp_apply]

theorem holds_map (f : P → Q) (M : Model Q) (p : Formula P) (n : Nat) :
    (p.map f).Holds M n ↔ p.Holds ((Model.reduct f).obj M) n := by
  induction p generalizing n with
  | atom _ => rfl
  | bot => rfl
  | not p ih => exact not_congr (ih n)
  | imp p q hp hq => exact imp_congr (hp n) (hq n)
  | and p q hp hq => exact and_congr (hp n) (hq n)
  | or p q hp hq => exact or_congr (hp n) (hq n)
  | next p ih => exact ih (n + 1)
  | «until» p q hp hq =>
    exact exists_congr fun d => and_congr (hq (n + d))
      (forall_congr' fun i => imp_congr_right fun _ => hp (n + i))

end Formula

def room (P : Type) : Room.{0, 0, 1} := ⟨Formula P, Cat.of (Model P), Sat⟩

def corridor (f : P → Q) : room P ⟶ room Q :=
  ⟨Formula.map f, Model.reduct f, fun M p => p.holds_map f M 0⟩

def institution : Type ⥤ Room.{0, 0, 1} where
  obj := room
  map f := corridor f
  map_id _ := Room.hom_ext (funext Formula.map_id) rfl
  map_comp f g := Room.hom_ext (funext (Formula.map_comp f g)) rfl

def inst : Inst := ⟨Type, institution⟩

def encodePropositional : PL.Formula P → Formula P
  | .var p => .atom p
  | .bot => .bot
  | .imp p q => .imp (encodePropositional p) (encodePropositional q)
  | .and p q => .and (encodePropositional p) (encodePropositional q)
  | .or p q => .or (encodePropositional p) (encodePropositional q)

theorem encodePropositional_holds (M : Model P) (p : PL.Formula P) (n : Nat) :
    (encodePropositional p).Holds M n ↔ PL.Formula.eval (M.val n) p := by
  induction p with
  | var _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr hp hq
  | and p q hp hq => exact and_congr hp hq
  | or p q hp hq => exact or_congr hp hq

def initialValuation (P : Type) : Model P ⥤ PL.Model P where
  obj M := ULift.up (M.val 0)
  map h := ⟨fun p => h.down 0 p⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem encodePropositional_map (f : P → Q) (p : PL.Formula P) :
    encodePropositional (p.rename f) = (encodePropositional p).map f := by
  induction p <;> simp_all only [encodePropositional, PL.Formula.rename, Formula.map]

def propositionalNatural : PL.institution ⟶ institution where
  app P := ⟨encodePropositional, initialValuation P,
    fun M p => encodePropositional_holds M p 0⟩
  naturality := by
    intro P Q f
    exact Room.hom_ext (funext (encodePropositional_map f)) rfl

def propositionalToLtl : Inst.CoHom PL.inst inst :=
  ⟨𝟭 Type, propositionalNatural ≫ (Functor.leftUnitor institution).inv⟩

theorem propositionalToLtl_modelExpansive : propositionalToLtl.ModelExpansive := by
  intro P v
  refine ⟨(show Model P from ULift.up (fun (_ : Nat) => v.val)), ?_⟩
  cases v
  rfl

end Silmaril.Logic.Temporal.LTL
