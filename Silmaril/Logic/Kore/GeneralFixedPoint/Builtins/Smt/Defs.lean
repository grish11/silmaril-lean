module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Model.Defs
public import Silmaril.Logic.Smt.Uflia.Quantified.Variables

/-! Quantified characteristic formulas preserve genuinely set-valued children.
Free object variables become unary membership predicates, not singleton constants.
The target model boundary interprets those predicates by the source valuation. -/
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Smt

inductive ValueSort where
  | integer | boolean
  deriving DecidableEq, Repr

abbrev ValueSort.code : ValueSort → Uflia.SortCode Empty
  | .integer => .int
  | .boolean => .bool

abbrev ValueSort.Value (s : ValueSort) := (Uflia.Carriers.trivial Empty).value s.code

def ValueSort.name [b : SortBindings] : ValueSort → String
  | .integer => b.intSort
  | .boolean => b.boolSort

/-- Object-variable values may be arbitrary sets, including empty and nonsingleton sets. -/
abbrev Valuation := (s : ValueSort) → String → Set s.Value

inductive Pattern : ValueSort → Type where
  | variable (s : ValueSort) (name : String) : Pattern s
  | integer (value : Int) : Pattern .integer
  | boolean (value : Bool) : Pattern .boolean
  | top (s : ValueSort) : Pattern s
  | bottom (s : ValueSort) : Pattern s
  | neg {s} : Pattern s → Pattern s
  | conj {s} : Pattern s → Pattern s → Pattern s
  | disj {s} : Pattern s → Pattern s → Pattern s
  | intEq : Pattern .integer → Pattern .integer → Pattern .boolean
  | boolNot : Pattern .boolean → Pattern .boolean

def Pattern.denote (v : Valuation) : {s : ValueSort} → Pattern s → Set s.Value
  | _, .variable s name => v s name
  | _, .integer n => {n}
  | _, .boolean b => {b}
  | _, .top _ => Set.univ
  | _, .bottom _ => ∅
  | _, .neg p => (p.denote v)ᶜ
  | _, .conj p q => p.denote v ∩ q.denote v
  | _, .disj p q => p.denote v ∪ q.denote v
  | _, .intEq p q => {b | ∃ x ∈ p.denote v, ∃ y ∈ q.denote v,
      b = Operational.Conditional.intEqual x y}
  | _, .boolNot p => {b | ∃ x ∈ p.denote v, b = !x}

/-- Unary predicates encode the whole object-variable set. No new SMT syntax. -/
inductive Membership : (n : Nat) → (Fin n → Uflia.SortCode Empty) → Uflia.SortCode Empty → Type where
  | variable (s : ValueSort) (name : String) : Membership 1 (fun _ => s.code) .bool

def signature : Uflia.Signature Empty := ⟨Membership⟩

def target (v : Valuation) : Uflia.Model signature where
  carriers := Uflia.Carriers.trivial Empty
  operation := by
    classical
    exact fun op args => match op with
      | .variable s name => decide (args 0 ∈ v s name)

namespace Formula
variable {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}

def boolean (b : Bool) : Uflia.Quantified.Formula signature Γ := .app (.boolean b) (fun i => i.elim0)

def integer (n : Int) : Uflia.Quantified.Term signature Γ .int := .app (.integer n) (fun i => i.elim0)

def eq {s} (p q : Uflia.Quantified.Term signature Γ s) : Uflia.Quantified.Formula signature Γ :=
  .app (.eq s) (Fin.cases p (fun _ => q))

def neg (p : Uflia.Quantified.Formula signature Γ) : Uflia.Quantified.Formula signature Γ := .app .not (fun _ => p)

def conj (p q : Uflia.Quantified.Formula signature Γ) : Uflia.Quantified.Formula signature Γ :=
  .app .and (Fin.cases p (fun _ => q))

def disj (p q : Uflia.Quantified.Formula signature Γ) : Uflia.Quantified.Formula signature Γ :=
  .app .or (Fin.cases p (fun _ => q))
end Formula

/-- The distinguished output may be any target term. Witnesses are fresh bound
variables, so empty, universal and complemented hook children remain sound. -/
def Pattern.compile : {s : ValueSort} → Pattern s → {k : Nat} →
    {Γ : Fin k → Uflia.SortCode Empty} → Uflia.Quantified.Term signature Γ s.code → Uflia.Quantified.Formula signature Γ
  | _, .variable s name, _, _, out => .app (.uf (.variable s name)) (fun _ => out)
  | _, .integer n, _, _, out => Formula.eq out (Formula.integer n)
  | _, .boolean b, _, _, out => Formula.eq out (Formula.boolean b)
  | _, .top _, _, _, _ => Formula.boolean true
  | _, .bottom _, _, _, _ => Formula.boolean false
  | _, .neg p, _, _, out => Formula.neg (p.compile out)
  | _, .conj p q, _, _, out => Formula.conj (p.compile out) (q.compile out)
  | _, .disj p q, _, _, out => Formula.disj (p.compile out) (q.compile out)
  | _, .intEq p q, _, _, out => .ex .int (.ex .int
      (Formula.conj (p.compile (.var (Fin.succ 0))) (Formula.conj (q.compile (.var 0))
        (Formula.eq ((out.weaken .int).weaken .int) (Formula.eq (.var (Fin.succ 0)) (.var 0))))))
  | _, .boolNot p, _, _, out => .ex .bool
      (Formula.conj (p.compile (.var 0))
        (Formula.eq (out.weaken .bool) (Formula.neg (.var 0))))

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
