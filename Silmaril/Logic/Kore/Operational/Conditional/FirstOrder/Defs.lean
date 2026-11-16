module

public import Silmaril.Logic.Kore.Operational.Conditional.Thms
public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Edge.Thms

/-! Actual FOL syntax for the selected conditional KORE profile. The signature
has only constructor and zero symbols; no operational or satisfaction relation
is installed. Each source rule contributes two token constants. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables

inductive FSort | state | code | integer | config
  deriving DecidableEq

/-- A finite family of symbols for each finite installed rule list. Token names
are interpreted from the source, and need not be distinct. -/
inductive Operation (rules : List Rule) : (n : Nat) → (Fin n → FSort) → FSort → Type
  | token (i : Fin rules.length) (right : Bool) : Operation rules 0 Fin.elim0 .state
  | zero : Operation rules 0 Fin.elim0 .integer
  | cons : Operation rules 2 (Fin.cases .state (fun _ => .code)) .code
  | config : Operation rules 3 (Fin.cases .code (Fin.cases .integer (fun _ => .integer))) .config

def signature (rules : List Rule) : FOL.Signature where
  S := FSort
  Op := Operation rules
  Rel := fun _ _ => Empty

def Carrier : FSort → Type
  | .state => String
  | .code => List String
  | .integer => Int
  | .config => Config

/-- Independent constructor interpretation; Step, rule satisfaction and formula
truth do not occur in this structure. Integer equality is actual equality. -/
def model (rules : List Rule) : FOL.Structure (signature rules) where
  carrier := Carrier
  op := fun op args => match op with
    | .token i right => if right then (rules.get i).after else (rules.get i).before
    | .zero => (0 : Int)
    | .cons => args 0 :: args 1
    | .config => ⟨args 0, args 1, args 2⟩
  rel := fun r => nomatch r

/-- Slots 1--4 after cfg0 are tail, x, capturedVal and counter. In particular
x and capturedVal are independent integer variables, not one shared slot. -/
def telescope : List FSort := [.code, .integer, .integer, .integer]

abbrev Term (rules : List Rule) (s : FSort) :=
  EQ.Term (signature rules).toSignature (Fin.cases FSort.config (blockContext emptyContext telescope)) s

def configTerm (rules : List Rule) (i : Fin rules.length) (right : Bool) : Term rules .config :=
  .app .config (Fin.cases
    (.app .cons (Fin.cases (.app (.token i right) (fun j => j.elim0)) (fun _ => .var 1)))
    (Fin.cases (if right then .var 3 else .var 2) (fun _ => .var 4)))

def guardFormula (rules : List Rule) : Guard → Reachability.Derivation.FirstOrder.RulePattern (Sg := signature rules) .config telescope
  | .zero => .eq (.var 2) (.app .zero (fun j => j.elim0))
  | .nonzero => .not (.eq (.var 2) (.app .zero (fun j => j.elim0)))

def formulaRule (rules : List Rule) (i : Fin rules.length) :
    Reachability.Derivation.FirstOrder.Step.FormulaRule (Sg := signature rules) .config where
  telescope := telescope
  lhs := .and (.eq (.var 2) (.var 3))
    (.and (guardFormula rules (rules.get i).guard) (.eq (.var 0) (configTerm rules i false)))
  rhs := .eq (.var 0) (configTerm rules i true)

def formulaRules (rules : List Rule) : Fin rules.length →
    Reachability.Derivation.FirstOrder.Step.FormulaRule (Sg := signature rules) .config := formulaRule rules

def encodeValuation (rules : List Rule) (v : Valuation) : BlockAssignment (model rules) telescope :=
  (v.tail, v.x, v.capturedVal, v.counter, ())

def decodeValuation (rules : List Rule) (b : BlockAssignment (model rules) telescope) : Valuation :=
  ⟨b.1, b.2.1, b.2.2.1, b.2.2.2.1⟩

def assignment (rules : List Rule) (v : Valuation) :=
  joinAssignment (model rules) (Γ := emptyContext) (fun i => i.elim0) telescope (encodeValuation rules v)

end Silmaril.Logic.Kore.Operational.Conditional.FirstOrder
