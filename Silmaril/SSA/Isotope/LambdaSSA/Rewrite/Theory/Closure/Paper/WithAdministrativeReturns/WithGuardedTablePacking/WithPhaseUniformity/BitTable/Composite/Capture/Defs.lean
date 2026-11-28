module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Defs

/-! # A written row that keeps its first reply across the second request

`capProgram l₁ l₂` is one written program. It sends the request `l₁` with
the state as query. On the left reply it sends the request `l₂` with the
first reply's payload as query. On the second left reply it returns the
first reply's payload, which it has kept across the second request. On
the second right reply it repeats with the second payload. On the first
right reply it repeats with the first payload.

`capSecond l₂` is the second step with the kept Bit as its state: it
sends `l₂` with its state as query, returns its state on the left reply
and repeats with the reply on the right.

`entryProgram l₁ l₂` has the same two requests, but its second left
reply returns the state the row was entered with, kept across both
requests.

`fixRegion c` replaces a returned payload by the constant `c`, written
with literal unit, and keeps a repeat.

`keptRegions r y` are the four result regions of a labelled request that
stand for the results of `capSecond` entered with the constant `y`: the
left reply takes the result at `y` whatever its payload is.

`selSource sel` is a table of literal request trees. After the second
left reply with payload `y'`, having kept the first payload `y`, it acts
on `sel y y'`. `capSource` uses the kept payload. `duoSource` of the
two-request program uses the second payload.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

variable {K : Nat}

/-! ## The written program -/

/-- The second step. Its state is the kept Bit. -/
def capSecond (l₂ : Bool) : Program := .ask l₂ (.read 0) (.ret 0 1) (.ret 1 0)

/-- Two requests in one written program. The left leaf of the second
request returns the payload of the first reply. -/
def capProgram (l₁ l₂ : Bool) : Program :=
  .ask l₁ (.read 0) (.ask l₂ (.read 0) (.ret 0 1) (.ret 1 0)) (.ret 1 0)

/-- The same two requests, but the left leaf of the second request
returns the state the row was entered with, kept across both requests. -/
def entryProgram (l₁ l₂ : Bool) : Program :=
  .ask l₁ (.read 0) (.ask l₂ (.read 0) (.ret 0 2) (.ret 1 0)) (.ret 1 0)

/-- A router table all of whose rows are such programs. -/
def capRouter (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) : Router K :=
  ⟨fun i => capProgram (l₁ i) (l₂ i), act⟩

/-- The same table with the second step still a written program. Its
query is the kept Bit. -/
def capCarried (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) : TreeTable K :=
  ⟨fun i => (labelPoll (l₁ i)).program, fun i => duoKids K (capSecond (l₂ i)) (act i)⟩

/-! ## The kept Bit as a constant -/

/-- A Bit constant that uses no variable. -/
def litBit (c : Bool) : Tm signature.Instr :=
  match c with
  | false => .inl .unit
  | true => .inr .unit

theorem litBit_typed (c : Bool) : Tm.BranchValue [Bit] (litBit c) Bit := by
  cases c
  · exact .inl .unit
  · exact .inr .unit

theorem litLeft_typed (c : Bool) :
    ValueBranches [Bit] (.br 0 (.inl (litBit c)) : Region signature.Instr) [Silmaril.coprod Bit State] :=
  .br rfl (.inl (litBit_typed c))

/-- Replace a returned payload by the constant `c` and keep a repeat. -/
def fixRegion (c : Bool) : Region signature.Instr :=
  .case (.var 0) ((Region.br 0 (.inl (litBit c))).renameVars (lift Nat.succ))
    ((Region.br 0 (.inr (.var 0))).renameVars (lift Nat.succ))

theorem fix_typed (c : Bool) :
    ValueBranches [Silmaril.coprod Bit State] (fixRegion c) [Silmaril.coprod Bit State] :=
  caseValueBranches (litLeft_typed c) keep_typed

/-- The results of a labelled request that stand for the results of
`capSecond` entered with the constant `y`. -/
def keptRegions (r : Bool → Bool → Region signature.Instr) (y x' y' : Bool) : Region signature.Instr :=
  match x' with
  | false => r false y
  | true => r true y'

theorem kept_typed {r : Bool → Bool → Region signature.Instr}
    (h : ∀ x y, ValueBranches [Ty.unit] (r x y) [Silmaril.coprod Bit (States K)]) (y x' y' : Bool) :
    ValueBranches [Ty.unit] (keptRegions r y x' y') [Silmaril.coprod Bit (States K)] := by
  cases x'
  · exact h false y
  · exact h true y'

/-- The same choice on trees. -/
def keptKids (kids : Bool → Bool → Tree K) (y x' y' : Bool) : Tree K :=
  match x' with
  | false => kids false y
  | true => kids true y'

/-! ## Literal request trees -/

/-- The action after the second reply `(x', y')` with `y` kept. -/
def selAct (a : Bool → Bool → Act K) (sel : Bool → Bool → Bool) (y x' y' : Bool) : Act K :=
  match x' with
  | false => a false (sel y y')
  | true => a true y'

def selKids (K : Nat) (l₂ : Bool) (a : Bool → Bool → Act K) (sel : Bool → Bool → Bool) (x y : Bool) :
    LTree K :=
  match x with
  | false => .ask y l₂ fun x' y' => .leaf (selAct a sel y x' y')
  | true => .leaf (a true y)

/-- A table of literal request trees whose second left reply acts on
`sel y y'`. -/
def selSource (sel : Bool → Bool → Bool) (l₁ l₂ : Fin (K + 1) → Bool)
    (act : Fin (K + 1) → Bool → Bool → Act K) : LTable K :=
  ⟨l₁, fun i => selKids K (l₂ i) (act i) sel⟩

/-- Use the kept first payload. -/
def keepFirst (y _ : Bool) : Bool := y

/-- Use the second payload. The kept Bit is erased. -/
def useSecond (_ y' : Bool) : Bool := y'

/-- Use the negation of the kept payload. -/
def flipFirst (y _ : Bool) : Bool := !y

/-- The table of `capProgram` rows written as literal request trees. -/
def capSource (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) : LTable K :=
  selSource keepFirst l₁ l₂ act

/-! ## Regression tables -/

/-- One row: return the Bit it is given, or repeat. -/
def echoAct (_ : Fin 1) (x y : Bool) : Act 0 :=
  match x with
  | false => .ret y
  | true => .go 0 y

/-- The second request as two explicit states, one for each kept Bit,
in front of the row. -/
def selExplicitAct (sel : Bool → Bool → Bool) (j : Fin 3) (x y : Bool) : Act 2 :=
  match j, x, y with
  | 0, false, y => .ret (sel false y)
  | 0, true, y => .go 2 y
  | 1, false, y => .ret (sel true y)
  | 1, true, y => .go 2 y
  | 2, false, false => .go 0 false
  | 2, false, true => .go 1 true
  | 2, true, y => .go 2 y

def selExplicitLabel (l₁ l₂ : Bool) (j : Fin 3) : Bool :=
  match j with
  | 0 => l₂
  | 1 => l₂
  | 2 => l₁

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
