module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Bisimulation.Defs

/-! # Split states for rows that keep their entry state

`entryProgram l₁ l₂` keeps the state its row was entered with across both
of its requests. A table of such rows is `entryRouter`.

## Split states

Each row `j` gets two split states, `splitIdx j false` and
`splitIdx j true`, one for each entry Bit. `splitRow` and `splitBit` read
a split state back. `redirect` keeps an exit and sends a repeat that
carries the Bit `q` to row `j` to the split state `splitIdx j q`.

* `entrySplit`: the same written rows at the split states, with every
  repeat redirected.
* `entryDuo`: the split table with two-request programs, which keep
  nothing. The left return of a split state is its entry Bit, as a
  constant (`entryAct`).
* `entrySource`: `entryDuo` as literal request trees.
* `entryCase j`: `entrySource` entered by a case on the original state:
  the split state of `false` on `false`, of `true` on `true`.

## Resetting the query

`resetRegion q` replaces the tag of the state's Bit by `q`.
`resetRows c rows` resets the query of row `x` to `c x` before the row
runs. `Matched c h` says that every repeat of every row already carries
the Bit `c` assigns to its target. `Act.Carries c` is the same for one
action.

## Loops that are literal sources at each constant

`constEntry q r` is `r` entered with the constant state `q`.
`caseEntry r₀ r₁` enters `r₀` or `r₁` by a case on the state's Bit.
`Pointed r t x` says that `r` entered with each constant `q` equals the
table of literal request trees `t q` entered with `q` at `x q`, in the
opt-in quotient.

## Regression tables

`turnAct` returns the Bit it is given or repeats with the negated Bit.
`turnSource frozen` is its split table written out; when `frozen`, a
repeat stays in its copy. `turnExplicitAct` and `capTurnAct` write the
second requests as explicit router states.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)




theorem emptyState_typed :
    ValueBranches [Silmaril.empty] (.br 0 (.inr (.var 0)) : Region signature.Instr) [State] :=
  .br rfl (.inr (.var rfl))

/-- Replace the tag of the state's Bit by `q` and keep its unit payload. -/
def resetRegion (q : Bool) : Region signature.Instr :=
  .case (.var 0)
    ((pairSplit (.br 0 (.inl (bitTm q))) (.br 0 (.inl (bitTm q)))).renameVars (lift Nat.succ))
    ((Region.br 0 (.inr (.var 0))).renameVars (lift Nat.succ))

theorem reset_typed (q : Bool) : ValueBranches [State] (resetRegion q) [State] :=
  caseValueBranches (caseValueBranches (const_typed q) (const_typed q)) emptyState_typed

/-- The rows with their query reset to the Bit of their state. -/
def resetRows {M : Nat} (c : Fin (M + 1) → Bool) (rows : Fin (M + 1) → Region signature.Instr)
    (x : Fin (M + 1)) : Region signature.Instr :=
  (resetRegion (c x)).lsubst (fun _ => (rows x).renameVars (lift Nat.succ))

theorem resetRows_typed {M : Nat} {D : Ty Empty} (c : Fin (M + 1) → Bool)
    {rows : Fin (M + 1) → Region signature.Instr} (h : ∀ x, ValueBranches [State] (rows x) [D])
    (x : Fin (M + 1)) : ValueBranches [State] (resetRows c rows x) [D] :=
  seqValueBranches (reset_typed (c x)) (h x)

/-- Reset the query of every state, as an arrow of default Paper. -/
noncomputable def resetArr {M : Nat} (c : Fin (M + 1) → Bool) :
    ofType (Φ := signature.Instr) (States M) ⟶ ofType (States M) :=
  ofRegion (dispatch_typed M (resetRows_typed c (entry_typed M)))

/-- Every row sends each repeat to a state whose Bit the repeat carries:
resetting the targets of the row changes nothing. An equation of default
Paper. -/
def Matched {M : Nat} (c : Fin (M + 1) → Bool) {rows : Fin (M + 1) → Region signature.Instr}
    (h : ∀ x, ValueBranches [State] (rows x) [Silmaril.coprod Bit (States M)]) : Prop :=
  ∀ x, (ofRegion (h x) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
      coprod.map (𝟙 _) (resetArr c) =
    ofRegion (h x) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom

theorem deadBit_typed : ValueBranches [Silmaril.empty] (.br 0 (.inl .unit) : Region signature.Instr) [Bit] :=
  .br rfl (.inl .unit)

/-- A loop entered by a case on the state's Bit: `r₀` on `false`, `r₁` on `true`. -/
def caseEntry (r₀ r₁ : Region signature.Instr) : Region signature.Instr :=
  .case (.var 0) ((pairSplit r₀ r₁).renameVars (lift Nat.succ))
    ((Region.br 0 (.inl .unit)).renameVars (lift Nat.succ))

theorem caseEntry_typed {r₀ r₁ : Region signature.Instr} (h₀ : ValueBranches [Ty.unit] r₀ [Bit])
    (h₁ : ValueBranches [Ty.unit] r₁ [Bit]) : ValueBranches [State] (caseEntry r₀ r₁) [Bit] :=
  caseValueBranches (caseValueBranches h₀ h₁) deadBit_typed

/-- A region entered with the constant state `q`. -/
def constEntry (q : Bool) (r : Region signature.Instr) : Region signature.Instr :=
  (Region.br 0 (.inl (bitTm q))).lsubst (fun _ => r.renameVars (lift Nat.succ))

theorem constEntry_typed {D : Ty Empty} (q : Bool) {r : Region signature.Instr} (h : ValueBranches [State] r [D]) :
    ValueBranches [Ty.unit] (constEntry q r) [D] :=
  seqValueBranches (const_typed q) h

/-- `r` entered with each constant is a table of literal request trees
entered with that constant. -/
def Pointed {K : Nat} (r : Region signature.Instr) (t : Bool → LTable K) (x : Bool → Fin (K + 1)) : Prop :=
  ∀ q, Eqv false [Ty.unit] (constEntry q r) (constEntry q ((t q).entered (x q))) [Bit]

section Split

variable {K : Nat}

/-- The split state of row `j` entered with the Bit `q`. -/
def splitIdx (j : Fin (K + 1)) (q : Bool) : Fin (K + (K + 1) + 1) :=
  match q with
  | false => frontIdx K j
  | true => tailIdx K j

/-- The row of a split state. -/
def splitRow : Fin (K + (K + 1) + 1) → Fin (K + 1) := joinIdx K id id

/-- The entry Bit of a split state. -/
def splitBit : Fin (K + (K + 1) + 1) → Bool := joinIdx K (fun _ => false) (fun _ => true)

/-- Keep an exit; send a repeat to the split state of the Bit it carries. -/
def redirect : Act K → Act (K + (K + 1))
  | .ret c => .ret c
  | .go j q => .go (splitIdx j q) q

/-- A repeat carries the Bit `c` assigns to its target. -/
def Act.Carries {M : Nat} (c : Fin (M + 1) → Bool) : Act M → Prop
  | .ret _ => True
  | .go x q => c x = q

/-- The actions with the left return fixed at `q`. -/
def keptAct {M : Nat} (a : Bool → Bool → Act M) (q x y : Bool) : Act M :=
  match x with
  | false => a false q
  | true => a true y

variable (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

/-- A router table all of whose rows keep their entry state. -/
def entryRouter : Router K := ⟨fun i => entryProgram (l₁ i) (l₂ i), act⟩

/-- The same rows at split states, with every repeat redirected. -/
def entrySplit : Router (K + (K + 1)) :=
  ⟨fun x => entryProgram (l₁ (splitRow x)) (l₂ (splitRow x)), fun x a b => redirect (act (splitRow x) a b)⟩

/-- The actions of a split state: its left return is its entry Bit. -/
def entryAct (x : Fin (K + (K + 1) + 1)) : Bool → Bool → Act (K + (K + 1)) :=
  keptAct (fun a b => redirect (act (splitRow x) a b)) (splitBit x)

/-- The split table with two-request programs, which keep nothing. -/
def entryDuo : Router (K + (K + 1)) :=
  duoRouter (fun x => l₁ (splitRow x)) (fun x => l₂ (splitRow x)) (entryAct act)

/-- The split table as literal request trees. -/
def entrySource : LTable (K + (K + 1)) :=
  duoSource (fun x => l₁ (splitRow x)) (fun x => l₂ (splitRow x)) (entryAct act)

/-- The split table entered by a case on the original state. -/
def entryCase (j : Fin (K + 1)) : Region signature.Instr :=
  caseEntry (constEntry false ((entrySource l₁ l₂ act).entered (splitIdx j false)))
    (constEntry true ((entrySource l₁ l₂ act).entered (splitIdx j true)))

theorem entryCase_typed (j : Fin (K + 1)) : ValueBranches [State] (entryCase l₁ l₂ act j) [Bit] :=
  caseEntry_typed (constEntry_typed false ((entrySource l₁ l₂ act).entered_typed _))
    (constEntry_typed true ((entrySource l₁ l₂ act).entered_typed _))

end Split

/-! ## Regression tables -/

/-- One row: return the Bit it is given, or repeat with the negated Bit. -/
def turnAct (_ : Fin 1) (x y : Bool) : Act 0 :=
  match x with
  | false => .ret y
  | true => .go 0 (!y)

/-- The copy a repeat goes to: the copy of the Bit it carries, or, when
`frozen`, the copy it is in. -/
def turnTarget (frozen c q : Bool) : Bool :=
  match frozen with
  | false => q
  | true => c

def turnCopy (c : Bool) : Fin 2 :=
  match c with
  | false => 0
  | true => 1

def turnKids (frozen l₂ c x y : Bool) : LTree 1 :=
  match x with
  | false => .ask y l₂ fun x' y' =>
      match x' with
      | false => .leaf (.ret c)
      | true => .leaf (.go (turnCopy (turnTarget frozen c (!y'))) (!y'))
  | true => .leaf (.go (turnCopy (turnTarget frozen c (!y))) (!y))

/-- The split table of the one-row table of `turnAct`, written out. Copy
`c` returns `c` after the second left reply. When `frozen`, a repeat
stays in its copy, so the kept Bit is the first state for ever. -/
def turnSource (frozen l₁ l₂ : Bool) : LTable 1 :=
  ⟨fun _ => l₁, fun j => turnKids frozen l₂ (match j with | 0 => false | 1 => true)⟩

/-- The frozen table entered by a case on the state. -/
def frozenCase (l₁ l₂ : Bool) : Region signature.Instr :=
  caseEntry (constEntry false ((turnSource true l₁ l₂).entered 0))
    (constEntry true ((turnSource true l₁ l₂).entered 1))

theorem frozenCase_typed (l₁ l₂ : Bool) : ValueBranches [State] (frozenCase l₁ l₂) [Bit] :=
  caseEntry_typed (constEntry_typed false ((turnSource true l₁ l₂).entered_typed 0))
    (constEntry_typed true ((turnSource true l₁ l₂).entered_typed 1))

def turnRow (c : Bool) : Fin 4 :=
  match c with
  | false => 2
  | true => 3

/-- The same with the second requests as two explicit states in front. -/
def turnExplicitAct (frozen : Bool) (i : Fin 4) (x y : Bool) : Act 3 :=
  match i, x with
  | 0, false => .ret false
  | 0, true => .go (turnRow (turnTarget frozen false (!y))) (!y)
  | 1, false => .ret true
  | 1, true => .go (turnRow (turnTarget frozen true (!y))) (!y)
  | 2, false => .go 0 y
  | 2, true => .go (turnRow (turnTarget frozen false (!y))) (!y)
  | 3, false => .go 1 y
  | 3, true => .go (turnRow (turnTarget frozen true (!y))) (!y)

def turnExplicitLabel (l₁ l₂ : Bool) (i : Fin 4) : Bool :=
  match i with
  | 0 => l₂
  | 1 => l₂
  | 2 => l₁
  | 3 => l₁

/-- The table of `capProgram` rows with `turnAct`: one explicit state for
each kept first payload, in front of the row. -/
def capTurnAct (i : Fin 3) (x y : Bool) : Act 2 :=
  match i, x, y with
  | 0, false, _ => .ret false
  | 0, true, y => .go 2 (!y)
  | 1, false, _ => .ret true
  | 1, true, y => .go 2 (!y)
  | 2, false, false => .go 0 false
  | 2, false, true => .go 1 true
  | 2, true, y => .go 2 (!y)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
