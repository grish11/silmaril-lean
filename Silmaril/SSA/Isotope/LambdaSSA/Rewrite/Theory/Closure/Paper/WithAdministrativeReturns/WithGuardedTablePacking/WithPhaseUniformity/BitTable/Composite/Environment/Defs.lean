module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Entry.Defs

/-! # Written rows with an environment of Bits

## The fragment

A schedule `Normal 2 n` is a finite tree of labelled requests over an
environment of `n` Bit slots. A request reads its query from a slot. Each
reply extends the environment: the reply's payload becomes slot zero. A
leaf takes exit zero (return) or exit one (repeat) with the Bit in a
slot. `envCode c` is the schedule as written code.

An `EnvRow` is a first request that reads the entry state, followed by a
schedule for each reply tag. Under the first reply slot zero is that
reply and slot one is the entry state. `EnvRow.program` is its written
program. `labelPoll`, `duoProgram`, `capProgram` and `entryProgram` are
such programs.

## Specialization

`envSem c ρ` is the packed schedule with a term for each slot, and
`envSpec c env` the packed schedule with a constant for each slot.
`envTree a c env` is the literal request tree of the schedule on the
constants `env`, routed by `a`: a leaf acts on the constant in its slot,
a request is sent with the constant in its slot, and each of its four
replies extends `env`. `splitSubst b` replaces a Bit variable by the
constant `b` built on the unit variable below it.

## Tables

`envRouter row act` is the router table of written rows. `splitRouter t`
puts the rows of any router at the split states of #5273 and redirects
every repeat. `envSource row act` is the split table as literal request
trees: the split state of the entry Bit `c` has the trees of its row
entered with `c`. `envCase` enters it by a case on the original state.
`LTree.Carries c` says every repeat of a tree carries the Bit `c` assigns
to its target.

## Regression tables

`slotRow l₁ l₂ sL sR` has a second request whose left reply returns slot
`sL` and whose right reply returns slot `sR`, among the second reply, the
first reply and the entry state. `slotRouter` routes it with `turnAct`,
whose repeat carries the negated Bit. `slotAct` writes the split table
with the second requests as explicit states; when `frozen` a repeat stays
in its copy. `letProgram` is a written row with a Bit let and a unit let,
and `letRow` its row in the fragment.
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

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Code Normal)

variable {K : Nat}

/-! ## The fragment -/

/-- A request schedule as written code: every request reads a slot. -/
def envCode : {n : Nat} → Normal 2 n → Code 2 n
  | _, .ret e s => .ret e s
  | _, .ask l s left right => .ask l (.read s) (envCode left) (envCode right)

/-- Slot terms under a new reply: the reply is slot zero. -/
def pushTm {n : Nat} (ρ : Fin n → Tm signature.Instr) : Fin (n + 1) → Tm signature.Instr :=
  Fin.cases (.var 0) (fun i => (ρ i).rename Nat.succ)

/-- The packed schedule with a term for each slot. -/
def envSem : {n : Nat} → Normal 2 n → (Fin n → Tm signature.Instr) → Region signature.Instr
  | _, .ret e s, ρ => .br 0 (packedExitArg e.val (ρ s))
  | _, .ask l s left right, ρ =>
    .case (.op (.ask l) (ρ s)) (envSem left (pushTm ρ)) (envSem right (pushTm ρ))

/-- The packed schedule with a constant for each slot. -/
def envSpec {n : Nat} (c : Normal 2 n) (env : Fin n → Bool) : Region signature.Instr :=
  envSem c fun i => bitTm (env i)

/-- Replace the Bit variable by the constant `b` and the unit variable by
the unit payload of that constant. -/
def splitSubst (b : Bool) : Nat → Tm signature.Instr
  | 0 => bitTm b
  | 1 => .var 0
  | i + 2 => .var (i + 2)

/-- The environment with a new reply. -/
def consBit {n : Nat} (b : Bool) (env : Fin n → Bool) : Fin (n + 1) → Bool := Fin.cases b env

/-- Whether an exit is the repeat. -/
def exitBit (e : Fin 2) : Bool :=
  match e with
  | 0 => false
  | 1 => true

/-- The literal request tree of a schedule whose slots are the constants
`env`, routed by `a`. A leaf acts on the constant in its slot. A request
is sent with the constant in its slot, and each reply extends `env`. -/
def envTree (a : Bool → Bool → Act K) : {n : Nat} → Normal 2 n → (Fin n → Bool) → LTree K
  | _, .ret e s, env => .leaf (a (exitBit e) (env s))
  | _, .ask l s left right, env => .ask (env s) l fun x y =>
    match x with
    | false => envTree a left (consBit y env)
    | true => envTree a right (consBit y env)

/-- Every repeat of the tree carries the Bit `c` assigns to its target. -/
def LTree.Carries {M : Nat} (c : Fin (M + 1) → Bool) : LTree M → Prop
  | .leaf a => a.Carries c
  | .ask _ _ kids => ∀ x y, (kids x y).Carries c

/-! ## Rows and tables -/

/-- A written row: a first request that reads the entry state, then a
schedule for each reply tag with the reply and the entry state as slots. -/
structure EnvRow where
  label : Bool
  left : Normal 2 2
  right : Normal 2 2

def EnvRow.normal (r : EnvRow) : Normal 2 1 := .ask r.label 0 r.left r.right

/-- The written program of the row. -/
def EnvRow.program (r : EnvRow) : Program := envCode r.normal

/-- The row entered with the Bit `c`, routed by `a`, as literal request
trees for the four first replies. -/
def EnvRow.kids (r : EnvRow) (a : Bool → Bool → Act K) (c x y : Bool) : LTree K :=
  match x with
  | false => envTree a r.left (consBit y fun _ => c)
  | true => envTree a r.right (consBit y fun _ => c)

/-- A router table of written rows. -/
def envRouter (row : Fin (K + 1) → EnvRow) (act : Fin (K + 1) → Bool → Bool → Act K) : Router K :=
  ⟨fun i => (row i).program, act⟩

/-- The rows of any router table at the split states, with every repeat
redirected to the split state of the Bit it carries. -/
def splitRouter (t : Router K) : Router (K + (K + 1)) :=
  ⟨fun x => t.prog (splitRow x), fun x a b => redirect (t.act (splitRow x) a b)⟩

/-- The split table as literal request trees: the split state of the
entry Bit `c` has the trees of its row entered with `c`. -/
def envSource (row : Fin (K + 1) → EnvRow) (act : Fin (K + 1) → Bool → Bool → Act K) : LTable (K + (K + 1)) :=
  ⟨fun x => (row (splitRow x)).label,
    fun x => (row (splitRow x)).kids (fun a b => redirect (act (splitRow x) a b)) (splitBit x)⟩

/-- The split table entered by a case on the original state. -/
def envCase (row : Fin (K + 1) → EnvRow) (act : Fin (K + 1) → Bool → Bool → Act K) (j : Fin (K + 1)) :
    Region signature.Instr :=
  caseEntry (constEntry false ((envSource row act).entered (splitIdx j false)))
    (constEntry true ((envSource row act).entered (splitIdx j true)))

theorem envCase_typed (row : Fin (K + 1) → EnvRow) (act : Fin (K + 1) → Bool → Bool → Act K) (j : Fin (K + 1)) :
    ValueBranches [State] (envCase row act j) [Bit] :=
  caseEntry_typed (constEntry_typed false ((envSource row act).entered_typed _))
    (constEntry_typed true ((envSource row act).entered_typed _))

/-! ## Regression tables -/

/-- The value of a slot under the second request: the second reply, the
first reply, or the entry state. -/
def pick (s : Fin 3) (y' y c : Bool) : Bool := consBit y' (consBit y fun _ => c) s

/-- A row with two requests. The second is sent on the first left reply
with that reply as query. Its left reply returns slot `sL` and its right
reply returns slot `sR`. The first right reply is the repeat. -/
def slotRow (l₁ l₂ : Bool) (sL sR : Fin 3) : EnvRow :=
  ⟨l₁, .ask l₂ 0 (.ret 0 sL) (.ret 0 sR), .ret 1 0⟩

/-- The one-row table of `slotRow` with `turnAct`: a returned Bit is
returned, and the repeat carries the negated Bit. -/
def slotRouter (l₁ l₂ : Bool) (sL sR : Fin 3) : Router 0 :=
  envRouter (fun _ => slotRow l₁ l₂ sL sR) turnAct

def slotInner (c y : Bool) : Fin 6 :=
  match c, y with
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

def slotCopy (c : Bool) : Fin 6 :=
  match c with
  | false => 4
  | true => 5

/-- The split table with its second requests as four explicit states,
one for each entry Bit and first reply, in front of the two copies of the
row. When `frozen`, a repeat stays in its copy. -/
def slotAct (frozen : Bool) (sL sR : Fin 3) (i : Fin 6) (x y : Bool) : Act 5 :=
  match i, x with
  | 0, false => .ret (pick sL y false false)
  | 0, true => .ret (pick sR y false false)
  | 1, false => .ret (pick sL y true false)
  | 1, true => .ret (pick sR y true false)
  | 2, false => .ret (pick sL y false true)
  | 2, true => .ret (pick sR y false true)
  | 3, false => .ret (pick sL y true true)
  | 3, true => .ret (pick sR y true true)
  | 4, false => .go (slotInner false y) y
  | 4, true => .go (slotCopy (turnTarget frozen false (!y))) (!y)
  | 5, false => .go (slotInner true y) y
  | 5, true => .go (slotCopy (turnTarget frozen true (!y))) (!y)

def slotLabel (l₁ l₂ : Bool) (i : Fin 6) : Bool :=
  match i with
  | 0 => l₂
  | 1 => l₂
  | 2 => l₂
  | 3 => l₂
  | 4 => l₁
  | 5 => l₁

/-- A router table of labelled requests as a table of literal request
trees whose trees are leaves. -/
def leafTable {M : Nat} (label : Fin (M + 1) → Bool) (act : Fin (M + 1) → Bool → Bool → Act M) : LTable M :=
  ⟨label, fun i x y => .leaf (act i x y)⟩

/-- The frozen explicit table entered by a case on the state. -/
def slotFrozen (l₁ l₂ : Bool) (sL sR : Fin 3) : Region signature.Instr :=
  caseEntry (constEntry false ((leafTable (slotLabel l₁ l₂) (slotAct true sL sR)).entered 4))
    (constEntry true ((leafTable (slotLabel l₁ l₂) (slotAct true sL sR)).entered 5))

theorem slotFrozen_typed (l₁ l₂ : Bool) (sL sR : Fin 3) :
    ValueBranches [State] (slotFrozen l₁ l₂ sL sR) [Bit] :=
  caseEntry_typed (constEntry_typed false ((leafTable (slotLabel l₁ l₂) (slotAct true sL sR)).entered_typed 4))
    (constEntry_typed true ((leafTable (slotLabel l₁ l₂) (slotAct true sL sR)).entered_typed 5))

/-- A written row with lets: it binds the result of a first request,
which is that request's reply or the entry state, and sends a second
request with the bound Bit as query. The second left reply returns the
entry state and the second right reply repeats. -/
def letProgram (l₁ l₂ : Bool) : Program :=
  .letBit (.ask l₁ (.read 0) (.ret 0 0) (.letUnit (.ret 0 1))) (.ask l₂ (.read 0) (.ret 0 2) (.ret 1 0))

/-- Its row in the fragment: the first right reply sends the second
request with the entry state. -/
def letRow (l₁ l₂ : Bool) : EnvRow :=
  ⟨l₁, .ask l₂ 0 (.ret 0 2) (.ret 1 0), .ask l₂ 1 (.ret 0 2) (.ret 1 0)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
