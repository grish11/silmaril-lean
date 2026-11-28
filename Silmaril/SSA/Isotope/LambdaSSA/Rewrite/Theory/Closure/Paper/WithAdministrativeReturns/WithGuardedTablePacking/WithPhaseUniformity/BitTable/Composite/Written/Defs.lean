module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Nested.Defs

/-! # Router tables of written programs as mixed tables

A `Router` has a written program at each row. A written program is a
`Code 2 1`: returns, unit lets, Bit lets and requests whose query reads a
slot or is a constructor-known case of slots. `Code.normalize` gives its
request schedule, a `Normal 2 1`.

A request schedule on one slot is a leaf or starts with a request on that
slot. `MixRow.ofNormal` reads it as a row of a mixed table: a leaf is a
request-free row, and a schedule that starts with a request is a row of
the environment fragment. `MixRow.normal` goes back. `mixRowOf p` is the
row of the written program `p`, and `Router.mixRows t` the rows of a
table.

`Router.Normalizes t row` is the syntactic condition that relates a table
of written programs to given rows: the normal form of each program is the
request schedule of its row.

`letNested` is a written row with a Bit let that captures the first reply
or the entry state and uses it as the query of a second request.
`letIdle` is a written request-free row with a unit let. `letStash` is
the table of the two, routed by `stashAct`.
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

/-- The request schedule of a row of a mixed table. -/
def MixRow.normal : MixRow → Normal 2 1
  | .ask r => r.normal
  | .pure e => .ret e 0

/-- The row of a request schedule on one slot: a schedule that starts
with a request is a row of the environment fragment, and a schedule that
is a leaf is a request-free row. -/
def MixRow.ofNormal : Normal 2 1 → MixRow
  | .ret e _ => .pure e
  | .ask l _ left right => .ask ⟨l, left, right⟩

/-- The row of a written program: the row of its normal form. -/
def mixRowOf (p : Program) : MixRow := .ofNormal (p.normalize id)

/-- The rows of a router table of written programs. -/
def Router.mixRows (t : Router K) (i : Fin (K + 1)) : MixRow := mixRowOf (t.prog i)

/-- The syntactic condition: the normal form of each written program is
the request schedule of the given row. -/
def Router.Normalizes (t : Router K) (row : Fin (K + 1) → MixRow) : Prop :=
  ∀ i, (t.prog i).normalize id = (row i).normal

/-! ## Regression tables -/

/-- A written row with a let. After the first left reply it binds a
captured Bit, the first reply or, when `s`, the entry state, and sends a
second request with the bound Bit as query. Both replies of the second
request repeat. The right reply of the first request returns. -/
def letNested (l₁ l₂ s : Bool) : Program :=
  .ask l₁ (.read 0)
    (.letBit (.ret 0 (match s with | false => 0 | true => 1)) (.ask l₂ (.read 0) (.ret 1 0) (.ret 1 0)))
    (.ret 0 0)

/-- A written request-free row with a let: it repeats with its state. -/
def letIdle : Program := .letUnit (.ret 1 0)

/-- The written table: the row with a let in front of the request-free
row, routed by `stashAct n f`. The request-free row is a silent cycle,
which negates the Bit when `f`. -/
def letStash (l₁ l₂ s n f : Bool) : Router 1 :=
  ⟨fun i => match i with | 0 => letNested l₁ l₂ s | 1 => letIdle, stashAct n f⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
