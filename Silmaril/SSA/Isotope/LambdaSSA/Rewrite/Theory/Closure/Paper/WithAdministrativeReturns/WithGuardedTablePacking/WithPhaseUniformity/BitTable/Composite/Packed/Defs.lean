module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Written.Defs

/-! # Packed dispatcher loops and source loops that factor through them

`Router.loop t` is the packed loop of a router table on its packed state
`States K`: a tagged sum with one component for each row, each carrying a
Bit. `t.entered i` is that loop entered at row `i`.

`seqRegion e d` runs `e` and then `d` on its result.

A source loop `src` on a state type `S` is related to a packed loop by
two guarded regions: an encoding `enc : S → States K` and a decoding
`dec : States K → S`.

* `Retracts S enc dec`: `enc` followed by `dec` is the identity on `S`.
  The packed state carries the source state faithfully.
* `Factors dec src t`: the source run on a decoded packed state is the
  packed loop of `t`. Entered at row `i`, this says that the source
  entered at the decoded state of row `i` is `t.entered i`.

Both are equations of the opt-in quotient.
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

/-- Run `e`, then `d` on its result. -/
def seqRegion (e d : Region signature.Instr) : Region signature.Instr :=
  e.lsubst (fun _ => d.renameVars (lift Nat.succ))

theorem seqRegion_typed {X Y Z : Ty Empty} {e d : Region signature.Instr} (he : ValueBranches [X] e [Y])
    (hd : ValueBranches [Y] d [Z]) : ValueBranches [X] (seqRegion e d) [Z] :=
  seqValueBranches he hd

/-- The packed loop of a router table, on its packed state: one tag for
each row, each carrying a Bit. It is not entered at a row. -/
def Router.loop (t : Router K) : Region signature.Instr := dispatchLoop K t.rows

theorem Router.loop_typed (t : Router K) : ValueBranches [States K] t.loop [Bit] :=
  dispatchLoop_typed t.rows_typed

/-- The identity on a type. -/
theorem idRegion_typed (S : Ty Empty) : ValueBranches [S] (.br 0 (.var 0) : Region signature.Instr) [S] :=
  .br rfl (.var rfl)

/-- A source loop on the state type `S` factors through the packed loop
of `t` along the decoding `dec`: the source run on a decoded packed state
is the packed loop. -/
def Factors (dec src : Region signature.Instr) (t : Router K) : Prop :=
  Eqv false [States K] (seqRegion dec src) t.loop [Bit]

/-- `enc` followed by `dec` is the identity on `S`: the packed state
carries the source state faithfully. -/
def Retracts (S : Ty Empty) (enc dec : Region signature.Instr) : Prop :=
  Eqv false [S] (seqRegion enc dec) (.br 0 (.var 0)) [S]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
