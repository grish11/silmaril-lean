module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.LatchSeparation

/-! # What default Paper proves about the two-block source, and what it does not

No seed and no quotient law is added. Default Paper is unchanged.

## The boundary

The opt-in reduction of #5314 has two parts:

1. `latchSource l = latchReadback l`: the table-packing seed at the source.
2. `latchReadback l = loopRegion Pair (pairBody l)`: default Paper.

This file shows that part 1 cannot be moved into default Paper.

## What default Paper proves

* `latchReadback_eqv_loop` (#5314): the packed readback is the loop on
  pairs.
* `latchReadback_eqv_pairSource`: so the packed readback is the
  one-header source of #5309.

On the readback side the two-block structure is gone: readback, loop on
pairs and one-header source are one class of default Paper.

## What default Paper does not prove

* `latchSource_ne_readback_paper`: the table-packing equation at this
  source, `latchSource l = latchReadback l'`, is not an equation of
  default Paper. This is the exact source-side equation that is missing.
* `latchSource_ne_loop_paper`, `latchSource_ne_pairSource_paper`: the
  two-block source is not equal in default Paper to the loop on pairs or
  to the one-header source, for any labels.
* `latchSource_ne_loop_unaryReturns`: the same holds in the unary-return
  quotient, which extends default Paper.

## The administrative-return quotient

The table-packing quotient adds one rule, the packing seed, to the
administrative-return quotient. That quotient adds two seeds to the
unary-return quotient: constructor β inside the operand of a primitive
(`WithConstructorCaseOperands.Step`), and the split of a returned
term-level case (`WithLetCase.Step`). Neither mentions a table.

* `latchSource_ne_readback_administrativeReturns`: the table-packing
  equation at this source is not an equation of the administrative-return
  quotient.
* `latchSource_ne_loop_administrativeReturns`,
  `latchSource_ne_pairSource_administrativeReturns`: nor is the equality
  with the loop on pairs or with the one-header source, for any labels.
* `latchSource_readback_needs_packing`: the equation holds in the
  table-packing quotient and fails in the administrative-return quotient.

So the packing seed is the first rule of this chain of quotients that
proves the equation, and no smaller quotient of the chain does.

These are statements about derivability, not about the supported models:
in the table-packing quotient the equations hold (#5314), and they are
valid in every supported model.

## The proof

The proof reuses the existing observer of the bound-simulation
obstruction, which is checked sound for every equation of default Paper
over any instruction signature. It gives each request a fixed reply and marks an
endless local path through a table with at least two rows; an endless
path through a one-block loop stays unmarked.

* On the input whose two Bits equal the reply payload, the two-block
  source alternates between its header and its back-edge block: a marked
  endless path.
* The one-header source and the loop on pairs repeat one block: an
  unmarked endless path.

The observer also respects both seeds of the administrative-return
quotient, when case terms and bound unary lets are unmarked and the
operands of primitives are evaluated, as they are here. It evaluates a
case on a constructor to the selected arm, so constructor β at an operand
keeps the observed operand; and it evaluates a returned case and the case
of the returns alike.

Every derivation of default Paper is validated by the observer, so no
combination of its laws for tables, block substitution, dinaturality or
Bekič relates the two sides. The Bekič law of default Paper is stated for
one-block loops at a sum type; it does not apply to a table with two
blocks.

## Not determined here

* Other two-block tables. The separation is proved for this source.
* Quotients outside this chain. Nothing is claimed about an opt-in rule
  other than the packing seed.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
open Silmaril.DeBruijn (lift)

/-! ## What default Paper proves -/

/-- The packed readback of the two-block source is the one-header
source, in default Paper. -/
theorem latchReadback_eqv_pairSource (l : Bool) :
    Paper.Eqv [Pair] (latchReadback l).val (pairSource l) [Bit] :=
  LatchSeparation.readback_header l

/-! ## What default Paper does not prove -/

/-- The table-packing equation at the two-block source is not an
equation of default Paper. -/
theorem latchSource_ne_readback_paper (l l' : Bool) :
    ¬ Paper.Eqv [Pair] (latchSource l) (latchReadback l').val [Bit] :=
  LatchSeparation.source_ne_readback l l'

/-- Default Paper does not prove the two-block source equal to the loop
on pairs. -/
theorem latchSource_ne_loop_paper (l l' : Bool) :
    ¬ Paper.Eqv [Pair] (latchSource l) (loopRegion Pair (pairBody l')) [Bit] :=
  LatchSeparation.source_ne_loop l l'

/-- Default Paper does not prove the two-block source equal to the
one-header source. -/
theorem latchSource_ne_pairSource_paper (l l' : Bool) :
    ¬ Paper.Eqv [Pair] (latchSource l) (pairSource l') [Bit] :=
  LatchSeparation.source_ne_header l l'

/-- Neither does the unary-return quotient. -/
theorem latchSource_ne_loop_unaryReturns (l l' : Bool) :
    ¬ Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Eqv false [Pair]
      (latchSource l) (loopRegion Pair (pairBody l')) [Bit] :=
  LatchSeparation.source_ne_loop_unary l l'

/-! ## The administrative-return quotient -/

/-- The table-packing equation at the two-block source is not an
equation of the administrative-return quotient. -/
theorem latchSource_ne_readback_administrativeReturns (l l' : Bool) :
    ¬ WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (latchReadback l').val [Bit] :=
  LatchSeparation.source_ne_readback_admin l l'

/-- The administrative-return quotient does not prove the two-block
source equal to the loop on pairs. -/
theorem latchSource_ne_loop_administrativeReturns (l l' : Bool) :
    ¬ WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (loopRegion Pair (pairBody l')) [Bit] :=
  LatchSeparation.source_ne_loop_admin l l'

/-- Nor equal to the one-header source. -/
theorem latchSource_ne_pairSource_administrativeReturns (l l' : Bool) :
    ¬ WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (pairSource l') [Bit] :=
  LatchSeparation.source_ne_header_admin l l'

/-- The equation between the two-block source and its packed readback
holds in the table-packing quotient and fails in the administrative-return
quotient, which lacks only the packing seed. -/
theorem latchSource_readback_needs_packing (l : Bool) :
    WithGuardedTablePacking.Eqv false [Pair] (latchSource l) (latchReadback l).val [Bit] ∧
      ¬ WithAdministrativeReturns.Eqv false [Pair] (latchSource l) (latchReadback l).val [Bit] :=
  ⟨latchSource_readback l, latchSource_ne_readback_administrativeReturns l l⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
