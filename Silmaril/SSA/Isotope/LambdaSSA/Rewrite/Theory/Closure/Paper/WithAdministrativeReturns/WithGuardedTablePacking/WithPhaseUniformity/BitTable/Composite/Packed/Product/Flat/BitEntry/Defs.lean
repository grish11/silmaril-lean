module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Controlled.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Defs

/-! # Sources with one Bit of input, and their two constant inputs

`atInput q s` runs a source `s` on the constant input `q`. The constant
is built on the unit input, so the two constant inputs are the two
constructors of a Bit.

`BitPointed s label act x` is a certificate for a source: at each
constant input `q`, the source is the router table
`Router.ofSpin label act` entered at the row `x q` with the Bit `q`.
The equations of a certificate are equations of the opt-in quotient.
Nothing decides whether a given flat graph has a certificate.
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
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)

variable {M : Nat}

/-- The source run on the constant input `q`. -/
def atInput (q : Bool) (s : Region signature.Instr) : Region signature.Instr :=
  seqRegion (.br 0 (bitTm q)) s

theorem atInput_typed {D : Ty Empty} {s : Region signature.Instr} (q : Bool) (hs : ValueBranches [Bit] s [D]) :
    ValueBranches [Ty.unit] (atInput q s) [D] :=
  seqRegion_typed (.br rfl (bitTm_typed q)) hs

/-- At each constant input the source is a router table entered at a row
with that input as its Bit. -/
def BitPointed (s : Region signature.Instr) (label : Fin (M + 1) → Option Bool)
    (act : Fin (M + 1) → Bool → Bool → Act M) (x : Bool → Fin (M + 1)) : Prop :=
  ∀ q, Eqv false [Ty.unit] (atInput q s) (constEntry q ((Router.ofSpin label act).entered (x q))) [Bit]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
