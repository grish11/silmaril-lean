module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.SelectedTerminal

/-! # Separation of the selected direct read and quoted table -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow_eq_iff)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local instance : HasEff signature.Instr Bool := signature.hasEff

local notation "E" => Paper.Extension.Eqv Seed
local notation "read" => Finite.Expr.read (1 : Fin 2)
local notation "quote" => Finite.Expr.quote 2 (fun env => env 1)

/-- The ambient join separates the precise open terminal comparison at each
ordered exit. Both variants keep the same finite emit prefix. -/
theorem terminal_ne (pos : Position Exits) :
    ¬ E [TerminalInput] (terminal pos read).elaborate.val (terminal pos quote).elaborate.val Exits :=
  PairSequencing.selected_terminal_ne pos

/-- The probe separates a unary value let from its value when used inside
the emitted case discriminator. -/
theorem prefixed_test_ne :
    ¬ E [Bit] (prefixedTest (.seq .input .input)).elaborate.val (prefixedTest .input).elaborate.val Exits :=
  PairSequencing.prefixed_test_ne

/-- The direct read and table are unequal in #4095's source SSA quotient,
at the actual packed singleton representatives. -/
theorem packed_ne : packed direct ≠ packed table :=
  fun h => PairSequencing.selected_closed_ne
    ((packArrow_eq_iff direct.selected.elaborate.property table.selected.elaborate.property).1 h)

/-- Adding the existing case-return and unary-forwarding seeds still
separates the same packed representatives. -/
theorem packed_caseUnary_ne :
    Paper.Extension.Singleton.ofRegion (Paper.WithCaseAndUnaryReturns.JoinedStep false)
        direct.selected.elaborate.property.packExits ≠
      Paper.Extension.Singleton.ofRegion (Paper.WithCaseAndUnaryReturns.JoinedStep false)
        table.selected.elaborate.property.packExits :=
  fun h => PairSequencing.selected_packed_caseUnary_ne ((Paper.Extension.Singleton.ofRegion_eq_iff _ _ _).1 h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay
