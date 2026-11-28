module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.SelectedTerminal.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseNativeReplay

/-! # Native replay and separation for the selected read versus table -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite (Derivable)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v

/-- A native equation can be placed in the original packed continuation. -/
theorem applyPacked_eqv {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    {S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {X A : τ} {L : LCtx τ} {r s : Region Φ}
    (h : Paper.Extension.Eqv S [product X A] r s L) :
    Paper.Extension.Eqv S [A, X] (Paper.PackedBody.applyPacked r) (Paper.PackedBody.applyPacked s) L :=
  SelectedCaseNativeReplay.applyPacked_eqv h

/-- Replay either arm of a literal selected case under constructor substitution
of its packed input and payload. The discriminator is shared. -/
theorem case_congr {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    {S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {X A B : τ} {L : LCtx τ} (a : Term Φ X (coprod A B))
    {l l' : CaseTree Φ (product X A) L} {r r' : CaseTree Φ (product X B) L}
    (hl : Paper.Extension.Eqv S [product X A] l.elaborate.val l'.elaborate.val L)
    (hr : Paper.Extension.Eqv S [product X B] r.elaborate.val r'.elaborate.val L) :
    Paper.Extension.Eqv S [X] (CaseTree.case A B a l r).elaborate.val
      (CaseTree.case A B a l' r').elaborate.val L :=
  SelectedCaseNativeReplay.case_congr a hl hr

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "E" => Paper.Extension.Eqv Seed
local notation "read" => Finite.Expr.read (1 : Fin 2)
local notation "quote" => Finite.Expr.quote 2 (fun env => env 1)

/-- The two witnessed request binding presentations elaborate to the same
packed arrow when the terminal expression is shared. -/
theorem packed_fixture_binder (b b' : Bool) (result : Finite.Expr 2) :
    packed (fixture b result) = packed (fixture b' result) :=
  rfl

/-- The two open terminal equations suffice for replay of the full fixture
through the chosen requests, guard, and outward packing. -/
theorem packed_of_terminal {S : VCtx (Ty Empty) → Region signature.Instr → Region signature.Instr →
      LCtx (Ty Empty) → Prop}
    (h₀ : Paper.Extension.Eqv S [TerminalInput]
      (terminal first read).elaborate.val (terminal first quote).elaborate.val Exits)
    (h₁ : Paper.Extension.Eqv S [TerminalInput]
      (terminal second read).elaborate.val (terminal second quote).elaborate.val Exits) :
    Paper.Extension.Singleton.ofRegion S direct.selected.elaborate.property.packExits =
      Paper.Extension.Singleton.ofRegion S table.selected.elaborate.property.packExits :=
  SelectedCaseNativeReplay.packed_of_terminal h₀ h₁

/-- Equality of lowered returns alone gives no congruence in the
emit-prefixed case discriminator, even for a unary value let. -/
theorem prefixed_case_congruence_fails :
    ¬ (∀ (a b : Term signature.Instr Bit Bit),
      E [Bit] (CfgEta.TypeCategory.returnRegion a.elaborate.val)
        (CfgEta.TypeCategory.returnRegion b.elaborate.val) [Bit] →
      E [Bit] (prefixedTest a).elaborate.val (prefixedTest b).elaborate.val Exits) :=
  fun h => prefixed_test_ne (h _ _ SelectedCaseNativeReplay.returned_seq_input)

/-- The two witnesses admit the native LetCase derivation from the exact
closed comparison. -/
theorem witnessed_derivable :
    Derivable false (Finite.Extensional.Selected.equation Bit [Bit] direct table) :=
  SelectedCaseNativeReplay.witnessed_derivable

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.NativeReplay
