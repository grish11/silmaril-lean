module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms

/-! # A poll with distinct inner and outer recurrence exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.GenerationExample

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.PackedBody (applyPacked applyPacked_typed)
open SyntacticCategory (iterateRegion iterateRegion_valueBranches)

abbrev State : Ty Empty := .coprod .unit .unit
abbrev Result : Ty Empty := .product .unit .unit
abbrev PollResult : Ty Empty := .coprod (.coprod Result State) State

inductive Op where
  | refresh
  | poll

instance : HasTy Op (Ty Empty) where
  src
    | .refresh => State
    | .poll => .product State State
  trg
    | .refresh => State
    | .poll => PollResult

instance : HasEff Op Bool where
  eff _ := true

def poll : Region Op := returnRegion (.op Op.poll (.var 0))

theorem poll_typed : ValueBranches [Ty.product State State] poll [PollResult] :=
  returnRegion_typed (.op (f := Op.poll) (.var (i := 0) rfl))

theorem refresh_typed : Tm.HasType [State] (.op Op.refresh (.var 0)) State :=
  .op (f := Op.refresh) (.var (i := 0) rfl)

/-- Run the refresh once and pass both the retained and updated state to the poll. -/
def round : Region Op := .let₁ (.op Op.refresh (.var 0)) (applyPacked poll)

theorem round_typed : ValueBranches [State] round [PollResult] :=
  .let₁ refresh_typed (applyPacked_typed poll_typed)

/-- The rightmost reply re-enters this inner CFG. The other replies return
a result or a request for another outer round. -/
def inner : Region Op := iterateRegion State round

theorem inner_typed : ValueBranches [State] inner [Ty.coprod Result State] :=
  iterateRegion_valueBranches round_typed

/-- Enter the inner CFG on every outer recurrence. -/
def nested : Region Op := iterateRegion State inner

theorem nested_typed : ValueBranches [State] nested [Result] :=
  iterateRegion_valueBranches inner_typed

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.GenerationExample
