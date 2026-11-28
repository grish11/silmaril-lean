module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Proofs

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.RVSDG (Origin Wires)
open Silmaril.SSA.RVSDG.NestedTheta.Equality (addresses_injective)

private theorem origin_eq {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    {lhs rhs : Origin args past t} (same : lhs.address = rhs.address) : lhs = rhs := by
  let left : Wires args past [t] := .cons lhs .nil
  let right : Wires args past [t] := .cons rhs .nil
  exact congrArg (fun w => w.get .head)
    (addresses_injective left right (congrArg List.singleton same))

private theorem table_eq {args : List PortTy} {past sigs : List (List PortTy)}
    (left : Dataflow WordOp args past sigs) :
    ∀ {otherSigs} (right : Dataflow WordOp args past otherSigs), tableCode left = tableCode right →
      ∃ eq : sigs = otherSigs, eq ▸ left = right := by
  induction left with
  | nil =>
    intro otherSigs right same
    cases right with
    | nil => exact ⟨rfl, rfl⟩
    | cons => cases same
  | cons op operands rest ih =>
    intro otherSigs right same
    cases right with
    | nil => cases same
    | cons other otherOperands tail =>
      obtain ⟨headEq, tailEq⟩ := List.cons.inj same
      obtain ⟨opEq, operandsEq⟩ := Prod.mk.inj headEq
      cases op <;> cases other <;> cases opEq
      all_goals
        obtain rfl := addresses_injective _ _ operandsEq
        obtain ⟨rfl, rfl⟩ := ih _ tailEq
        exact ⟨rfl, rfl⟩

private theorem graph_eq {arity : Nat} {sigs : List (List PortTy)}
    {left right : BankGraph arity sigs} (header : left.header = right.header)
    (phi : left.phiInputs = right.phiInputs) (predicate : left.predicate = right.predicate)
    (result : left.result = right.result) : left = right := by
  cases left with
  | mk preA bodyA phiA predA resA =>
    cases right with
    | mk preB bodyB phiB predB resB =>
      cases preA; cases preB; cases header; cases phi; cases predicate; cases result
      rfl

private theorem graphCode_eq {arity : Nat} {leftSigs rightSigs : List (List PortTy)}
    {left : BankGraph arity leftSigs} {right : BankGraph arity rightSigs}
    (same : graphCode left = graphCode right) : ∃ eq : leftSigs = rightSigs, eq ▸ left = right := by
  obtain ⟨rfl, header⟩ := table_eq left.header right.header (congrArg GraphCode.header same)
  refine ⟨rfl, graph_eq header ?_ (origin_eq (congrArg GraphCode.predicate same))
    (origin_eq (congrArg GraphCode.result same))⟩
  funext edge
  cases edge with
  | entry => exact addresses_injective _ _ (congrArg GraphCode.entry same)
  | backedge => exact addresses_injective _ _ (congrArg GraphCode.feedback same)

theorem recognize_sound {arity : Nat} {sigs : List (List PortTy)}
    {g : BankGraph arity sigs} {spec : Spec} (recognized : recognize g = some spec) :
    ∃ p, Rows.checkPlan arity spec = some p ∧ ∃ eq : p.sigs = sigs, eq ▸ p.graph = g := by
  unfold recognize at recognized
  cases decoded : Decode.spec arity (graphCode g) with
  | none => simp [decoded] at recognized
  | some candidate =>
    cases checked : Rows.checkPlan arity candidate with
    | none => simp [decoded, checked] at recognized
    | some p =>
      simp only [decoded, checked, Option.bind_some] at recognized
      split at recognized
      · rename_i same
        cases Option.some.inj recognized
        exact ⟨p, checked, graphCode_eq same.symm⟩
      · cases recognized

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Proofs
