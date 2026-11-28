module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms

/-! # Generated refinement for a CFG with a two-label backedge -/

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG

namespace LambdaSSAUBFiniteCFGRegression

private abbrev U : Silmaril.Ty Empty := .unit
private abbrev Output : Silmaril.Ty Empty := .coprod U (Packet U 2)
private abbrev State := Fin 7
private abbrev unitPayload : Payload U := ⟨.unit, .unit⟩

private inductive Instr where
  | first
  | second

local instance : HasTy Instr (Silmaril.Ty Empty) := ⟨fun _ => U, fun _ => .coprod Output U⟩

private def replyJump (label : Fin 2) (s : State) : Reply (.coprod Output U) 7 :=
  let packet := pack label unitPayload
  .ret ⟨.inl (.inr packet.val), .inl (.inr packet.property)⟩ s

private def replyExit (s : State) : Reply (.coprod Output U) 7 :=
  .ret ⟨.inl (.inl .unit), .inl (.inl .unit)⟩ s

private def primitive : Primitives Instr 7
  | .first, _, s =>
    match s.val with
    | 0 => replyJump 1 1
    | 2 => .ret ⟨.inr .unit, .inr .unit⟩ 2
    | 3 => replyJump 1 3
    | 4 => .fault 5
    | 5 => .diverge
    | _ => replyExit s
  | .second, _, s =>
    match s.val with
    | 1 => replyJump 0 2
    | 3 => replyJump 0 3
    | _ => replyExit s

private def cfg (withUB : Bool) : Blocks Instr U U U 2 where
  block i :=
    .call (if i = 0 then .first else .second) (.var 0)
      (.case (.var 0) (.ret (.var 0)) (if withUB then .ub else .ret (.inl .unit)))

private def unitCode : Fin 1 ≃ Payload U where
  toFun _ := unitPayload
  invFun _ := 0
  left_inv i := (Fin.eq_zero i).symm
  right_inv a := by
    obtain ⟨_, h⟩ := a
    cases h
    rfl

private def codes : Codes U U U 1 1 1 := ⟨fun _ => unitPayload, unitCode, unitCode⟩

private abbrev table (withUB : Bool) := (cfg withUB).generate codes primitive
private abbrev code (label : Fin 2) (s : State) := encode codes label unitPayload s
private abbrev env := emptyBindings.push unitPayload

private noncomputable abbrev observed (withUB : Bool) (label : Fin 2) (s : State) :=
  Shape.denote ((cfg withUB).region label .unit) (model primitive env) s

private theorem changing_backedge :
    table true 0 (code 0 0) = .repeat (code 1 1) ∧
    table true 0 (code 1 1) = .repeat (code 0 2) ∧
    table true 0 (code 0 2) = .stop .ub :=
  ⟨rfl, rfl, rfl⟩

private theorem silent_cycle_rows :
    table true 0 (code 0 3) = .repeat (code 1 3) ∧
    table true 0 (code 1 3) = .repeat (code 0 3) :=
  ⟨rfl, rfl⟩

private theorem exact_sum_agreement (withUB : Bool) (label : Fin 2) (s : State) :
    observed withUB label s =
      (iterateSum ((cfg withUB).step primitive unitPayload)).run 0 (pack label unitPayload) s :=
  region_eq_exactSum (cfg withUB) codes primitive 0 label .unit s

private theorem reaches_ub : observed true 0 0 = ⊤ :=
  (classify_region (cfg true) codes primitive 0 0 .unit 0).trans rfl

private theorem returns_after_backedge : observed false 0 0 = returnPayload .unit (2 : State) :=
  (classify_region (cfg false) codes primitive 0 0 .unit 0).trans rfl

private theorem other_start_exits : observed true 0 6 = returnPayload .unit (6 : State) :=
  (classify_region (cfg true) codes primitive 0 0 .unit 6).trans rfl

private theorem silent_cycle :
    observed true 0 3 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) :=
  (classify_region (cfg true) codes primitive 0 0 .unit 3).trans rfl

private theorem fault_preserves_state : observed true 0 4 = WithTop.some {Outcome.fault (5 : State)} :=
  (classify_region (cfg true) codes primitive 0 0 .unit 4).trans rfl

private theorem primitive_divergence :
    observed true 0 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) :=
  (classify_region (cfg true) codes primitive 0 0 .unit 5).trans rfl

private theorem checked_refinement (i : Fin 2) (s : State) : observed false i s ≤ observed true i s :=
  (check_region_iff (cfg false) (cfg true) codes primitive).mp (by decide) 0 i .unit s

private theorem reverse_check_fails : check (table true) (table false) = false := by decide

#print axioms classify_region
#print axioms region_eq_exactSum
#print axioms check_region_iff
#print axioms changing_backedge
#print axioms silent_cycle_rows
#print axioms exact_sum_agreement
#print axioms reaches_ub
#print axioms returns_after_backedge
#print axioms other_start_exits
#print axioms silent_cycle
#print axioms fault_preserves_state
#print axioms primitive_divergence
#print axioms checked_refinement
#print axioms reverse_check_fails

end LambdaSSAUBFiniteCFGRegression
