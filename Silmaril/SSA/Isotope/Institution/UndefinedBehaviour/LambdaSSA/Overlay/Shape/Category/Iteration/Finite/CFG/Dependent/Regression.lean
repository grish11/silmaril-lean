module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Mathlib.Tactic.FinCases

/-! # A heterogeneous cycle and same-payload returns at distinct positions -/

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Payload Primitives Program Reply Expr emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)

namespace LambdaSSAUBDependentCFGRegression

private abbrev U : Silmaril.Ty Empty := .unit
private abbrev P : Silmaril.Ty Empty := .product U U
private abbrev Internal : List (Silmaril.Ty Empty) := [U, P]
private abbrev External : List (Silmaril.Ty Empty) := [U, U, P]
private abbrev Output : Silmaril.Ty Empty := .coprod (packedExitType External) (packedExitType Internal)
private abbrev State := Fin 7

private abbrev uval : Payload U := ⟨.unit, .unit⟩
private abbrev pval : Payload P := pairPayload uval uval

private theorem unit_payload (p : Payload U) : p = uval := by
  obtain ⟨_, h⟩ := p
  cases h
  rfl

private theorem pair_payload (p : Payload P) : p = pval := by
  obtain ⟨_, h⟩ := p
  cases h with
  | pair a b => cases a; cases b; rfl

private def seeds : Fin 2 ≃ Packet Internal where
  toFun := Fin.cases ⟨0, uval⟩ (fun _ => ⟨1, pval⟩)
  invFun p := p.1
  left_inv i := by fin_cases i <;> rfl
  right_inv := by
    rintro ⟨i, a⟩
    revert a
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a
      rw [unit_payload a]
      rfl
    · intro a
      obtain rfl := Fin.eq_zero j
      rw [pair_payload a]
      rfl

private def exits : Fin 3 ≃ Packet External where
  toFun := Fin.cases ⟨0, uval⟩ (Fin.cases ⟨1, uval⟩ (fun _ => ⟨2, pval⟩))
  invFun p := p.1
  left_inv i := by fin_cases i <;> rfl
  right_inv := by
    rintro ⟨i, a⟩
    revert a
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_)) i
    · intro a
      rw [unit_payload a]
      rfl
    · intro a
      rw [unit_payload a]
      rfl
    · intro a
      obtain rfl := Fin.eq_zero j
      rw [pair_payload a]
      rfl

private def codes : Codes U Internal External 1 2 3 := ⟨fun _ => uval, seeds, exits⟩

private inductive Instr where
  | first
  | second

local instance : HasTy Instr (Silmaril.Ty Empty) :=
  ⟨fun f => match f with | .first => U | .second => P, fun _ => .coprod Output U⟩

private def replyJump (p : Packet Internal) (s : State) : Reply (.coprod Output U) 7 :=
  let a := pack p
  .ret ⟨.inl (.inr a.val), .inl (.inr a.property)⟩ s

private def replyExit (p : Packet External) (s : State) : Reply (.coprod Output U) 7 :=
  let a := pack p
  .ret ⟨.inl (.inl a.val), .inl (.inl a.property)⟩ s

private def primitive : Primitives Instr 7
  | .first, _, s =>
    match s.val with
    | 0 => replyJump ⟨1, pval⟩ 1
    | 2 => .ret ⟨.inr .unit, .inr .unit⟩ 2
    | 3 => replyJump ⟨1, pval⟩ 3
    | 4 => .fault 5
    | 5 => .diverge
    | _ => replyExit ⟨2, pval⟩ s
  | .second, _, s =>
    match s.val with
    | 1 => replyJump ⟨0, uval⟩ 2
    | 3 => replyJump ⟨0, uval⟩ 3
    | _ => replyExit ⟨0, uval⟩ s

private def body (f : Instr) (withUB secondExit : Bool) : Program Instr [instrSrc f, U] Output :=
  .call f (.var 0) (.case (.var 0) (.ret (.var 0))
    (if withUB then .ub else
      if secondExit then .ret (.inl (.inr (.inl .unit))) else .ret (.inl (.inl .unit))))

private def cfg (withUB secondExit : Bool) : Blocks Instr U Internal External where
  block := Fin.cases (motive := fun i => Program Instr [Internal.get i, U] Output)
    (body .first withUB secondExit)
    (Fin.cases (motive := fun j : Fin 1 => Program Instr [Internal.get j.succ, U] Output)
      (body .second withUB secondExit) (fun i => i.elim0))

private abbrev table (withUB secondExit : Bool) := (cfg withUB secondExit).generate codes primitive
private abbrev code (p : Packet Internal) (s : State) := codes.invocation.symm (p, s)
private abbrev env := emptyBindings.push uval

private noncomputable abbrev observed (withUB secondExit : Bool) (s : State) :=
  Shape.denote ((cfg withUB secondExit).region 0 .unit) (model primitive env) s

private theorem changing_heterogeneous_cycle :
    table true false 0 (code ⟨0, uval⟩ 0) = .repeat (code ⟨1, pval⟩ 1) ∧
    table true false 0 (code ⟨1, pval⟩ 1) = .repeat (code ⟨0, uval⟩ 2) ∧
    table true false 0 (code ⟨0, uval⟩ 2) = .stop .ub :=
  ⟨rfl, rfl, rfl⟩

private theorem silent_cycle_rows :
    table true false 0 (code ⟨0, uval⟩ 3) = .repeat (code ⟨1, pval⟩ 3) ∧
    table true false 0 (code ⟨1, pval⟩ 3) = .repeat (code ⟨0, uval⟩ 3) :=
  ⟨rfl, rfl⟩

private theorem reaches_ub : observed true false 0 = ⊤ :=
  (classify_region (cfg true false) codes primitive 0 0 .unit 0).trans rfl

private theorem exit_zero : observed false false 0 = WithTop.some {Outcome.ret 0 .unit (2 : State)} :=
  (classify_region (cfg false false) codes primitive 0 0 .unit 0).trans rfl

private theorem exit_one : observed false true 0 = WithTop.some {Outcome.ret 1 .unit (2 : State)} :=
  (classify_region (cfg false true) codes primitive 0 0 .unit 0).trans rfl

private theorem distinct_exit_observations : ¬ observed false false 0 ≤ observed false true 0 := by
  intro le
  rw [exit_zero, exit_one] at le
  have subset := WithTop.coe_le_coe.mp le
  have ret : Outcome.ret (0 : Fin 3) .unit (2 : State) ∈ {Outcome.ret 1 .unit (2 : State)} :=
    subset (by simp)
  exact (by decide : (0 : Fin 3) ≠ 1) (Outcome.ret.inj (Set.mem_singleton_iff.mp ret)).1

private theorem product_exit :
    observed true false 6 = WithTop.some {Outcome.ret 2 (.pair .unit .unit) (6 : State)} :=
  (classify_region (cfg true false) codes primitive 0 0 .unit 6).trans rfl

private theorem silent_divergence :
    observed true false 3 = WithTop.some ({Outcome.diverge} : Set (Outcome 3 Unit State)) :=
  (classify_region (cfg true false) codes primitive 0 0 .unit 3).trans rfl

private theorem ordinary_fault : observed true false 4 = WithTop.some {Outcome.fault (5 : State)} :=
  (classify_region (cfg true false) codes primitive 0 0 .unit 4).trans rfl

private theorem primitive_divergence :
    observed true false 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 3 Unit State)) :=
  (classify_region (cfg true false) codes primitive 0 0 .unit 5).trans rfl

private theorem packed_product_entry (s : State) :
    packBehaviour (L := External)
      (Shape.denote ((cfg true false).region 1 (.pair .unit .unit)) (model primitive env) s) =
      (iterateSum ((cfg true false).step primitive uval)).run 0 (pack ⟨1, pval⟩) s :=
  region_eq_exactSum (cfg true false) codes primitive 0 1 (.pair .unit .unit) s

private theorem checked_towards_ub (s : State) : observed false false s ≤ observed true false s :=
  (check_region_iff (cfg false false) (cfg true false) codes primitive).mp (by decide) 0 0 .unit s

private theorem rejects_same_payload_at_distinct_positions :
    check (table false false) (table false true) = false ∧
      check (table false true) (table false false) = false :=
  ⟨by decide, by decide⟩

#print axioms generated_row
#print axioms classify_region
#print axioms region_eq_exactSum
#print axioms check_region_iff
#print axioms changing_heterogeneous_cycle
#print axioms silent_cycle_rows
#print axioms reaches_ub
#print axioms exit_zero
#print axioms exit_one
#print axioms distinct_exit_observations
#print axioms product_exit
#print axioms silent_divergence
#print axioms ordinary_fault
#print axioms primitive_divergence
#print axioms packed_product_entry
#print axioms checked_towards_ub
#print axioms rejects_same_payload_at_distinct_positions

end LambdaSSAUBDependentCFGRegression
