module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Institution.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Mathlib.Tactic.FinCases

/-! # Recognize a native packed cycle and check its actual entry -/

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Payload Primitives Reply emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)

namespace LambdaSSAUBNativePackedRegression

private abbrev U : Silmaril.Ty Empty := .unit
private abbrev P : Silmaril.Ty Empty := .product U U
private abbrev Internal : List (Silmaril.Ty Empty) := [U, P]
private abbrev External : List (Silmaril.Ty Empty) := [U, U]
private abbrev Output : Silmaril.Ty Empty := .coprod (packedExitType External) (packedExitType Internal)
private abbrev State := Fin 6

private abbrev uval : Payload U := ⟨.unit, .unit⟩
private abbrev pval : Payload P := pairPayload uval uval

private theorem unit_payload (p : Payload U) : p = uval := by
  obtain ⟨_, h⟩ := p
  cases h
  rfl

private theorem product_payload (p : Payload P) : p = pval := by
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
      rw [product_payload a]
      rfl

private def exits : Fin 2 ≃ Packet External where
  toFun := Fin.cases ⟨0, uval⟩ (fun _ => ⟨1, uval⟩)
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
      rw [unit_payload a]
      rfl

private def codes : Codes U Internal External 1 2 2 := ⟨fun _ => uval, seeds, exits⟩

private inductive Instr where
  | unitBlock
  | productBlock
  deriving DecidableEq

local instance : HasTy Instr (Silmaril.Ty Empty) :=
  ⟨fun f => match f with | .unitBlock => U | .productBlock => P, fun _ => Output⟩

private def replyJump (p : Packet Internal) (s : State) : Reply Output 6 :=
  let a := pack p
  .ret ⟨.inr a.val, .inr a.property⟩ s

private def replyExit (p : Packet External) (s : State) : Reply Output 6 :=
  let a := pack p
  .ret ⟨.inl a.val, .inl a.property⟩ s

private def primitive : Primitives Instr 6
  | .unitBlock, _, s =>
    match s.val with
    | 0 => replyJump ⟨1, pval⟩ 1
    | 3 => replyJump ⟨1, pval⟩ 3
    | 4 => .fault 5
    | 5 => .diverge
    | _ => replyExit ⟨0, uval⟩ s
  | .productBlock, _, s =>
    match s.val with
    | 1 => replyJump ⟨0, uval⟩ 2
    | 3 => replyJump ⟨0, uval⟩ 3
    | 4 => .fault 5
    | 5 => .diverge
    | _ => replyExit ⟨1, uval⟩ 2

/-- This source is written in the native syntax, including the local link. -/
private def producer (f : Instr) : Native.Typed Instr [instrSrc f, U] [Output] :=
  ⟨.cfg (.br 0 (.op f (.var 0))) 1 (fun _ => .br 1 (.var 0)),
    .cfg (fun _ : Fin 1 => Output)
      (.br (ℓ := 0) rfl (.op (f := f) (.var (i := 0) rfl)))
      (fun _ => .br (ℓ := 1) rfl (.var (i := 0) rfl))⟩

private def paddedRoute {Γ : List (Silmaril.Ty Empty)} :
    Native.Typed Instr (Output :: Γ) (Internal ++ External) :=
  let k := Native.route Internal External (Γ := Γ) (Φ := Instr)
  ⟨.let₁ .unit (k.val.renameVars Nat.succ),
    .let₁ .unit (k.property.renameVars (LambdaSSA.Ren.wk (Output :: Γ) U))⟩

private def twicePaddedRoute {Γ : List (Silmaril.Ty Empty)} :
    Native.Typed Instr (Output :: Γ) (Internal ++ External) :=
  let k := Native.route Internal External (Γ := Γ) (Φ := Instr)
  let weaken := LambdaSSA.Ren.comp (LambdaSSA.Ren.wk (Output :: Γ) U)
    (LambdaSSA.Ren.wk (U :: Output :: Γ) U)
  ⟨.let₁ .unit (.let₁ .unit (k.val.renameVars (Nat.succ ∘ Nat.succ))),
    .let₁ .unit (.let₁ .unit (k.property.renameVars weaken))⟩

private def binderUsingRoute :
    Native.Typed Instr [Output, U, U] (Internal ++ External) :=
  ⟨.let₁ .unit (.br 3 (.var 0)), .let₁ .unit (.br (ℓ := 3) rfl (.var (i := 0) rfl))⟩

private def outerUnitUsingRoute :
    Native.Typed Instr [Output, U, U] (Internal ++ External) :=
  ⟨.let₁ .unit (.let₁ .unit (.br 3 (.var 1))),
    .let₁ .unit (.let₁ .unit (.br (ℓ := 3) rfl (.var (i := 1) rfl)))⟩

private def fixtureWithRouter (productEntry : Bool)
    (router : Native.Typed Instr [Output, U, U] (Internal ++ External)) :
    Native.Typed Instr [U] External :=
  let entry : Native.Typed Instr [U] (Internal ++ External) :=
    if productEntry then ⟨.br 1 (.pair .unit .unit), .br (ℓ := 1) rfl (.pair .unit .unit)⟩
    else ⟨.br 0 .unit, .br (ℓ := 0) rfl .unit⟩
  let blocks (j : Fin Internal.length) : Native.Typed Instr [Internal.get j, U] (Internal ++ External) :=
    Fin.cases (motive := fun i => Native.Typed Instr [Internal.get i, U] (Internal ++ External))
      (Native.bind (producer .unitBlock) router)
      (Fin.cases (motive := fun i : Fin 1 => Native.Typed Instr [Internal.get i.succ, U] (Internal ++ External))
        (Native.bind (producer .productBlock) (Native.route Internal External)) (fun i => i.elim0)) j
  ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩

private def fixture (productEntry modified : Bool) : Native.Typed Instr [U] External :=
  fixtureWithRouter productEntry (if modified then paddedRoute else Native.route Internal External)

private abbrev source := fixture false false
private abbrev target := fixture true false
private abbrev paddedCFG := fixture false true

private def readSource : Native.Readback Instr U Internal External :=
  (Native.recognize Internal source).get (by decide)

private def readTarget : Native.Readback Instr U Internal External :=
  (Native.recognize Internal target).get (by decide)

private theorem recognizes_source : Native.recognize Internal source = some readSource := rfl
private theorem recognizes_target : Native.recognize Internal target = some readTarget := rfl

private theorem exact_readback_rejects_redundant_binder : Native.recognize Internal paddedCFG = none := rfl

private theorem proposed_before_router_check :
    Native.propose (X := U) Internal External paddedCFG.val = some readSource := rfl

private abbrev usesBinder := fixtureWithRouter false binderUsingRoute

private theorem padded_has_normal_form : Native.normalizeRouterUnits Internal paddedCFG = some source := by
  calc
    _ = some readSource.typed := rfl
    _ = _ := congrArg some (Native.recognized_eq recognizes_source).symm

private theorem recognizes_unused_binder :
    Native.recognizeRouterUnits Internal paddedCFG = some readSource := rfl

private theorem recognizes_other_entry :
    Native.recognizeRouterUnits Internal target = some readTarget := rfl

private theorem read_producer_before_binder_check :
    Native.propose (X := U) Internal External usesBinder.val = some readSource := rfl

private theorem rejects_use_of_bound_unit :
    Native.hasRouterUnit usesBinder.val 0 = true ∧
      Native.recognizeRouterUnits Internal usesBinder = none :=
  ⟨rfl, rfl⟩

private abbrev twicePaddedCFG := fixtureWithRouter false twicePaddedRoute
private abbrev usesOuterUnit := fixtureWithRouter false outerUnitUsingRoute

private theorem counts_two_binders : Native.routerUnitDepth twicePaddedCFG.val 0 = 2 := rfl

private theorem twice_padded_has_normal_form :
    Native.normalizeRouterUnits Internal twicePaddedCFG = some source := by
  calc
    _ = some readSource.typed := rfl
    _ = _ := congrArg some (Native.recognized_eq recognizes_source).symm

private theorem recognizes_nested_unused_binders :
    Native.recognizeRouterUnits Internal twicePaddedCFG = some readSource := rfl

private theorem rejects_use_of_outer_unit :
    Native.propose (X := U) Internal External usesOuterUnit.val = some readSource ∧
      Native.routerUnitDepth usesOuterUnit.val 0 = 2 ∧
      Native.recognizeRouterUnits Internal usesOuterUnit = none :=
  ⟨rfl, rfl, rfl⟩

private abbrev code (p : Packet Internal) (s : State) := codes.invocation.symm (p, s)
private abbrev table := readSource.blocks.generate codes primitive
private abbrev env := emptyBindings.push uval

private theorem cross_typed_backedge :
    table 0 (code ⟨0, uval⟩ 0) = .repeat (code ⟨1, pval⟩ 1) ∧
    table 0 (code ⟨1, pval⟩ 1) = .repeat (code ⟨0, uval⟩ 2) :=
  ⟨rfl, rfl⟩

private noncomputable abbrev observed (raw : Native.Typed Instr [U] External) (s : State) :=
  Shape.denote (.native raw) (model primitive env) s

private theorem exit_after_backedge :
    observed source 0 = WithTop.some {Outcome.ret 0 .unit (2 : State)} :=
  (Native.classify_recognized recognizes_source codes primitive 0 0).trans rfl

private theorem distinct_entry_exit :
    observed target 0 = WithTop.some {Outcome.ret 1 .unit (2 : State)} :=
  (Native.classify_recognized recognizes_target codes primitive 0 0).trans rfl

private theorem silent_replay :
    observed source 3 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (Native.classify_recognized recognizes_source codes primitive 0 3).trans rfl

private theorem fault_state : observed source 4 = WithTop.some {Outcome.fault (5 : State)} :=
  (Native.classify_recognized recognizes_source codes primitive 0 4).trans rfl

private theorem in_step_divergence :
    observed source 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (Native.classify_recognized recognizes_source codes primitive 0 5).trans rfl

private theorem rejects_distinct_native_entry :
    Native.check readSource readTarget codes primitive = false := by decide

private theorem rejected_refinement : ¬ ∀ s, observed source s ≤ observed target s := by
  intro ordered
  have checked := (Native.check_recognized_iff recognizes_source recognizes_target codes primitive).mpr
    (fun _ s => ordered s)
  rw [rejects_distinct_native_entry] at checked
  cases checked

private theorem normalized_all_states (s : State) : observed twicePaddedCFG s = observed source s :=
  Native.normalizeRouterUnits_denote twice_padded_has_normal_form (model primitive env) s

private theorem normalized_exit_after_backedge :
    observed twicePaddedCFG 0 = WithTop.some {Outcome.ret 0 .unit (2 : State)} :=
  (Native.classify_recognizedRouterUnits recognizes_nested_unused_binders codes primitive 0 0).trans rfl

private theorem normalized_replay :
    observed twicePaddedCFG 3 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (normalized_all_states 3).trans silent_replay

private theorem normalized_fault :
    observed twicePaddedCFG 4 = WithTop.some {Outcome.fault (5 : State)} :=
  (normalized_all_states 4).trans fault_state

private theorem normalized_primitive_divergence :
    observed twicePaddedCFG 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (normalized_all_states 5).trans in_step_divergence

private theorem normalized_replay_is_ordinary : observed twicePaddedCFG 3 ≠ ⊤ := by
  rw [normalized_replay]
  exact WithTop.coe_ne_top

private def ubAtFirst (i : Fin External.length) : Region Instr (External.get i :: [U]) [U] :=
  if i = 0 then .ub else .native ⟨.br 0 .unit, .br (ℓ := 0) rfl .unit⟩

private theorem normalized_return_reaches_overlay_ub :
    Shape.denote (.lsubst (.native twicePaddedCFG) ubAtFirst) (model primitive env) 0 = ⊤ := by
  change Behaviour.bind (observed twicePaddedCFG 0) _ = ⊤
  apply Behaviour.bind_eq_top_of_reaches_top (i := (0 : Fin 2)) (a := .unit) (s := (2 : State))
  · rw [normalized_exit_after_backedge]
    simp [Behaviour.possible]
  · rfl

private theorem normalized_replay_skips_overlay_ub :
    Shape.denote (.lsubst (.native twicePaddedCFG) ubAtFirst) (model primitive env) 3 =
      WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) := by
  change Behaviour.bind (observed twicePaddedCFG 3) _ = _
  rw [normalized_replay]
  exact Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.diverge_bind _

private theorem normalized_rejects_distinct_entry : ¬ ∀ s, observed twicePaddedCFG s ≤ observed target s := by
  intro ordered
  have checked :=
    (Native.check_recognizedRouterUnits_iff recognizes_nested_unused_binders recognizes_other_entry codes primitive).mpr
      (fun _ s => ordered s)
  rw [rejects_distinct_native_entry] at checked
  cases checked

private def sharedExit : Primitives Instr 6 := fun _ _ s =>
  match s.val with
  | 4 => .fault 5
  | 5 => .diverge
  | _ => replyExit ⟨0, uval⟩ s

private theorem accepted_institution_refinement :
    let M := model sharedExit env
    ((Institution.Observational.lambdaSSA Instr External.length).room [U].length).Sat
      (CategoryTheory.Discrete.mk M.raw)
      (.le ⟨twicePaddedCFG.val, twicePaddedCFG.property.scoped⟩ ⟨target.val, target.property.scoped⟩) :=
  (Native.check_satisfies_iff recognizes_nested_unused_binders recognizes_other_entry codes sharedExit).mp
    (by decide) 0

private theorem finds_changed_exit : Native.counterexample readSource readTarget codes primitive = some (0, 0) :=
  rfl

private theorem actual_entry_counterexample : ¬ observed twicePaddedCFG 0 ≤ observed target 0 :=
  Native.counterexample_point recognizes_nested_unused_binders recognizes_other_entry codes primitive finds_changed_exit

private theorem refutes_all_models : ¬ LambdaSSA.UB.Refines.{0,0,0,0} twicePaddedCFG target :=
  Native.counterexample_refutes recognizes_nested_unused_binders recognizes_other_entry codes primitive finds_changed_exit

private theorem missing_ordered_return :
    let M := (model primitive env).raw
    let outcome := Institution.Observational.Observation.ret (0 : State) ((0 : Nat), Value.unit) (2 : State)
    outcome ∈ LambdaSSA.UB.observe M twicePaddedCFG ∧ outcome ∉ LambdaSSA.UB.observe M target := by
  change Outcome.ret (0 : Fin 2) .unit (2 : State) ∈ (observed twicePaddedCFG 0).possible ∧
    Outcome.ret (0 : Fin 2) .unit (2 : State) ∉ (observed target 0).possible
  rw [normalized_exit_after_backedge, distinct_entry_exit]
  simp [Behaviour.possible]

private def firstExit (i : Fin External.length) : Bool := i == 0
private def noExit (_ : Fin External.length) : Bool := false

private noncomputable abbrev observedExitUB (raw : Native.Typed Instr [U] External)
    (selected : Fin External.length → Bool) (s : State) :=
  Shape.denote (Native.withExitUB raw selected) (model primitive env) s

private theorem selected_exit_is_top :
    observedExitUB twicePaddedCFG firstExit 0 = ⊤ :=
  (Native.classify_exitUB recognizes_nested_unused_binders firstExit codes primitive 0 0).trans rfl

private theorem same_payload_at_other_exit :
    observedExitUB target firstExit 0 = WithTop.some {Outcome.ret 1 .unit (2 : State)} :=
  (Native.classify_exitUB recognizes_other_entry firstExit codes primitive 0 0).trans rfl

private theorem exit_ub_preserves_replay :
    observedExitUB twicePaddedCFG firstExit 3 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (Native.classify_exitUB recognizes_nested_unused_binders firstExit codes primitive 0 3).trans rfl

private theorem exit_ub_preserves_fault_state :
    observedExitUB twicePaddedCFG firstExit 4 = WithTop.some {Outcome.fault (5 : State)} :=
  (Native.classify_exitUB recognizes_nested_unused_binders firstExit codes primitive 0 4).trans rfl

private theorem exit_ub_preserves_primitive_divergence :
    observedExitUB twicePaddedCFG firstExit 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (Native.classify_exitUB recognizes_nested_unused_binders firstExit codes primitive 0 5).trans rfl

private theorem accepts_ub_on_right (s : State) :
    observed twicePaddedCFG s ≤ observedExitUB twicePaddedCFG firstExit s := by
  calc
    observed twicePaddedCFG s = observedExitUB twicePaddedCFG noExit s :=
      (Native.denote_noExitUB twicePaddedCFG (model primitive env) s).symm
    _ ≤ _ := (Native.checkExitUB_iff recognizes_nested_unused_binders recognizes_nested_unused_binders
      noExit firstExit codes primitive).mp (by decide) 0 s

private theorem rejects_ub_on_left :
    Native.checkExitUB readSource readSource firstExit noExit codes primitive = false := by decide

private theorem ub_on_left_counterexample :
    ¬ observedExitUB twicePaddedCFG firstExit 0 ≤ observed twicePaddedCFG 0 := by
  intro le
  have rejected := Native.counterexampleExitUB_point recognizes_nested_unused_binders
    recognizes_nested_unused_binders firstExit noExit codes primitive (c := 0) (s := 0) rfl
  exact rejected (le.trans (Native.denote_noExitUB twicePaddedCFG (model primitive env) 0).ge)

#print axioms Native.recognized_eq
#print axioms Native.readback_agrees
#print axioms Native.generated_native_row
#print axioms Native.classify_recognized
#print axioms Native.check_recognized_iff
#print axioms recognizes_source
#print axioms exact_readback_rejects_redundant_binder
#print axioms proposed_before_router_check
#print axioms cross_typed_backedge
#print axioms exit_after_backedge
#print axioms distinct_entry_exit
#print axioms silent_replay
#print axioms fault_state
#print axioms in_step_divergence
#print axioms rejected_refinement

#print axioms Native.normalizeRouterUnits_equiv
#print axioms Native.normalizeRouterUnits_denote
#print axioms Native.classify_recognizedRouterUnits
#print axioms Native.check_recognizedRouterUnits_iff
#print axioms recognizes_unused_binder
#print axioms rejects_use_of_bound_unit
#print axioms counts_two_binders
#print axioms twice_padded_has_normal_form
#print axioms recognizes_nested_unused_binders
#print axioms rejects_use_of_outer_unit
#print axioms normalized_exit_after_backedge
#print axioms normalized_replay
#print axioms normalized_fault
#print axioms normalized_primitive_divergence
#print axioms normalized_replay_is_ordinary
#print axioms normalized_return_reaches_overlay_ub
#print axioms normalized_replay_skips_overlay_ub
#print axioms normalized_rejects_distinct_entry

#print axioms Native.check_satisfies_iff
#print axioms Native.counterexample_eq_none_iff
#print axioms Native.counterexample_point
#print axioms Native.counterexample_refutes
#print axioms accepted_institution_refinement
#print axioms finds_changed_exit
#print axioms actual_entry_counterexample
#print axioms refutes_all_models
#print axioms missing_ordered_return

#print axioms Native.denote_noExitUB
#print axioms Native.classify_exitUB
#print axioms Native.checkExitUB_iff
#print axioms Native.counterexampleExitUB_point
#print axioms selected_exit_is_top
#print axioms same_payload_at_other_exit
#print axioms exit_ub_preserves_replay
#print axioms exit_ub_preserves_fault_state
#print axioms exit_ub_preserves_primitive_divergence
#print axioms accepts_ub_on_right
#print axioms rejects_ub_on_left
#print axioms ub_on_left_counterexample

end LambdaSSAUBNativePackedRegression
