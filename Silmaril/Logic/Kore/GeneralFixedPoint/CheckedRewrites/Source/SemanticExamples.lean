module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Thms
public import Mathlib.Tactic.FinCases

/-! Populated semantic controls for checked source rewrites.
The three-state model is specific to these examples; the general API still
accepts arbitrary inhabited sorted relational models. -/
@[expose] public section
noncomputable section
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.SemanticExamples
open Silmaril.Logic Silmaril.Logic.Kore.GeneralFixedPoint
open Predicates

inductive State where
  | start | left | right
  deriving DecidableEq, Inhabited

/-- Only declarations are shared. Every example checks its own original text. -/
def declarationText : String :=
  "[] module Branches sort Cfg{} [] " ++
  "symbol start{}():Cfg{} [] symbol left{}():Cfg{} [] symbol right{}():Cfg{} [] "

def namedSymbol (index : Nat) (name : String) : Kore.Modules.NamedSymbol :=
  ⟨⟨"Branches", index⟩, ⟨name, [], "Cfg"⟩⟩

def declaredScope : Kore.Modules.Scope :=
  ⟨[(⟨"Branches", 0⟩, "Cfg")],
    [namedSymbol 1 "start", namedSymbol 2 "left", namedSymbol 3 "right"], []⟩

/-- All sorts have a populated carrier. The three declared constants denote
three distinct singletons; this is an example interpretation, not a source law. -/
def model : Matching.GeneralFixedPoint.Model declaredScope.signature where
  carrier _ := State
  nonempty _ := ⟨.start⟩
  operation op _ :=
    if op.val.declaration.name = "start" then {State.start}
    else if op.val.declaration.name = "left" then {State.left}
    else {State.right}

def noCaptures : Env model [] := fun i => Fin.elim0 i

private theorem denote_start (n : Nat) (sets objects : Semantics.Values model) :
    Semantics.denote declaredScope model (n + 1) sets objects "Cfg" (.app "start" []) =
      some ({State.start} : Set State) := by
  change some {w : State | ∃ args : Fin 0 → State,
      (∀ i : Fin 0, args i ∈ (Fin.elim0 i : Set State)) ∧ w = State.start} =
    some ({State.start} : Set State)
  apply congrArg (some : Set State → Option (Set State))
  ext w
  constructor
  · rintro ⟨_, _, hw⟩
    exact hw
  · intro hw
    exact ⟨Fin.elim0, (fun i => Fin.elim0 i), hw⟩

private theorem denote_left (n : Nat) (sets objects : Semantics.Values model) :
    Semantics.denote declaredScope model (n + 1) sets objects "Cfg" (.app "left" []) =
      some ({State.left} : Set State) := by
  change some {w : State | ∃ args : Fin 0 → State,
      (∀ i : Fin 0, args i ∈ (Fin.elim0 i : Set State)) ∧ w = State.left} =
    some ({State.left} : Set State)
  apply congrArg (some : Set State → Option (Set State))
  ext w
  constructor
  · rintro ⟨_, _, hw⟩
    exact hw
  · intro hw
    exact ⟨Fin.elim0, (fun i => Fin.elim0 i), hw⟩

private theorem denote_right (n : Nat) (sets objects : Semantics.Values model) :
    Semantics.denote declaredScope model (n + 1) sets objects "Cfg" (.app "right" []) =
      some ({State.right} : Set State) := by
  change some {w : State | ∃ args : Fin 0 → State,
      (∀ i : Fin 0, args i ∈ (Fin.elim0 i : Set State)) ∧ w = State.right} =
    some ({State.right} : Set State)
  apply congrArg (some : Set State → Option (Set State))
  ext w
  constructor
  · rintro ⟨_, _, hw⟩
    exact hw
  · intro hw
    exact ⟨Fin.elim0, (fun i => Fin.elim0 i), hw⟩

private theorem raw_start (n : Nat) (a : Env model []) :
    rawValue model (n + 1) [] a "Cfg" (.app "start" []) = {State.start} := by
  simp only [rawValue, denote_start, Option.getD_some]

private theorem raw_left (n : Nat) (a : Env model []) :
    rawValue model (n + 1) [] a "Cfg" (.app "left" []) = {State.left} := by
  simp only [rawValue, denote_left, Option.getD_some]

private theorem raw_right (n : Nat) (a : Env model []) :
    rawValue model (n + 1) [] a "Cfg" (.app "right" []) = {State.right} := by
  simp only [rawValue, denote_right, Option.getD_some]

private theorem raw_bottom (a : Env model []) :
    rawValue model 8 [] a "Cfg" (.bottom "Cfg") = ∅ := by
  rfl

/-! Two installed competitors, one common source state, two different terminal
successors. The system below is projected from the actual accepted source. -/

def branchText : String := declarationText ++
  "axiom{} \\rewrites{Cfg{}}(start{}(),left{}()) [] " ++
  "axiom{} \\rewrites{Cfg{}}(start{}(),right{}()) [] endmodule []"

theorem branch_checked : (checkText "Cfg" 8 branchText).isSome = true := by
  decide +kernel

def branchPackage : Package "Cfg" 8 branchText :=
  (checkText "Cfg" 8 branchText).get branch_checked

/-- The ambient type computes to the original declaration-backed scope. -/
def branchModule : CheckedModule declaredScope "Cfg" :=
  branchPackage.definition.modules.get ⟨0, by decide +kernel⟩

def branchSystem : CheckedRewriteSystem declaredScope "Cfg" := branchModule.system

theorem branch_installed_origins :
    branchModule.axioms.map (fun r => (r.origin, r.isClaim)) =
      [(⟨"Branches", 4⟩, false), (⟨"Branches", 5⟩, false)] := by
  decide +kernel

/-- This characterizes all rule choices, not just one selected execution. -/
theorem branch_raw_step_iff (w v : State) :
    RawStep branchSystem model w v ↔
      w = .start ∧ (v = .left ∨ v = .right) := by
  constructor
  · rintro ⟨i, a, lhs, _, rhs⟩
    fin_cases i
    · change w ∈ rawValue model 8 [] a "Cfg" (.app "start" []) at lhs
      change v ∈ rawValue model 8 [] a "Cfg" (.app "left" []) at rhs
      rw [raw_start] at lhs
      rw [raw_left] at rhs
      exact ⟨lhs, Or.inl rhs⟩
    · change w ∈ rawValue model 8 [] a "Cfg" (.app "start" []) at lhs
      change v ∈ rawValue model 8 [] a "Cfg" (.app "right" []) at rhs
      rw [raw_start] at lhs
      rw [raw_right] at rhs
      exact ⟨lhs, Or.inr rhs⟩
  · rintro ⟨hw, hv | hv⟩
    · refine ⟨⟨0, by decide +kernel⟩, noCaptures, ?_, trivial, ?_⟩
      · change w ∈ rawValue model 8 [] noCaptures "Cfg" (.app "start" [])
        rw [raw_start]
        exact hw
      · change v ∈ rawValue model 8 [] noCaptures "Cfg" (.app "left" [])
        rw [raw_left]
        exact hv
    · refine ⟨⟨1, by decide +kernel⟩, noCaptures, ?_, trivial, ?_⟩
      · change w ∈ rawValue model 8 [] noCaptures "Cfg" (.app "start" [])
        rw [raw_start]
        exact hw
      · change v ∈ rawValue model 8 [] noCaptures "Cfg" (.app "right" [])
        rw [raw_right]
        exact hv

theorem two_distinct_successors :
    RawStep branchSystem model .start .left ∧
      RawStep branchSystem model .start .right ∧ State.left ≠ State.right := by
  exact ⟨(branch_raw_step_iff _ _).mpr ⟨rfl, Or.inl rfl⟩,
    (branch_raw_step_iff _ _).mpr ⟨rfl, Or.inr rfl⟩, by decide⟩

theorem left_terminal : ∀ v, ¬ RawStep branchSystem model .left v := by
  intro v edge
  have impossible := ((branch_raw_step_iff .left v).mp edge).1
  cases impossible

theorem right_terminal : ∀ v, ¬ RawStep branchSystem model .right v := by
  intro v edge
  have impossible := ((branch_raw_step_iff .right v).mp edge).1
  cases impossible

/-- An actual finite complete path witnesses that all-partial soundness is
not made vacuous by the absence of complete executions in this example. -/
def rightComplete : Reachability.Derivation.CompletePath (RawStep branchSystem model) where
  length := 1
  point n := match n with | 0 => .start | _ + 1 => .right
  edge := by
    intro i hi
    have zero : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
    subst i
    exact two_distinct_successors.2.1
  terminal := right_terminal

theorem branch_well_defined : RawWellDefined branchSystem model := by
  intro i a w _ _
  fin_cases i
  · refine ⟨State.left, ?_⟩
    change State.left ∈ rawValue model 8 [] a "Cfg" (.app "left" [])
    simpa only [raw_left] using
      (show State.left ∈ ({State.left} : Set State) from rfl)
  · refine ⟨State.right, ?_⟩
    change State.right ∈ rawValue model 8 [] a "Cfg" (.app "right" [])
    simpa only [raw_right] using
      (show State.right ∈ ({State.right} : Set State) from rfl)

/-- No claim captures are needed. The initial state fails the target, while
both terminal successors satisfy it. -/
def branchClaim : Reachability.Derivation.Claim (fun _ : Empty => Unit) State :=
  ⟨(fun _ w => w = .start), (fun _ w => w = .left ∨ w = .right)⟩

def noClaimCaptures : Reachability.Derivation.Assignment (fun _ : Empty => Unit) :=
  fun i => nomatch i

theorem initial_not_post : ¬ branchClaim.post noClaimCaptures State.start := by
  intro member
  rcases member with impossible | impossible <;> cases impossible

/-- Use the actual Step constructor: prove coverage and successor closure for
all installed native lowerings. No reachability conclusion is a premise. -/
def branch_derivation : Reachability.Derivation.Derives
    (lowerSchemes branchSystem model) ∅ ∅ branchClaim := by
  apply Reachability.Derivation.Derives.step
  · intro assignment w hw
    have edge : RawStep branchSystem model w .left :=
      (branch_raw_step_iff _ _).mpr ⟨hw, Or.inl rfl⟩
    obtain ⟨i, a, lhs, _⟩ := (induced_raw_iff_lowered branchSystem model w .left).mp edge
    exact ⟨i, a, lhs⟩
  · intro assignment i a w v _ lhs rhs
    have edge : RawStep branchSystem model w v :=
      (induced_raw_iff_lowered branchSystem model w v).mpr ⟨i, a, lhs, rhs⟩
    exact ((branch_raw_step_iff w v).mp edge).2

theorem branch_all_partial : Reachability.AllPartial (RawStep branchSystem model)
    (fun w => w = .left ∨ w = .right) .start :=
  derivation_sound branchSystem model branch_derivation branch_well_defined
    noClaimCaptures .start rfl

/-- Selecting only the left branch cannot discharge the actual Step rule's
all-competitor successor premise. The right installed rule is a counterexample. -/
theorem cannot_ignore_right : ¬ Reachability.RuleSystem.SuccessorsIn
    (lowerSchemes branchSystem model) (fun w => w = State.start)
    (fun w => w = State.left) := by
  intro closure
  have edge : RawStep branchSystem model .start .right :=
    (branch_raw_step_iff _ _).mpr ⟨rfl, Or.inr rfl⟩
  obtain ⟨i, a, lhs, rhs⟩ := (induced_raw_iff_lowered branchSystem model _ _).mp edge
  have impossible : State.right = State.left := closure i a .start .right rfl lhs rhs
  cases impossible

/-! An accepted bottom RHS is not a total rewrite. Syntax checking is separate
from the genuine semantic enabled-LHS/nonempty-RHS obligation. -/

def emptyText : String := declarationText ++
  "axiom{} \\rewrites{Cfg{}}(start{}(),\\bottom{Cfg{}}()) [] endmodule []"

theorem empty_checked : (checkText "Cfg" 8 emptyText).isSome = true := by
  decide +kernel

def emptyPackage : Package "Cfg" 8 emptyText :=
  (checkText "Cfg" 8 emptyText).get empty_checked

def emptyModule : CheckedModule declaredScope "Cfg" :=
  emptyPackage.definition.modules.get ⟨0, by decide +kernel⟩

def emptySystem : CheckedRewriteSystem declaredScope "Cfg" := emptyModule.system

/-- The actual raw LHS and guard are enabled at the populated start state. -/
theorem empty_rule_enabled :
    State.start ∈ rawValue model 8 [] noCaptures "Cfg"
      emptySystem.rules[0].checked.raw.lhs ∧
    rawPredicateTruth model 8 [] emptySystem.rules[0].checked.raw.guard noCaptures := by
  constructor
  · change State.start ∈ rawValue model 8 [] noCaptures "Cfg" (.app "start" [])
    simpa only [raw_start] using
      (show State.start ∈ ({State.start} : Set State) from rfl)
  · trivial

theorem empty_not_well_defined : ¬ RawWellDefined emptySystem model := by
  intro wellDefined
  obtain ⟨v, rhs⟩ := wellDefined ⟨0, by decide +kernel⟩ noCaptures .start
    empty_rule_enabled.1 empty_rule_enabled.2
  change v ∈ rawValue model 8 [] noCaptures "Cfg" (.bottom "Cfg") at rhs
  rw [raw_bottom] at rhs
  change False at rhs
  exact rhs

theorem empty_no_successor : ¬ ∃ v, RawStep emptySystem model .start v := by
  rintro ⟨v, i, a, _, _, rhs⟩
  fin_cases i
  change v ∈ rawValue model 8 [] a "Cfg" (.bottom "Cfg") at rhs
  rw [raw_bottom] at rhs
  change False at rhs
  exact rhs

/-! Whole-denotation equality differs from overlap. Both guarded declarations
are accepted; the equality guard is false and the membership guard is true. -/

def pairRaw : RawPattern :=
  .disj "Cfg" (.app "left" []) (.app "right" [])

private theorem denote_pair (n : Nat) (sets objects : Semantics.Values model) :
    Semantics.denote declaredScope model (n + 2) sets objects "Cfg" pairRaw =
      some (({State.left} : Set State) ∪ {State.right}) := by
  change (do
    let p ← Semantics.denote declaredScope model (n + 1) sets objects "Cfg" (.app "left" [])
    let q ← Semantics.denote declaredScope model (n + 1) sets objects "Cfg" (.app "right" [])
    pure (p ∪ q)) = some (({State.left} : Set State) ∪ {State.right})
  simp [denote_left, denote_right]

private theorem raw_pair (n : Nat) (a : Env model []) :
    rawValue model (n + 2) [] a "Cfg" pairRaw =
      ({State.left} : Set State) ∪ {State.right} := by
  simp only [rawValue, denote_pair, Option.getD_some]

def guardText : String := declarationText ++
  "axiom{} \\rewrites{Cfg{}}(\\and{Cfg{}}(start{}()," ++
  "\\equals{Cfg{},Cfg{}}(left{}(),\\or{Cfg{}}(left{}(),right{}()))),left{}()) [] " ++
  "axiom{} \\rewrites{Cfg{}}(\\and{Cfg{}}(start{}()," ++
  "\\in{Cfg{},Cfg{}}(left{}(),\\or{Cfg{}}(left{}(),right{}()))),right{}()) [] endmodule []"

theorem guards_checked : (checkText "Cfg" 8 guardText).isSome = true := by
  decide +kernel

def guardPackage : Package "Cfg" 8 guardText :=
  (checkText "Cfg" 8 guardText).get guards_checked

def guardModule : CheckedModule declaredScope "Cfg" :=
  guardPackage.definition.modules.get ⟨0, by decide +kernel⟩

def guardSystem : CheckedRewriteSystem declaredScope "Cfg" := guardModule.system

/-- The left singleton overlaps the two-element set but does not equal it. -/
theorem checked_equality_guard_false : ¬ rawPredicateTruth model 8 []
    guardSystem.rules[0].checked.raw.guard noCaptures := by
  change ¬ (rawValue model 8 [] noCaptures "Cfg" (.app "left" []) =
    rawValue model 8 [] noCaptures "Cfg" pairRaw)
  rw [raw_left, raw_pair]
  intro same
  have member : State.right ∈ ({State.left} : Set State) := by
    rw [same]
    exact Or.inr rfl
  change State.right = State.left at member
  cases member

theorem checked_membership_guard_true : rawPredicateTruth model 8 []
    guardSystem.rules[1].checked.raw.guard noCaptures := by
  change (rawValue model 8 [] noCaptures "Cfg" (.app "left" []) ∩
    rawValue model 8 [] noCaptures "Cfg" pairRaw).Nonempty
  rw [raw_left, raw_pair]
  exact ⟨State.left, rfl, Or.inl rfl⟩

/-- The same false equality guard disables the actual native lowered LHS. -/
theorem equality_native_lhs_disabled (w : State) :
    ¬ w ∈ guardSystem.rules[0].checked.lowerLhs.denote (expand model)
      noCaptures (fun i => Fin.elim0 i) := by
  intro enabled
  have raw := (lowerLhs_iff model guardSystem.rules[0].checked noCaptures w).mp enabled
  exact checked_equality_guard_false raw.2

/-- The overlap guard enables the actual second native LHS at start. -/
theorem membership_native_lhs_enabled :
    State.start ∈ guardSystem.rules[1].checked.lowerLhs.denote (expand model)
      noCaptures (fun i => Fin.elim0 i) := by
  apply (lowerLhs_iff model guardSystem.rules[1].checked noCaptures State.start).mpr
  constructor
  · change State.start ∈ rawValue model 8 [] noCaptures "Cfg" (.app "start" [])
    simpa only [raw_start] using
      (show State.start ∈ ({State.start} : Set State) from rfl)
  · exact checked_membership_guard_true

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.SemanticExamples
