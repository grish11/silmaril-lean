module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.SemanticExamples
public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Claim.Thms

@[expose] public section
noncomputable section
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.ParsedExamples
open Silmaril.Logic Silmaril.Logic.Kore.GeneralFixedPoint
open Predicates
open SemanticExamples

/-- Complete text with two competitors and two checked claims. The first
accepts both possible endpoints; the second wrongly excludes the right one. -/
def text : String := declarationText ++
  "axiom{} \\rewrites{Cfg{}}(start{}(),left{}()) [] " ++
  "axiom{} \\rewrites{Cfg{}}(start{}(),right{}()) [] " ++
  "claim{} \\rewrites{Cfg{}}(start{}(),\\or{Cfg{}}(left{}(),right{}())) [] " ++
  "claim{} \\rewrites{Cfg{}}(start{}(),left{}()) [] endmodule []"

theorem accepted : (checkText "Cfg" 8 text).isSome = true := by
  decide +kernel

def package : Package "Cfg" 8 text := (checkText "Cfg" 8 text).get accepted

def owner : CheckedModule declaredScope "Cfg" :=
  package.definition.modules.get ⟨0, by decide +kernel⟩

/-- Claims have their original positions and remain separate from rules. -/
theorem source_positions :
    owner.axioms.map (fun r => (r.origin.declarationIndex, r.isClaim)) = [(4, false), (5, false)] ∧
    owner.claims.map (fun r => (r.origin.declarationIndex, r.isClaim)) = [(6, true), (7, true)] := by
  decide +kernel

/-- Adding parsed claims does not change the actual transition system. -/
theorem same_rules : owner.system = branchSystem := by
  rfl

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


def good : ClaimSelection package :=
  ⟨owner, by exact List.mem_cons_self, owner.claims[0], by exact List.mem_cons_self⟩

def bad : ClaimSelection package :=
  ⟨owner, by exact List.mem_cons_self, owner.claims[1], by
    exact List.mem_cons_of_mem _ (List.mem_cons_self)⟩

theorem good_pre (a : Predicates.Env model []) (w : State) :
    (good.meaning model).pre a w ↔ w = .start := by
  change (w ∈ rawValue model 8 [] a "Cfg" (.app "start" []) ∧ True) ↔ _
  rw [raw_start]
  simp only [Set.mem_singleton_iff, and_true]

theorem good_post (a : Predicates.Env model []) (w : State) :
    (good.meaning model).post a w ↔ w = .left ∨ w = .right := by
  change w ∈ rawValue model 8 [] a "Cfg" pairRaw ↔ _
  rw [raw_pair]
  rfl

theorem bad_pre (a : Predicates.Env model []) (w : State) :
    (bad.meaning model).pre a w ↔ w = .start := by
  change (w ∈ rawValue model 8 [] a "Cfg" (.app "start" []) ∧ True) ↔ _
  rw [raw_start]
  simp only [Set.mem_singleton_iff, and_true]

theorem bad_post (a : Predicates.Env model []) (w : State) :
    (bad.meaning model).post a w ↔ w = .left := by
  change w ∈ rawValue model 8 [] a "Cfg" (.app "left" []) ↔ _
  rw [raw_left]
  rfl

theorem good_obligations : good.StepObligations model where
  coverage := by
    intro a w pre
    have edge : RawStep owner.system model w .left := by
      rw [same_rules]
      exact (branch_raw_step_iff _ _).mpr ⟨(good_pre a w).mp pre, Or.inl rfl⟩
    obtain ⟨i, b, lhs, guard, rhs⟩ := edge
    exact ⟨i, b, lhs, guard⟩
  closure := by
    intro a i b w v pre lhs guard rhs
    have edge : RawStep owner.system model w v := ⟨i, b, lhs, guard, rhs⟩
    rw [same_rules] at edge
    exact (good_post a v).mpr ((branch_raw_step_iff w v).mp edge).2

def good_derivation := good.step model good_obligations

theorem good_sound :
    ∀ a w, (good.meaning model).pre a w →
      Silmaril.Logic.Reachability.AllPartial (RawStep owner.system model)
        ((good.meaning model).post a) w := by
  apply good.step_sound model good_obligations
  change RawWellDefined owner.system model
  simpa only [same_rules] using branch_well_defined

/-- The positive source claim is not initially satisfied, and the actual
system has a finite complete path. Soundness is not vacuous in this model. -/
theorem positive_initial : (good.meaning model).pre noCaptures .start ∧
    ¬ (good.meaning model).post noCaptures .start := by
  refine ⟨(good_pre noCaptures .start).mpr rfl, ?_⟩
  intro h
  rcases (good_post noCaptures .start).mp h with impossible | impossible <;> cases impossible

def parsedComplete : Reachability.Derivation.CompletePath (RawStep owner.system model) := by
  simpa only [same_rules] using rightComplete

/-- Actual accepted left-only parsed claim fails the bridge's closure premise.
The right competitor is installed at the same source state. -/
theorem bad_no_obligations : ¬ bad.StepObligations model := by
  intro h
  have edge : RawStep owner.system model .start .right := by
    rw [same_rules]
    exact two_distinct_successors.2.1
  obtain ⟨i, b, lhs, guard, rhs⟩ := edge
  have post := h.closure noCaptures i b .start .right
    ((bad_pre noCaptures .start).mpr rfl) lhs guard rhs
  have impossible : State.right = State.left := (bad_post noCaptures .right).mp post
  cases impossible

/-- The actual complete right-branch path avoids the left-only parsed target
at its initial vertex and every later vertex. This is separate from the Step
closure counterexample above. -/
theorem bad_complete_avoids (i : Nat) :
    ¬ (bad.meaning model).post noCaptures (parsedComplete.point i) := by
  intro post
  have impossible := (bad_post noCaptures (parsedComplete.point i)).mp post
  cases i with
  | zero =>
    change State.start = State.left at impossible
    cases impossible
  | succ i =>
    change State.right = State.left at impossible
    cases impossible

/-- Semantic failure of all-partial reachability, witnessed by an actual finite
complete source path, rather than merely inability to use one proof rule. -/
theorem bad_not_all_partial :
    ¬ Reachability.AllPartial (RawStep owner.system model)
      ((bad.meaning model).post noCaptures) State.start := by
  intro valid
  obtain ⟨i, bounded, post⟩ := valid parsedComplete.length parsedComplete.point
    (by rfl) parsedComplete.edge parsedComplete.terminal
  exact bad_complete_avoids i post

/-- No closed derivation in any of the existing eight semantic rules can prove
this actual parsed claim in the populated model. Soundness supplies the
contradiction using the independently proved totality of installed axioms. -/
theorem bad_no_closed_derivation :
    ¬ Nonempty (Reachability.Derivation.Derives
      (lowerSchemes owner.system model) ∅ ∅ (bad.meaning model)) := by
  rintro ⟨d⟩
  have total : RawWellDefined owner.system model := by
    simpa only [same_rules] using branch_well_defined
  have valid := derivation_sound owner.system model d total noCaptures State.start
    ((bad_pre noCaptures State.start).mpr rfl)
  exact bad_not_all_partial valid

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.ParsedExamples
