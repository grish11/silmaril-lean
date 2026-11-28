module

import Silmaril.SSA.PEG.Thms
import Silmaril.SSA.PEG.Figure19.Structured.Thms
import Silmaril.SSA.PEG.Semantics.Reindex.Thms
import Mathlib.Logic.Equiv.Basic
meta import Silmaril.SSA.PEG.Figure19.Structured.Defs

namespace Silmaril.SSA.PEG.Tests

open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | one : Op [] .count
  | add : Op [.count, .count] .count
  | alternateAdd : Op [.count, .count] .count
  | succ : Op [.count] .count
  | atLeastTwo : Op [.count] .bool
  | partialCount : Op [.count] .count
  | partialFlag : Op [.count] .bool

private def mergeAdd : InstructionMap Op Op
  | _, _, .alternateAdd => .add
  | _, _, instr => instr

/-- Vertex 0 is the result of a conditional. The add uses the same
producer twice, and the roots repeat one output. -/
private def diamond : RawGraph Op [.bool] [.count, .count, .bool] 5 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 1 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .phi, [1, 3, 4]⟩
    | 1 => ⟨_, .param .head, []⟩
    | 2 => ⟨_, .op .one, []⟩
    | 3 => ⟨_, .op .alternateAdd, [2, 2]⟩
    | 4 => ⟨_, .op .zero, []⟩
  roots := [0, 0, 1]

example : diamond.check.isSome = true := by decide
example : ({ diamond with roots := [0, 0, 5] } : RawGraph Op [.bool] [.count, .count, .bool] 5 0).check.isNone = true :=
  by decide
example : ({ diamond with roots := [0, 0, 2] } : RawGraph Op [.bool] [.count, .count, .bool] 5 0).check.isNone = true :=
  by decide
example : ({ diamond with roots := [0, 0] } : RawGraph Op [.bool] [.count, .count, .bool] 5 0).check.isNone = true :=
  by decide

private def typedDiamond : Graph Op [.bool] [.count, .count, .bool] 5 0 :=
  diamond.check.get (by decide)

example : refNumbers (typedDiamond.node 3).args = [2, 2] := by decide
example : refNumbers typedDiamond.roots = [0, 0, 1] := by decide

example : (checkRefs diamond.sort [.bool, .count, .count] [1, 3]).isNone = true := by decide
example : (checkRefs diamond.sort [.bool, .count, .count] [2, 3, 4]).isNone = true := by decide

example : ∃ op, ((typedDiamond.mapOps mergeAdd).node 3).label = .op op ∧
    refNumbers ((typedDiamond.mapOps mergeAdd).node 3).args = [2, 2] :=
  ⟨.add, rfl, rfl⟩

private def loops : LoopForest 2 :=
  ⟨fun i => if i = 1 then some 0 else none⟩

private def countRef (i : Fin 5) : Ref (fun _ : Fin 5 => (Ty.count : Ty Unit)) .count := ⟨i, rfl⟩

private def pair (a b : Fin 5) : Tuple (Ref (fun _ : Fin 5 => (Ty.count : Ty Unit))) [.count, .count] :=
  .cons (countRef a) (.cons (countRef b) .nil)

/-- A (0), E (1), B (2), zero (3), one (4). Put E in A's feedback or initial slot. -/
private def nested (outerFeedback : Bool) : Graph Op [] [.count] 5 2 where
  forest := loops
  sort _ := .count
  node i := match i with
    | 0 => .ofLabel (.theta 0) (if outerFeedback then pair 3 1 else pair 1 3)
    | 1 => .ofLabel (.eval 1) (pair 2 4)
    | 2 => .ofLabel (.theta 1) (pair 3 0)
    | 3 => .ofLabel (.op .zero) .nil
    | 4 => .ofLabel (.op .one) .nil
  roots := .cons (countRef 0) .nil

private theorem validForest : loops.WellFormed := by
  intro i
  rintro ⟨ks, path, pos⟩
  have step : ∀ (a b : Fin 2), loops.Up a () b → b.val < a.val := by
    unfold LoopForest.Up
    decide
  exact (Nat.lt_irrefl i.val) (path.strictRank pos Fin.val (fun e _ => step _ _ e))

private theorem outerAncestor : loops.StrictlyEncloses 0 1 :=
  ⟨[()], .cons (by rfl) (.nil 0), by decide⟩

/-- Check a local edge property by enumerating the operand slots of the five vertices. -/
private theorem forEdges {feedback : Bool} {p : Fin 5 → EdgeKind (Fin 2) → Fin 5 → Prop}
    (check : ∀ a i, p a (((nested feedback).node a).label.kind i)
        (((nested feedback).node a).arg i).id) :
    ∀ {a b k}, (nested feedback).Edge a k b → p a k b := by
  rintro a b k ⟨i, rfl, rfl⟩
  exact check a i

private def feedbackRank (i : Fin 5) : Nat :=
  match i with
  | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0

private theorem feedbackCycles (back : Bool) : (nested back).FeedbackCycles := by
  have step : ∀ {a b k}, (nested back).Edge a k b →
      ¬k.IsFeedback → feedbackRank b < feedbackRank a := by
    cases back
    all_goals
      apply forEdges
      decide
  intro a ks path pos
  by_cases h : ∃ k ∈ ks, k.IsFeedback
  · exact h
  · exact (Nat.lt_irrefl _ (path.strictRank pos feedbackRank
      (fun e hk => step e (fun hb => h ⟨_, hk, hb⟩)))).elim

private theorem loopScope (back : Bool) : (nested back).Scoped := by
  have startAt : ∀ a, ((nested back).node a).label.loop = some 0 → a ≠ 2 := by
    cases back <;> decide
  have endsAt : ∀ b, ((nested back).node b).label.thetaLoop = some 1 → b = 2 := by
    cases back <;> decide
  have step : ∀ {a b k}, (nested back).Edge a k b → b = 2 → k = .sample 1 := by
    cases back
    all_goals
      apply forEdges
      decide
  intro a b ks start target path ha hb
  by_cases eq : target = start
  · subst target
    exact .inl ⟨[], .nil _⟩
  by_cases st : start = 1
  · have tg : target = 0 := by
      apply Fin.ext
      have := target.isLt
      omega
    subst start
    subst target
    obtain ⟨es, ancestry, _⟩ := outerAncestor
    exact .inl ⟨es, ancestry⟩
  · have st0 : start = 0 := Fin.ext (by omega)
    have tg1 : target = 1 := Fin.ext (by omega)
    subst start
    subst target
    right
    by_cases sampled : EdgeKind.sample (1 : Fin 2) ∈ ks
    · exact sampled
    · have avoid := path.preserves (p := fun a => a ≠ 2)
        (fun e hk _ eq => sampled (step e eq ▸ hk)) (startAt a ha)
      exact (avoid (endsAt b hb)).elim

private def outerRole (back : Bool) : EdgeKind (Fin 2) :=
  if back then .feedback 0 else .initial 0

private def outerRank (i : Fin 5) : Nat :=
  match i with
  | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0

private theorem everyCycleVisitsOuter (back : Bool) {a : Fin 5} {ks : List (EdgeKind (Fin 2))}
    (path : Walk (nested back).Edge a ks a) (pos : ks ≠ []) : outerRole back ∈ ks := by
  have step : ∀ {a b k}, (nested back).Edge a k b →
      k ≠ outerRole back → outerRank b < outerRank a := by
    cases back
    all_goals
      apply forEdges
      decide
  by_cases h : outerRole back ∈ ks
  · exact h
  · exact (Nat.lt_irrefl _ (path.strictRank pos outerRank
      (fun e hk => step e (fun eq => h (eq ▸ hk))))).elim

private theorem observerIsInner {back : Bool} {a b : Fin 5} {ks : List (EdgeKind (Fin 2))}
    (path : Walk (nested back).Edge a ks b) :
    ∀ k ∈ ks, ∀ l, k.IsObserverAt l → l = 1 := by
  have step : ∀ {a b k}, (nested back).Edge a k b →
      ∀ l, k.IsObserverAt l → l = 1 := by
    cases back
    all_goals
      apply forEdges
      unfold EdgeKind.IsObserverAt
      decide
  induction path with
  | nil => simp
  | cons edge _ ih =>
    intro k hk l hl
    rcases List.mem_cons.mp hk with rfl | tail
    · exact step edge l hl
    · exact ih k tail l hl

private theorem strong : (nested true).WellFormed where
  forest := validForest
  feedback := feedbackCycles true
  loopScope := loopScope true
  outerFeedback := by
    intro a ks path k hk inner obs
    have hi := observerIsInner path k hk inner obs
    subst inner
    exact ⟨0, outerAncestor, everyCycleVisitsOuter true path (by intro eq; simp [eq] at hk)⟩

private theorem weak : (nested false).PaperWellFormed where
  forest := validForest
  feedback := feedbackCycles false
  loopScope := loopScope false
  outerTheta := by
    intro a ks path k hk inner obs
    have hi := observerIsInner path k hk inner obs
    subst inner
    exact ⟨0, outerAncestor, .initial 0,
      everyCycleVisitsOuter false path (by intro eq; simp [eq] at hk), .inl rfl⟩

private theorem weakCycle : Walk (nested false).Edge 0 [.initial 0, .sample 1, .feedback 1] 0 :=
  .cons (show (nested false).Edge 0 (.initial 0) 1 from ⟨⟨0, by decide⟩, rfl, rfl⟩)
    (.cons (show (nested false).Edge 1 (.sample 1) 2 from ⟨⟨0, by decide⟩, rfl, rfl⟩)
      (.cons (show (nested false).Edge 2 (.feedback 1) 0 from ⟨⟨1, by decide⟩, rfl, rfl⟩) (.nil 0)))

example : (nested false).PaperWellFormed ∧ ¬(nested false).WellFormed := by
  refine ⟨weak, fun h => ?_⟩
  obtain ⟨outer, above, onCycle⟩ := h.outerFeedback 0 _ weakCycle _ (by decide) 1 (.inl rfl)
  have houter : outer = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at onCycle
    obtain h | h | h := onCycle
    · cases h
    · cases h
    · cases h
      rfl
  exact validForest 1 (houter ▸ above)

/-- Two top-level loops. A direct reference into the sibling's θ is out of scope. -/
private def siblings : Graph Op [] [.count] 5 2 where
  forest := ⟨fun _ => none⟩
  sort _ := .count
  node i := if i = 0 then .ofLabel (.theta 0) (pair 3 2) else (nested true).node i
  roots := .cons (countRef 0) .nil

example : ¬siblings.Scoped := by
  intro scopedGraph
  have edge : siblings.Edge 0 (.feedback 0) 2 := ⟨⟨1, by decide⟩, rfl, rfl⟩
  rcases scopedGraph 0 2 [.feedback 0] 0 1 (.cons edge (.nil 2)) rfl rfl with above | sampled
  · obtain ⟨ks, ancestry⟩ := above
    cases ancestry with
    | cons up _ => contradiction
  · exact (by decide : EdgeKind.sample (1 : Fin 2) ∉ [EdgeKind.feedback 0]) sampled

private def swapTwo : Fin 2 ≃ Fin 2 where
  toFun i := if i = 0 then 1 else 0
  invFun i := if i = 0 then 1 else 0
  left_inv := by unfold Function.LeftInverse; decide
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide

private def reverseFive : Fin 5 ≃ Fin 5 where
  toFun i := ⟨4 - i.val, by omega⟩
  invFun i := ⟨4 - i.val, by omega⟩
  left_inv := by unfold Function.LeftInverse; decide
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide

example : ((nested true).reindex reverseFive swapTwo).WellFormed :=
  ((nested true).wellFormed_reindex reverseFive swapTwo).mpr strong

example : ((nested true).reindex reverseFive swapTwo).Edge 4 (.feedback 1) 3 :=
  ((nested true).edge_relabel (fun op => op) reverseFive swapTwo 4 3 (.feedback 1)).mpr
    ⟨⟨1, by decide⟩, rfl, rfl⟩

/-- Specialized Fig. 11 equations for the weak graph, in outer/inner index
order. E samples at index 1, so monotonize checks exactly the prefix at 0. -/
private def SolvesWeak (a e b : Nat → Nat → Option Nat) : Prop :=
  (∀ o i, a o i = if o = 0 then e o i else some 0) ∧
  (∀ o i, e o i = if b o 0 = none then none else b o 1) ∧
  (∀ o i, b o i = if i = 0 then some 0 else a o (i - 1))

private def valueA (k o _i : Nat) : Option Nat :=
  if o = 0 then some k else some 0

private def valueB (k o i : Nat) : Option Nat :=
  if i = 0 then some 0 else valueA k o (i - 1)

private theorem solves (k : Nat) : SolvesWeak (valueA k) (valueA k) (valueB k) := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · intro o i
    by_cases h : o = 0 <;> simp [valueA, h]
  · intro o i
    simp [valueA, valueB]

example : ∃ a e b a' e' b', SolvesWeak a e b ∧ SolvesWeak a' e' b' ∧ a 0 0 ≠ a' 0 0 :=
  ⟨valueA 0, valueA 0, valueB 0, valueA 1, valueA 1, valueB 1,
    solves 0, solves 1, by decide⟩

section Denotation

set_option backward.isDefEq.respectTransparency false

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .zero, _ => some ⟨0⟩
    | .one, _ => some ⟨1⟩
    | .add, .cons x (.cons y .nil) => some ⟨x.down + y.down⟩
    | .alternateAdd, _ => none
    | .succ, .cons x .nil => some ⟨x.down + 1⟩
    | .atLeastTwo, .cons x .nil => some ⟨decide (2 ≤ x.down)⟩
    | .partialCount, .cons x .nil => if x.down = 0 then none else some x
    | .partialFlag, .cons x .nil => if x.down = 0 then none else some ⟨true⟩

private def diamondRank : DemandRank 5 0 :=
  [.phase fun i => match i with | 0 => 2 | 3 => 1 | _ => 0]

private theorem diamondWF : WellFounded typedDiamond.Demand :=
  typedDiamond.demandWellFounded_of_check diamondRank (by decide)

private def boolInput (b : Bool) : Tuple model.Value [.bool] := .cons ⟨b⟩ .nil

private def clock {l : Nat} (n : Nat) : Index l := fun _ => n

private theorem diamondBranch (b : Bool) :
    typedDiamond.denote model (boolInput b) diamondWF (0, clock 0) =
      if b then none else some ⟨0⟩ := by
  let v := typedDiamond.denote model (boolInput b) diamondWF
  have eq := typedDiamond.denote_solves model (boolInput b) diamondWF
  have condition : v (1, clock 0) = some ⟨b⟩ := eq (1, clock 0)
  have bottom : v (3, clock 0) = none := by
    have e := eq (3, clock 0)
    change v (3, clock 0) = (collect (F := model.Value) [.count, .count] _).elim none
      (fun _ => none) at e
    exact e.trans (by cases collect _ _ <;> rfl)
  have other : v (4, clock 0) = some ⟨0⟩ := eq (4, clock 0)
  have phi := eq (0, clock 0)
  change v (0, clock 0) =
    (v (1, clock 0)).elim none (fun flag => if flag.down then v (3, clock 0) else v (4, clock 0)) at phi
  rwa [condition, bottom, other] at phi

example : typedDiamond.denote model (boolInput false) diamondWF (0, clock 0) = some ⟨0⟩ :=
  diamondBranch false

example : typedDiamond.denote model (boolInput true) diamondWF (0, clock 0) = none :=
  diamondBranch true

example :
    (Label.phi (P := Op) (params := []) (out := .count)).interpret model .nil
      (clock 0 : Index 0) (fun slot _ _ => match slot with
        | 0 => none
        | 1 | 2 => some ⟨7⟩) = none :=
  rfl

example (wf' : WellFounded (typedDiamond.mapOps mergeAdd).Demand) :
    (typedDiamond.mapOps mergeAdd).observe model
        ((typedDiamond.mapOps mergeAdd).denote model (boolInput true) wf') (clock 0) =
      typedDiamond.observe (model.reduct mergeAdd)
        (typedDiamond.denote (model.reduct mergeAdd) (boolInput true) diamondWF) (clock 0) :=
  typedDiamond.observe_denote_mapOps mergeAdd (boolInput true) diamondWF wf' (clock 0)

private def nestedRank : DemandRank 5 2 :=
  [.counter 0, .phase outerRank, .counter 1]

example : nestedRank.check (nested true) = true := by decide
example : nestedRank.check (nested false) = false := by decide

example : (nestedRank.reindex reverseFive swapTwo).check
    ((nested true).reindex reverseFive swapTwo) = true := by
  rw [Graph.rank_check_reindex]
  decide

example : ∃! values, (nested true).Solves model .nil values :=
  (nested true).existsUnique_solves_of_check model .nil nestedRank (by decide)

example : ∃! values, (nested true).Solves model .nil values :=
  (nested true).existsUnique_solves_of_wellFormed model .nil strong

-- The sampling edge is legal at every requested count, independently of the current vector.
example (i : Index 2) (j : Nat) :
    (nested true).Demand (2, i.set 1 j) (1, i) :=
  Graph.sampleDemand (g := nested true) (a := 1) (b := 2)
    (⟨⟨0, by decide⟩, rfl, rfl⟩) i j

-- The printed-guard example contains a cycle of actual demands.
example : ¬WellFounded (nested false).Demand := by
  intro wf
  let start := (clock 0 : Index 2)
  let sample := start.set 1 1
  have initEdge : (nested false).Demand (1, start) (0, start) :=
    ⟨.initial 0, ⟨⟨0, by decide⟩, rfl, rfl⟩, rfl, rfl⟩
  have sampleEdge : (nested false).Demand (2, sample) (1, start) :=
    Graph.sampleDemand (g := nested false) (a := 1) (b := 2)
      ⟨⟨0, by decide⟩, rfl, rfl⟩ start 1
  have reset : sample.set 1 0 = start := by
    funext j
    by_cases hj : j = 1
    · simp [sample, Index.set, hj, start, clock]
    · simp [sample, Index.set, hj]
  have feedbackEdge : (nested false).Demand (0, start) (2, sample) :=
    ⟨.feedback 1, ⟨⟨1, by decide⟩, rfl, rfl⟩, 0, rfl, reset.symm⟩
  have noCycle (x : Request 5 2) : ¬∃ y z, (nested false).Demand y x ∧
      (nested false).Demand z y ∧ (nested false).Demand x z := by
    induction x using wf.induction with
    | h x ih =>
      rintro ⟨y, z, hy, hz, hx⟩
      exact ih y hy ⟨z, x, hz, hx, hy⟩
  exact noCycle (0, start) ⟨(1, start), (2, sample), initEdge, sampleEdge, feedbackEdge⟩

/-- θ counts, pass exits at two, and one stream has an undefined first sample
even though its value at the exit is defined. -/
private def running : RawGraph Op [] [.count, .count, .count] 11 1 where
  forest := ⟨fun _ => none⟩
  sort i := if i = 3 ∨ i = 8 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .theta 0, [1, 2]⟩
    | 1 => ⟨_, .op .zero, []⟩
    | 2 => ⟨_, .op .succ, [0]⟩
    | 3 => ⟨_, .op .atLeastTwo, [0]⟩
    | 4 => ⟨_, .pass 0, [3]⟩
    | 5 => ⟨_, .eval 0, [0, 4]⟩
    | 6 => ⟨_, .op .partialCount, [0]⟩
    | 7 => ⟨_, .eval 0, [6, 4]⟩
    | 8 => ⟨_, .op .partialFlag, [0]⟩
    | 9 => ⟨_, .pass 0, [8]⟩
    | 10 => ⟨_, .eval 0, [0, 9]⟩
  roots := [5, 7, 10]

private def runningGraph : Graph Op [] [.count, .count, .count] 11 1 :=
  running.check.get (by decide)

private def runningRank : DemandRank 11 1 :=
  [.phase fun i => match i with
    | 0 | 1 | 2 => 0
    | 3 | 6 | 8 => 1
    | 4 | 9 => 2
    | _ => 3,
   .counter 0,
   .phase fun i => match i with | 0 => 1 | 2 => 2 | _ => 0]

private noncomputable def runningValue : runningGraph.Valuation model :=
  runningGraph.denote model .nil (runningGraph.demandWellFounded_of_check runningRank (by decide))

private theorem runningEq (q : Request 11 1) :
    runningValue q = runningGraph.equation model .nil runningValue q :=
  runningGraph.denote_solves model .nil _ q

private theorem setClock (n k : Nat) : (clock n : Index 1).set 0 k = clock k := by
  funext j
  have eq : j = 0 := Fin.ext (by have := j.isLt; omega)
  subst j
  rfl

private theorem collectSingle
    (read : (slot : Fin [Ty.count].length) → Option (model.Value [Ty.count][slot])) :
    collect [Ty.count] read = (read 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases read 0 <;> rfl

private theorem iteration (k : Nat) : runningValue (0, clock k) = some ⟨k⟩ := by
  induction k with
  | zero =>
    exact (runningEq (0, clock 0)).trans (runningEq (1, clock 0))
  | succ k ih =>
    have theta := runningEq (0, clock (k + 1))
    change runningValue (0, clock (k + 1)) = runningValue (2, (clock (k + 1)).set 0 k) at theta
    have next := runningEq (2, clock k)
    change runningValue (2, clock k) =
      (collect (F := model.Value) [.count] _).elim none
        (model.run Op.succ) at next
    rw [collectSingle] at next
    change runningValue (2, clock k) =
      ((runningValue (0, clock k)).map (fun x => Tuple.cons x .nil)).elim none
        (model.run Op.succ) at next
    rw [setClock, next, ih] at theta
    exact theta

private theorem testAt (k : Nat) :
    runningValue (3, clock k) = some ⟨decide (2 ≤ k)⟩ := by
  have e := runningEq (3, clock k)
  change runningValue (3, clock k) =
    (collect (F := model.Value) [.count] _).elim none
      (model.run Op.atLeastTwo) at e
  rw [collectSingle] at e
  change runningValue (3, clock k) =
    ((runningValue (0, clock k)).map (fun x => Tuple.cons x .nil)).elim none
      (model.run Op.atLeastTwo) at e
  rw [iteration] at e
  exact e

private theorem passAt (k : Nat) : runningValue (4, clock k) = some ⟨2⟩ := by
  have e := runningEq (4, clock k)
  change runningValue (4, clock k) =
    (firstTrue (fun j => (runningValue (3, (clock k).set 0 j)).map ULift.down)).map ULift.up at e
  have least : firstTrue (fun j => some (decide (2 ≤ j))) = some 2 := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨by decide, fun j hj => ?_⟩
    have indices : j = 0 ∨ j = 1 := by omega
    rcases indices with rfl | rfl <;> decide
  have streamEq : (fun j => (runningValue (3, (clock k).set 0 j)).map ULift.down) =
      fun j => some (decide (2 ≤ j)) := by
    funext j
    rw [setClock, testAt]
    rfl
  rw [streamEq, least] at e
  exact e

-- A selected index greater than the current iteration still returns the exact sample.
private theorem selectedEval : runningValue (5, clock 0) = some ⟨2⟩ := by
  have e := runningEq (5, clock 0)
  change runningValue (5, clock 0) =
    (runningValue (4, clock 0)).elim none
      (fun k => monotonize (fun j => runningValue (0, (clock 0).set 0 j)) k.down) at e
  rw [passAt] at e
  change runningValue (5, clock 0) =
    monotonize (fun j => runningValue (0, (clock 0).set 0 j)) 2 at e
  exact e.trans (by
    apply (monotonize_eq_some_iff _ _ _).mpr
    constructor
    · rw [setClock, iteration]
    · intro j _
      rw [setClock, iteration]
      rfl)

private theorem partialAt (k : Nat) :
    runningValue (6, clock k) = if k = 0 then none else some ⟨k⟩ := by
  have e := runningEq (6, clock k)
  change runningValue (6, clock k) =
    (collect (F := model.Value) [.count] _).elim none
      (model.run Op.partialCount) at e
  rw [collectSingle] at e
  change runningValue (6, clock k) =
    ((runningValue (0, clock k)).map (fun x => Tuple.cons x .nil)).elim none
      (model.run Op.partialCount) at e
  rw [iteration] at e
  exact e

example : runningValue (6, clock 2) = some ⟨2⟩ := partialAt 2

-- The sample at two is defined, but eval is bottom because index zero is bottom.
private theorem blockedEval : runningValue (7, clock 0) = none := by
  have e := runningEq (7, clock 0)
  change runningValue (7, clock 0) =
    (runningValue (4, clock 0)).elim none
      (fun k => monotonize (fun j => runningValue (6, (clock 0).set 0 j)) k.down) at e
  rw [passAt] at e
  change runningValue (7, clock 0) =
    monotonize (fun j => runningValue (6, (clock 0).set 0 j)) 2 at e
  refine e.trans (Option.eq_none_iff_forall_ne_some.mpr fun v hv => ?_)
  have earlier := ((monotonize_eq_some_iff _ 2 v).mp hv).2 0 (by decide)
  change (runningValue (6, (clock 0).set 0 0)).isSome = true at earlier
  rw [setClock, partialAt] at earlier
  contradiction

private theorem flagAt (k : Nat) :
    runningValue (8, clock k) = if k = 0 then none else some ⟨true⟩ := by
  have e := runningEq (8, clock k)
  change runningValue (8, clock k) =
    (collect (F := model.Value) [.count] _).elim none
      (model.run Op.partialFlag) at e
  rw [collectSingle] at e
  change runningValue (8, clock k) =
    ((runningValue (0, clock k)).map (fun x => Tuple.cons x .nil)).elim none
      (model.run Op.partialFlag) at e
  rw [iteration] at e
  exact e

-- A later true cannot make pass recover from bottom in its predicate's prefix.
private theorem blockedPass : runningValue (9, clock 0) = none := by
  have e := runningEq (9, clock 0)
  change runningValue (9, clock 0) =
    (firstTrue (fun j => (runningValue (8, (clock 0).set 0 j)).map ULift.down)).map ULift.up at e
  have streamEq : (fun j => (runningValue (8, (clock 0).set 0 j)).map ULift.down) =
      fun j => if j = 0 then none else some true := by
    funext j
    rw [setClock, flagAt]
    by_cases zero : j = 0 <;> simp [zero]
  rw [streamEq] at e
  have blocked : firstTrue (fun j => if j = 0 then none else some true) = none := by
    apply (firstTrue_eq_none_iff _).mpr
    intro k hit
    obtain ⟨atK, earlier⟩ := (monotonize_eq_some_iff _ _ _).mp hit
    cases k with
    | zero => contradiction
    | succ k => have impossible := earlier 0 (Nat.zero_lt_succ k); contradiction
  rw [blocked] at e
  exact e

-- Eval with an undefined count has no defined observation.
private theorem undefinedEval : runningValue (10, clock 0) = none := by
  have e := runningEq (10, clock 0)
  change runningValue (10, clock 0) =
    (runningValue (9, clock 0)).elim none
      (fun k => monotonize (fun j => runningValue (0, (clock 0).set 0 j)) k.down) at e
  rw [blockedPass] at e
  exact e

-- Renumbering a typed table preserves the order of all three outputs
-- and retains both forms of bottom.
private def runningRows : Fin 11 ≃ Fin 11 := Equiv.swap 0 5
private def movedRunning := runningGraph.reindex runningRows (Equiv.refl (Fin 1))

example (wf : WellFounded movedRunning.Demand) :
    movedRunning.observe model (movedRunning.denote model .nil wf) (clock 0) =
      .cons (some ⟨2⟩) (.cons none (.cons none .nil)) := by
  have moved := runningGraph.observe_denote_reindex runningRows (Equiv.refl (Fin 1))
    model .nil (runningGraph.demandWellFounded_of_check runningRank (by decide)) wf (clock 0)
  change ((runningGraph.reindex runningRows (Equiv.refl (Fin 1))).observe model
    ((runningGraph.reindex runningRows (Equiv.refl (Fin 1))).denote model .nil wf) (clock 0)) = _
  rw [moved]
  change Tuple.cons (F := fun t => Option (model.Value t)) (runningValue (5, clock 0))
    (.cons (runningValue (7, clock 0)) (.cons (runningValue (10, clock 0)) .nil)) = _
  rw [selectedEval, blockedEval, undefinedEval]

example : firstTrue (fun _ => some false) = none := by
  apply (firstTrue_eq_none_iff _).mpr
  intro k hit
  cases ((monotonize_eq_some_iff _ _ _).mp hit).1

end Denotation

end Silmaril.SSA.PEG.Tests

namespace Silmaril.SSA.PEG.Figure19.Tests

open PEG PEG.Simple
open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | positive : Op [.count] .bool
  | odd : Op [.count] .bool
  | pred : Op [.count] .count
  | predTwo : Op [.count] .count
  | yes : Op [] .bool
  | not : Op [.bool] .bool

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .positive, .cons n .nil => some ⟨n.down != 0⟩
    | .odd, .cons n .nil => some ⟨n.down % 2 == 1⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .predTwo, .cons n .nil => some ⟨n.down - 2⟩
    | .yes, .nil => some ⟨true⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private abbrev store : List (Ty Unit) := [.count]

private def input (n : Nat) : Tuple model.Value store := .cons ⟨n⟩ .nil

private def step (op : Op [.count] .count) : Stmt Op true store store :=
  .seq (.assign (.op op (.cons (.var .head) .nil))) (.project (.cons .head .nil))

private def guard : Expr Op store .bool := .op .positive (.cons (.var .head) .nil)

private def inner : Stmt Op true store store :=
  .while rfl guard
    (.branch (.op .odd (.cons (.var .head) .nil)) (step .pred) (step .predTwo))

private def source : Program Op true store .count := ⟨store, .while rfl guard inner, .head⟩

private def compiled := PEG.Simple.Structured.translate source Op.not

-- The outer feedback executes a child while. The child's feedback
-- contains a φ whose two arms use different primitive instructions.
#guard (Structured.check source .not 32).isSome
#guard (Figure19.check compiled .printed 32).isNone

example : CFGContext compiled (inferDepth compiled.forest
    (PEG.Simple.Structured.program source Op.not).nodes.length) .inward :=
  (PEG.Simple.Structured.translate_figure19 source .not).2

private abbrev pairStore : List (Ty Unit) := [.count, .count]

private def exchange (op : Op [.count] .count) : Stmt Op true pairStore pairStore :=
  .seq (.assign (.op op (.cons (.var (.tail .head)) .nil)))
    (.project (.cons .head (.cons (.tail .head) .nil)))

-- Both values are captured by the child. Each child's next value
-- depends on the other old value, with the first update selected by φ.
private def nestedExchange : Program Op true pairStore .count :=
  let test : Expr Op pairStore .bool := .op .positive (.cons (.var .head) .nil)
  ⟨pairStore, .while rfl test (.while rfl test
    (.branch (.op .odd (.cons (.var .head) .nil)) (exchange .pred) (exchange .predTwo))), .head⟩

#guard (Structured.check nestedExchange .not 64).isSome

example :
    let g := PEG.Simple.Structured.translate nestedExchange Op.not
    let depth := inferDepth g.forest (PEG.Simple.Structured.program nestedExchange Op.not).nodes.length
    FitsForest g.forest depth ∧ CFGContext g depth .inward :=
  PEG.Simple.Structured.translate_figure19 nestedExchange .not

private theorem sourceReturns : source.Returns model (input 3) ⟨0⟩ := by
  have first : Exec model (step .pred) (input 3) (some (input 2)) :=
    .seq (.assign rfl) .project
  have second : Exec model (step .predTwo) (input 2) (some (input 0)) :=
    .seq (.assign rfl) .project
  have child : Exec model inner (input 3) (some (input 0)) :=
    .whileStep rfl (.branchTrue rfl first)
      (.whileStep rfl (.branchFalse rfl second) (.whileStop rfl))
  exact ⟨input 0, .whileStep rfl child (.whileStop rfl), rfl⟩

example (ok : (Structured.check source .not 32).isSome)
    (i : Index (PEG.Simple.Structured.program source Op.not).nodes.length) :
    let admitted := (Structured.check source .not 32).get ok
    compiled.observe model (compiled.denote model (input 3) admitted.demandWellFounded) i =
      .cons (some ⟨0⟩) .nil :=
  Structured.observe_of_returns ((Structured.check source .not 32).get ok)
    model (input 3) (fun _ => rfl) sourceReturns i

private def pairedSort (i : Fin 4) : Ty Unit := if i = 3 then .bool else .count

private def paired (passKey : Fin 2) : Graph Op store [.count] 4 2 where
  forest := ⟨fun _ => none⟩
  sort := pairedSort
  node i := match i with
  | 0 => .ofLabel (.eval 0) (.cons ⟨2, rfl⟩ (.cons ⟨1, rfl⟩ .nil))
  | 1 => .ofLabel (.pass passKey) (.cons ⟨3, rfl⟩ .nil)
  | 2 => .ofLabel (.param .head) .nil
  | 3 => .ofLabel (.op .yes) .nil
  roots := .cons ⟨0, rfl⟩ .nil

private def pairedRank : DemandRank 4 2 := [.phase fun i => 4 - i.val]

-- Both keys have depth one. Changing only the pass key preserves the
-- checked demand rank but violates the eval/pass pairing clause.
#guard (checkGuarded (paired 0) .inward 8 pairedRank).isSome
#guard (checkGuarded (paired 1) .inward 8 pairedRank).isNone

example (depth : Fin 2 → Nat) : ¬ CFGContext (paired 0) depth .printed :=
  fun typed => typed.printed_no_root_eval 0 rfl

example : WellFounded (paired 1).Demand :=
  (paired 1).demandWellFounded_of_check pairedRank (by decide)

example (depth : Fin 2 → Nat) : ¬ CFGContext (paired 1) depth .inward := by
  intro typed
  have boundary := (typed 0).evalBoundary
  change ∃ host, host ≤ 0 ∧ EvalDirection.inward.Allows host (depth 0) ∧
    ∃ test, Node.ofLabel (.pass (1 : Fin 2)) (.cons ⟨3, rfl⟩ .nil :
      Tuple (Ref pairedSort) [.bool]) = .ofLabel (.pass 0) test at boundary
  obtain ⟨host, _, _, test, different⟩ := boundary
  cases different

end Silmaril.SSA.PEG.Figure19.Tests
