module

import Silmaril.SSA.PEG.Builder
import Silmaril.SSA.Peggy.Optimizer.Cyclic.Thms
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.SSA.Peggy.Bridge.Figure11.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Thms
import Silmaril.SSA.Peggy.EPEG.Selection.Thms
import Silmaril.SSA.Peggy.Optimizer.Thms
import Silmaril.SSA.Peggy.Optimizer.Contextual.Thms
import Silmaril.SSA.Peggy.Worked.EvalScale.Thms
import Silmaril.SSA.Peggy.Worked.StrengthReduction.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Thms
import Silmaril.SSA.PEG.Simple.Thms
import Silmaril.SSA.PEG.Projection.Defs
meta import Silmaril.SSA.Peggy.Optimizer.Cyclic.Defs
meta import Silmaril.SSA.Peggy.EPEG.Selection.Legality.Defs
meta import Silmaril.SSA.Peggy.Bridge.Egg.Defs
meta import Silmaril.SSA.Peggy.Bridge.Figure11.Defs
meta import Silmaril.SSA.Peggy.Acyclic.Defs
meta import Silmaril.SSA.Peggy.EPEG.Defs
meta import Silmaril.SSA.Peggy.EPEG.Saturation.Defs
meta import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.ZeroSample
meta import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Defs
meta import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs
meta import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
meta import Silmaril.Logic.Egg.Core.Replay.Defs
meta import Silmaril.SSA.PEG.Builder
meta import Silmaril.SSA.Peggy.Optimizer.Defs
meta import Silmaril.SSA.Peggy.Optimizer.Contextual.Defs
meta import Silmaril.SSA.Peggy.Optimizer.Extension.Defs
meta import Silmaril.SSA.Peggy.Worked.EvalScale.Defs
meta import Silmaril.SSA.Peggy.Worked.StrengthReduction.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Defs
meta import Silmaril.SSA.PEG.Projection.Defs
meta import Mathlib.Tactic.FinCases

namespace Silmaril.SSA.Peggy.Tests

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Core.Replay (Receipt)
open PEG (Ty RawGraph Graph)
open Acyclic (Interpretation Ranked)
open Bridge.Egg

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | yes : Op [] .bool
  | no : Op [] .bool
  | bottom : Op [] .bool
  | fail : Op [] .count
  | add : Op [.count, .count] .count
  deriving DecidableEq

private abbrev params : List (Ty Unit) := [.bool, .count, .count]
private abbrev results : List (Ty Unit) := [.count, .count, .count, .bool]

/-- The add uses the selected value twice. The first and third outputs share
the add, and the two count parameters occupy distinct input slots. -/
private def sourceWith (control : Op [] .bool) : RawGraph Op params results 7 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 2 ∨ i = 6 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .op .add, [1, 1]⟩
    | 1 => ⟨_, .phi, [2, 3, 4]⟩
    | 2 => ⟨_, .op control, []⟩
    | 3 => ⟨_, .param (.tail .head), []⟩
    | 4 => ⟨_, .op .fail, []⟩
    | 5 => ⟨_, .param (.tail (.tail .head)), []⟩
    | 6 => ⟨_, .param .head, []⟩
  roots := [0, 5, 0, 6]

private abbrev source := sourceWith .yes

private def target : RawGraph Op params results 4 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 3 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .param (.tail .head), []⟩
    | 1 => ⟨_, .op .add, [0, 0]⟩
    | 2 => ⟨_, .param (.tail (.tail .head)), []⟩
    | 3 => ⟨_, .param .head, []⟩
  roots := [1, 2, 1, 3]

private def sourceRank (i : Fin 7) : Nat := match i with
  | 0 => 2 | 1 => 1 | _ => 0

private def targetRank (i : Fin 4) : Nat := if i = 1 then 1 else 0

private def src : Graph Op params results 7 0 := source.check.get (by decide)
private def dst : Graph Op params results 4 0 := target.check.get (by decide)
private def srcRanked : Ranked src := (Ranked.check src sourceRank).get (by decide)
private def dstRanked : Ranked dst := (Ranked.check dst targetRank).get (by decide)

-- A well-typed self-edge still fails fragment admission.
private def cyclic : Graph Op params results 7 0 :=
  ({ source with node := fun i => if i = 0 then { source.node i with args := [0, 1] }
    else source.node i }).check.get (by decide)

example : (Ranked.check cyclic sourceRank).isNone = true := by decide

private abbrev T := Term Op params

private def yes : T .bool := .app (.prim Op.yes) (fun j => j.elim0)
private def no : T .bool := .app (.prim Op.no) (fun j => j.elim0)
private def failed : T .count := .app (.prim Op.fail) (fun j => j.elim0)
private def condition : T .bool := .var 0
private def x : T .count := .var 1
private def y : T .count := .var 2

private def phi (c : T .bool) (a b : T .count) : T .count :=
  .app (.phi .count) (fun i => match i with | 0 => c | 1 => a | 2 => b)

private abbrev selectTrue : Core.Rule (signature Op) where
  scope := params.length
  context := context params
  guards := [⟨.bool, condition, yes⟩]
  conclusion := ⟨.count, phi condition x y, x⟩

private abbrev rules := [selectTrue]
private abbrev Rec := Receipt rules (context params)

private def substitute (i : Fin params.length) : T params[i] :=
  match i with | 0 => yes | 1 => x | 2 => failed

private def select (guardReceipt : Rec .bool) : Rec .count :=
  Receipt.rewrite (rs := rules) 0 substitute (fun j : Fin 1 => match j with | 0 => guardReceipt)

private def receipts (guardReceipt : Rec .bool) (i : Fin results.length) : Rec results[i] :=
  let rewrite := select guardReceipt
  let underAdd : Rec .count :=
    .congr (Symbol.prim Op.add) (fun i => match i with | 0 => rewrite | 1 => rewrite)
  match i with
  | 0 => underAdd
  | 1 => .refl y
  | 2 => .trans underAdd (.refl (.app (.prim Op.add) (fun j => match j with | 0 => x | 1 => x)))
  | 3 => .refl condition

private abbrev opEq : PrimitiveEq Op := fun _ _ => inferInstance

#guard (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome
#guard (checkOutputs opEq dstRanked srcRanked (fun i => .symm (receipts (.refl yes) i))).isSome
#guard (checkOutputs opEq srcRanked dstRanked (receipts (.refl no))).isNone
#guard ((Receipt.trans (.refl x) (.refl y) : Rec .count).replay (matchSymbol opEq)).isNone

private def swapped : Graph Op params results 4 0 :=
  ({ target with roots := [2, 1, 1, 3] }).check.get (by decide)

private def swappedRanked : Ranked swapped := (Ranked.check swapped targetRank).get (by decide)

#guard (checkOutputs opEq srcRanked swappedRanked (receipts (.refl yes))).isNone

private def nativeInterp : PEG.Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .yes, .nil => some ⟨true⟩
    | .no, .nil => some ⟨false⟩
    | .bottom, .nil | .fail, .nil => none
    | .add, .cons a (.cons b .nil) => some ⟨Nat.add a.down b.down⟩

private def interp : Interpretation Op := Bridge.Figure11.toAcyclic nativeInterp

private def input (i : Fin params.length) : interp.Partial params[i] :=
  match i with | 0 => none | 1 => some (7 : Nat) | 2 => some (3 : Nat)

#guard (show Option Nat from srcRanked.evalOutputs interp input 0) == some 14
#guard (show Option Nat from srcRanked.evalOutputs interp input 1) == some 3
#guard (show Option Nat from srcRanked.evalOutputs interp input 2) == some 14
#guard (srcRanked.evalOutputs interp input 3).isNone
#guard (srcRanked.evalOutputs interp (fun _ => none) 0).isNone

private theorem selectTrue_holds : selectTrue.Holds (model interp) := by
  intro ρ guards
  have hc := guards ⟨.bool, condition, yes⟩ (List.mem_singleton_self _)
  change ρ 0 = some true at hc
  change (ρ 0).bind (fun b : Bool => if b then ρ 1 else ρ 2) = ρ 1
  rw [hc]
  rfl

example (accepted : (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome) :
    srcRanked.evalOutputs interp input = dstRanked.evalOutputs interp input := by
  apply checkOutputs_sound opEq accepted interp _ input
  intro r hr
  have : r = selectTrue := List.mem_singleton.mp hr
  exact this ▸ selectTrue_holds

private def nativeInputs : RVSDG.Tuple nativeInterp.Value params :=
  .cons ⟨false⟩ (.cons ⟨7⟩ (.cons ⟨3⟩ .nil))

example (accepted : (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome) :
    src.observe nativeInterp (src.denote nativeInterp nativeInputs
      (Bridge.Figure11.demandWellFounded srcRanked)) Fin.elim0 =
    dst.observe nativeInterp (dst.denote nativeInterp nativeInputs
      (Bridge.Figure11.demandWellFounded dstRanked)) Fin.elim0 := by
  apply Bridge.Figure11.checkOutputs_figure11_sound opEq accepted nativeInterp
  intro r hr
  have : r = selectTrue := List.mem_singleton.mp hr
  exact this ▸ selectTrue_holds

private def variant (control : Op [] .bool) : Graph Op params results 7 0 :=
  (sourceWith control).check.get (by rfl)

private def variantRanked (control : Op [] .bool) : Ranked (variant control) :=
  (Ranked.check (variant control) sourceRank).get (by rfl)

private noncomputable def variantValues (control : Op [] .bool) :
    (variant control).Valuation nativeInterp :=
  (variant control).denote nativeInterp nativeInputs
    (Bridge.Figure11.demandWellFounded (variantRanked control))

private theorem variantPhi (control : Op [] .bool) :
    variantValues control (1, Fin.elim0) = (nativeInterp.run control .nil).elim none
      (fun flag => if flag.down then some ⟨7⟩ else none) := by
  have step := (variant control).denote_solves nativeInterp nativeInputs
    (Bridge.Figure11.demandWellFounded (variantRanked control))
  have guard : variantValues control (2, Fin.elim0) = nativeInterp.run control .nil :=
    step (2, Fin.elim0)
  have yesArm : variantValues control (3, Fin.elim0) = some ⟨7⟩ := step (3, Fin.elim0)
  have noArm : variantValues control (4, Fin.elim0) = none := step (4, Fin.elim0)
  have eq := step (1, Fin.elim0)
  change variantValues control (1, Fin.elim0) =
    (variantValues control (2, Fin.elim0)).elim none (fun flag => if flag.down
      then variantValues control (3, Fin.elim0) else variantValues control (4, Fin.elim0)) at eq
  rw [guard, yesArm, noArm] at eq
  exact eq

-- The undefined arm is ignored exactly when it is unselected.
example : variantValues .yes (1, Fin.elim0) = some ⟨7⟩ := variantPhi .yes
example : variantValues .no (1, Fin.elim0) = none := variantPhi .no
example : variantValues .bottom (1, Fin.elim0) = none := variantPhi .bottom

-- Equal branch values do not justify dropping an undefined control operand.
private def unsafePhi : Core.Rule (signature Op) :=
  { selectTrue with guards := [], conclusion := ⟨.count, phi condition x x, x⟩ }

example : ¬unsafePhi.Holds (model interp) := by
  intro holds
  have eq := holds input (by intro e he; cases he)
  change (none : Option Nat) = some 7 at eq
  cases eq

end Silmaril.SSA.Peggy.Tests

namespace Silmaril.SSA.Peggy.EPEG.Tests

open PEG Saturation
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | one : Op [] .count
  | succ : Op [.count] .count
  | atLeastTwo : Op [.count] .bool

private abbrev Result : List (Ty Unit) := [.count, .count]

/-- Vertices 0 and 1 form a feedback cycle. Vertices 3 and 9 duplicate θ
and pass respectively, and 7 and 8 eval at the two passes. -/
private def table : RawGraph Op [] Result 10 1 where
  forest := ⟨fun _ => none⟩
  sort i := if i = 5 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .theta 0, [2, 1]⟩
    | 1 => ⟨_, .op .succ, [0]⟩
    | 2 => ⟨_, .op .zero, []⟩
    | 3 => ⟨_, .theta 0, [4, 1]⟩
    | 4 => ⟨_, .op .zero, []⟩
    | 5 => ⟨_, .op .atLeastTwo, [0]⟩
    | 6 => ⟨_, .pass 0, [5]⟩
    | 7 => ⟨_, .eval 0, [0, 6]⟩
    | 8 => ⟨_, .eval 0, [3, 9]⟩
    | 9 => ⟨_, .pass 0, [5]⟩
  roots := [0, 7]

private def cyclicSource : Graph Op [] Result 10 1 := table.check.get (by decide)

private def countRef (i : Fin 10) (h : cyclicSource.sort i = .count) :
    Ref cyclicSource.sort .count := ⟨i, h⟩

private def boolRef (i : Fin 10) (h : cyclicSource.sort i = .bool) :
    Ref cyclicSource.sort .bool := ⟨i, h⟩

private def counts (a b : Ref cyclicSource.sort .count) :
    Tuple (Ref cyclicSource.sort) [.count, .count] := .cons a (.cons b .nil)

private def rank : DemandRank 10 1 :=
  [.phase fun i => match i with
      | 0 | 1 | 2 | 3 | 4 => 0
      | 5 => 1
      | 6 | 9 => 2
      | _ => 3,
   .counter 0,
   .phase fun i => match i with | 0 | 3 => 1 | 1 => 2 | _ => 0]

private theorem sourceWF : WellFounded cyclicSource.Demand :=
  cyclicSource.demandWellFounded_of_check rank (by decide)

example : cyclicSource.Edge 0 (.feedback 0) 1 ∧ cyclicSource.Edge 1 .ordinary 0 :=
  ⟨⟨⟨1, by decide⟩, rfl, rfl⟩, ⟨⟨0, by decide⟩, rfl, rfl⟩⟩

private def arithmetic : PEG.Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .one, .nil => some ⟨1⟩
    | .succ, .cons k .nil => some ⟨k.down + 1⟩
    | .atLeastTwo, .cons k .nil => some ⟨decide (2 ≤ k.down)⟩

private noncomputable def streams := cyclicSource.denote arithmetic .nil sourceWF

private theorem sourceSolves : cyclicSource.Solves arithmetic .nil streams :=
  cyclicSource.denote_solves arithmetic .nil sourceWF

private def zeros : MatchingNodes cyclicSource 2 4 :=
  ⟨[], .count, .op .zero, .nil, .nil, rfl, rfl, HEq.rfl, HEq.rfl⟩

private abbrev thetas : MatchingNodes cyclicSource 0 3 :=
  ⟨[.count, .count], .count, .theta 0,
    counts (countRef 2 rfl) (countRef 1 rfl), counts (countRef 4 rfl) (countRef 1 rfl),
    rfl, rfl, HEq.rfl, HEq.rfl⟩

private def passes : MatchingNodes cyclicSource 6 9 :=
  ⟨[.bool], .count, .pass 0,
    .cons (boolRef 5 rfl) .nil, .cons (boolRef 5 rfl) .nil, rfl, rfl, HEq.rfl, HEq.rfl⟩

private def evals : MatchingNodes cyclicSource 7 8 :=
  ⟨[.count, .count], .count, .eval 0,
    counts (countRef 0 rfl) (countRef 6 rfl), counts (countRef 3 rfl) (countRef 9 rfl),
    rfl, rfl, HEq.rfl, HEq.rfl⟩

private def seed : Equation cyclicSource := ⟨2, 4, rfl⟩

private def thetaRule : GuardedEquation cyclicSource := ⟨[seed], ⟨0, 3, rfl⟩⟩

private theorem thetaLaw : thetaRule.Holds streams := by
  intro guards
  apply thetas.streamEq sourceSolves
  intro k
  match k with
  | 0 => exact guards seed (List.mem_singleton_self _)
  | 1 => exact ⟨rfl, fun _ => HEq.rfl⟩

private def discrete : Classes 10 := Classes.discrete

-- Eval and θ are initially blocked. Passing over them must keep them eligible.
private def obligations : List (Obligation cyclicSource) :=
  [.congruent evals, .guarded thetaRule, .congruent passes, .congruent zeros]

private theorem contracts : ∀ o ∈ obligations, o.Holds streams := by
  intro o mem
  simp only [obligations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with eq | eq | eq | eq
  · subst o; trivial
  · subst o; exact thetaLaw
  · subst o; trivial
  · subst o; trivial

private def classes := saturate obligations discrete
private def limited := run 2 obligations discrete
private def reversed := saturate obligations.reverse discrete

example : thetaRule.check discrete = false := by decide
example : evals.checkOperands (discrete.merge 2 4) = false := by decide
example : limited 6 = limited 9 ∧ limited 7 ≠ limited 8 := by decide
example : isClosed obligations limited = false := by decide
example : isClosed obligations classes = true ∧ classes 7 = classes 8 := by decide

#guard (List.finRange 10).all (fun a => (List.finRange 10).all fun b =>
  (classes a == classes b) == (reversed a == reversed b))

example (a b : Fin 10) : classes a = classes b ↔ reversed a = reversed b :=
  saturate_perm (List.reverse_perm obligations).symm discrete a b

example : limited.Valid streams :=
  run_sound 2 obligations sourceSolves Classes.discrete_valid contracts

private theorem classesValid : classes.Valid streams :=
  run_sound obligations.length obligations (c := discrete) sourceSolves Classes.discrete_valid contracts

private def cyclicTarget : Graph Op [] Result 10 1 :=
  cyclicSource.withRoots (counts (countRef 3 rfl) (countRef 8 rfl))

private def selection : Selection cyclicSource cyclicTarget :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

example (idx : Index 1) :
    cyclicSource.observe arithmetic streams idx =
      cyclicTarget.observe arithmetic
        (cyclicTarget.denote arithmetic .nil
          (selection.demandWellFounded (classes := classes) (by decide))) idx :=
  run_selection_sound obligations.length obligations (c := discrete) (m := arithmetic) (env := .nil)
    selection sourceWF Classes.discrete_valid contracts (by decide) sourceSolves idx

/-- Now the increment reads vertex 3 instead of vertex 0. Together with
vertex 3's θ feedback, this gives the candidate a different cycle. -/
private def redirectedNode (v : Fin 10) :
    Node Op [] (Fin 1) cyclicSource.sort (cyclicSource.sort v) :=
  if h : v = 1 then
    h.symm ▸ Node.ofLabel (.op Op.succ) (.cons (countRef 3 rfl) .nil)
  else cyclicSource.node v

private def redirectedTarget : Graph Op [] Result 10 1 :=
  { cyclicTarget with node := redirectedNode }

private def redirectedSelection : Selection cyclicSource redirectedTarget :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

private def redirectedRows (v : Fin 10) : Selection.Row redirectedSelection v := by
  by_cases h : v = 1
  · subst v
    exact ⟨[.count], .op Op.succ, .cons (countRef 0 rfl) .nil, .cons (countRef 3 rfl) .nil,
      HEq.rfl, rfl⟩
  · let row := cyclicSource.node v
    exact ⟨row.inputs, row.label, row.args, row.args, HEq.rfl,
      by
        change redirectedNode v = Node.ofLabel row.label row.args
        rw [redirectedNode, dite_eq_right h]
        rfl⟩

example : redirectedTarget.Edge 3 (.feedback 0) 1 ∧ redirectedTarget.Edge 1 .ordinary 3 :=
  ⟨⟨⟨1, by decide⟩, rfl, rfl⟩, ⟨⟨0, by decide⟩, rfl, rfl⟩⟩

example : Selection.checkRows redirectedRows limited = false := by decide

example (idx : Index 1) :
    cyclicSource.observe arithmetic streams idx =
      redirectedTarget.observe arithmetic
        (redirectedTarget.denote arithmetic .nil
          (redirectedSelection.demandWellFounded (classes := classes) (by decide))) idx :=
  Selection.observe_sound_of_rows (m := arithmetic) (env := .nil) sourceWF classesValid
    (by decide) redirectedRows (by decide) idx

/-- Putting θ in its own initial slot preserves wiring types but violates
demand admission at index zero. -/
private def cyclicInitializer : Graph Op [] Result 10 1 :=
  ({ table with
    node := fun i => if i = 3 then { table.node i with args := [3, 1] } else table.node i
    roots := [3, 8] }).check.get (by decide)

private def badRank : Selection cyclicSource cyclicInitializer :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

example : badRank.check classes = false := by decide

/-- This candidate passes the rank and class-of-root checks, but the
representatives would assign zero to a vertex that now denotes one. -/
private def changedInitializer : Graph Op [] Result 10 1 :=
  ({ table with
    node := fun i => match i with
      | 2 => ⟨[], .op Op.one, []⟩
      | i => table.node i
    roots := [3, 8] }).check.get (by decide)

private def wrong : Selection cyclicSource changedInitializer :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

example : wrong.check classes = true := by decide

example : ¬changedInitializer.Solves arithmetic .nil (wrong.inherit streams) := by
  intro solves
  let idx : Index 1 := fun _ => 0
  have eq := solves (2, idx)
  change streams (2, idx) = some ⟨1⟩ at eq
  have zero : streams (2, idx) = some ⟨0⟩ := sourceSolves (2, idx)
  rw [zero] at eq
  cases eq

end Silmaril.SSA.Peggy.EPEG.Tests

namespace Silmaril.SSA.Peggy.Optimizer.Tests

open Silmaril.Logic.Institution.Examples
open PEG (Ty RawGraph Graph)
open Bridge.Egg Bridge.Figure11
open Silmaril.Logic.Egg
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | yes : Op [] .bool
  | no : Op [] .bool
  | bottom : Op [] .bool
  | bad : Op [] .count
  | add : Op [.count, .count] .count
  | triple : Op [.count] .count
  deriving DecidableEq

private abbrev params : List (Ty Unit) := [.count]
private abbrev output : List (Ty Unit) := [.count]
private abbrev branchSorts : List (Ty Unit) := [.bool, .count, .count, .count]

/-- The old root is φ(flag, (x+x)+x, bottom). A failed repeat check
changes only the last x in the add. -/
private def raw (flag : Op [] .bool) (repeated : Bool) : RawGraph Op params output 6 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 3 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .param .head, []⟩
    | 1 => ⟨_, .op .add, [0, 0]⟩
    | 2 => ⟨_, .op .add, [1, if repeated then 0 else 4]⟩
    | 3 => ⟨_, .op flag, []⟩
    | 4 => ⟨_, .op .bad, []⟩
    | 5 => ⟨_, .phi, [3, 2, 4]⟩
  roots := [5]

private def admitted (flag : Op [] .bool) (repeated : Bool) : Graph Op params output 6 0 :=
  (raw flag repeated).check.get (by cases repeated <;> rfl)

private def rank (i : Fin 6) : Nat := match i with
  | 1 => 1 | 2 => 2 | 5 => 3 | _ => 0

private def program (flag : Op [] .bool) (repeated : Bool) : Program Op params .count :=
  ⟨6, admitted flag repeated,
    (Acyclic.Ranked.check (admitted flag repeated) rank).get (by cases repeated <;> rfl)⟩

private def add {ts : List (Ty Unit)} (a b : Term Op ts .count) : Term Op ts .count :=
  .app (.prim Op.add) (fun i => match i with | 0 => a | 1 => b)

private abbrev BranchTerm := Term Op branchSorts
private def c : BranchTerm .bool := .var 0
private def prior : BranchTerm .count := .var 1
private def last : BranchTerm .count := .var 2
private def fallback : BranchTerm .count := .var 3
private def yes : BranchTerm .bool := .app (.prim Op.yes) (fun i => i.elim0)

private def phi (guard : BranchTerm .bool) (a b : BranchTerm .count) : BranchTerm .count :=
  .app (.phi .count) (fun i => match i with | 0 => guard | 1 => a | 2 => b)

private abbrev selectTrue : Rule Op .count where
  scope := branchSorts.length
  context := context branchSorts
  guards := [⟨.bool, c, yes⟩]
  lhs := phi c (add prior last) fallback
  rhs := .app (.prim Op.add) (fun i => match i with | 0 => ⟨1, rfl⟩ | 1 => ⟨2, rfl⟩)

private def x : Term Op params .count := .var 0

private abbrev compress : Rule Op .count where
  scope := params.length
  context := context params
  guards := []
  lhs := add (add x x) x
  rhs := .app (.prim Op.triple) (fun i => match i with | 0 => ⟨0, rfl⟩)

private def rules := [selectTrue, compress]
private abbrev opEq : PrimitiveEq Op := fun _ _ => inferInstance
private def start := program .yes true
private def chosen := optimize opEq rules 2 start

#guard (matchRoot opEq start selectTrue).length == 1
#guard (matchRoot opEq start compress).isEmpty
#guard (matchRoot opEq (program .bottom true) selectTrue).length == 1
#guard (discover opEq rules (program .bottom true)).isEmpty
#guard (discover opEq rules (program .no true)).isEmpty
#guard (optimize opEq rules 0 start).program.cost == 5
#guard (optimize opEq rules 1 start).program.cost == 2
#guard start.cost == 5 && chosen.program.cost == 1
#guard chosen.program.size == start.size + 2
#guard (optimize opEq rules 2 (program .yes false)).program.cost == 3

private def arithmetic : PEG.Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .yes, .nil => some ⟨true⟩
    | .no, .nil => some ⟨false⟩
    | .bottom, .nil | .bad, .nil => none
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .triple, .cons a .nil => some ⟨(a.down + a.down) + a.down⟩

private def exampleInput : (toAcyclic arithmetic).Inputs params :=
  fun i => match i with | 0 => some (14 : Nat)

#guard (show Option Nat from start.ranked.evalOutputs (toAcyclic arithmetic) exampleInput 0) == some 42
#guard (show Option Nat from chosen.program.ranked.evalOutputs
  (toAcyclic arithmetic) exampleInput 0) == some 42

private theorem selectLaw : selectTrue.core.Holds (model (toAcyclic arithmetic)) := by
  intro ρ guards
  let control : Fin branchSorts.length := 0
  let other : Fin branchSorts.length := 3
  let flag : Option Bool := ρ control
  have guard := guards ⟨.bool, c, yes⟩ (List.mem_singleton_self _)
  change flag = some true at guard
  change (flag.bind (fun b => if b then
    (add prior last).eval (model (toAcyclic arithmetic)) ρ else ρ other)) =
    (add prior last).eval (model (toAcyclic arithmetic)) ρ
  rw [guard]
  rfl

private def addValues (a b : Option Nat) : Option Nat :=
  (toAcyclic arithmetic).applyPrim Op.add (fun i => match i with | 0 => a | 1 => b)

private def tripleValue (value : Option Nat) : Option Nat :=
  (toAcyclic arithmetic).applyPrim Op.triple (fun i => match i with | 0 => value)

private theorem compressLaw : compress.core.Holds (model (toAcyclic arithmetic)) := by
  intro ρ _
  let v : Option Nat := ρ (show Fin params.length from 0)
  change addValues (addValues v v) v = tripleValue v
  cases v <;> rfl

example (env : Tuple arithmetic.Value params) :
    start.graph.observe arithmetic (start.graph.denote arithmetic env
      (demandWellFounded start.ranked)) Fin.elim0 =
    chosen.program.graph.observe arithmetic (chosen.program.graph.denote arithmetic env
      (demandWellFounded chosen.program.ranked)) Fin.elim0 := by
  apply chosen.sound
  intro rule h
  simp only [coreRules, rules, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with eq | eq
  · exact eq ▸ selectLaw
  · exact eq ▸ compressLaw

private abbrev orderedResults : List (Ty Unit) := [.count, .count, .count, .bool]

/-- The first root uses vertex 2 twice. The second includes a partial sum
in the unselected φ arm, and the third has an undefined guard. The last
row duplicates vertex 2 when the graph is built without sharing. -/
private def contextualTable (shared swapped : Bool) :
    RawGraph Op params orderedResults 12 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 7 ∨ i = 9 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .param .head, []⟩
    | 1 => ⟨_, .op .add, [0, 0]⟩
    | 2 => ⟨_, .op .add, [1, 0]⟩
    | 3 => ⟨_, .op .add, [2, if shared then 2 else 11]⟩
    | 4 => ⟨_, .op .bad, []⟩
    | 5 => ⟨_, .op .add, [4, 4]⟩
    | 6 => ⟨_, .op .add, [5, 4]⟩
    | 7 => ⟨_, .op .no, []⟩
    | 8 => ⟨_, .phi, [7, 6, 3]⟩
    | 9 => ⟨_, .op .bottom, []⟩
    | 10 => ⟨_, .phi, [9, 2, 0]⟩
    | 11 => ⟨_, .op .add, [1, 0]⟩
  roots := if swapped then [10, 8, 3, 9] else [3, 8, 10, 9]

private def contextGraph (shared swapped : Bool) : Graph Op params orderedResults 12 0 :=
  (contextualTable shared swapped).check.get (by cases shared <;> cases swapped <;> rfl)

private def contextRank (i : Fin 12) : Nat := match i with
  | 1 | 5 => 1
  | 2 | 6 | 11 => 2
  | 3 | 10 => 3
  | 8 => 4
  | _ => 0

private def contextProgram (shared swapped : Bool) : RankedProgram Op params orderedResults :=
  ⟨12, contextGraph shared swapped,
    (Acyclic.Ranked.check (contextGraph shared swapped) contextRank).get
      (by cases shared <;> cases swapped <;> rfl)⟩

private def shared := contextProgram true false
private def repeated := contextProgram false false
private def swapped := contextProgram true true
private def contextRules : List (Contextual.Schema Op) := [⟨.count, compress⟩]
private def contextBest := Contextual.optimize opEq contextRules 2 shared

#guard (matchTarget opEq shared compress (encodeOutputs shared.ranked 0)).isEmpty
#guard (matchTarget opEq shared compress (encodeOutputs shared.ranked 1)).isEmpty
#guard (matchTarget opEq shared compress (encodeOutputs shared.ranked 2)).isEmpty
#guard (Contextual.discover opEq contextRules shared).length == 2
#guard Contextual.cost shared == 10
#guard Contextual.cost (Contextual.optimize opEq contextRules 1 shared).program == 9
#guard Contextual.cost contextBest.program == 8
#guard contextBest.program.size == shared.size
#guard PEG.refNumbers
  (contextBest.program.graph.node (contextBest.program.graph.roots.get .head).id).args == [2, 2]

private def self : PEG.Ref shared.graph.sort .count := ⟨(show Fin 12 from 2), rfl⟩
#guard (Contextual.replace shared self (PEG.Node.ofLabel (.op Op.triple) (.cons self .nil))).isNone

#guard Contextual.cost repeated == 11
#guard (Contextual.compareOutputs opEq shared repeated).isSome
#guard (Contextual.compareOutputs opEq shared swapped).isNone

#guard (shared.ranked.eval (toAcyclic arithmetic) exampleInput (show Fin 12 from 6)).isNone
#guard (show Option Nat from contextBest.program.ranked.evalOutputs
  (toAcyclic arithmetic) exampleInput 0) == some 84
#guard (show Option Nat from contextBest.program.ranked.evalOutputs
  (toAcyclic arithmetic) exampleInput 1) == some 84
#guard (contextBest.program.ranked.evalOutputs (toAcyclic arithmetic) exampleInput 2).isNone

example (env : Tuple arithmetic.Value params) :
    shared.graph.observe arithmetic (shared.graph.denote arithmetic env
      (demandWellFounded shared.ranked)) Fin.elim0 =
    contextBest.program.graph.observe arithmetic (contextBest.program.graph.denote arithmetic env
      (demandWellFounded contextBest.program.ranked)) Fin.elim0 := by
  apply CheckedProgram.sound contextBest
  intro rule h
  have eq : rule = compress.core := List.mem_singleton.mp h
  exact eq ▸ compressLaw

end Silmaril.SSA.Peggy.Optimizer.Tests

namespace Silmaril.SSA.Peggy.Optimizer.Cyclic.Tests

open PEG
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | bad : Op [] .count
  | succ : Op [.count] .count
  | add : Op [.count, .count] .count

private inductive Seed where
  | parameter
  | bottom
  | changing

private def Seed.address : Seed → Fin 7
  | .parameter => 3
  | .bottom => 6
  | .changing => 0

private abbrev params : List (Ty Unit) := [.count]
private abbrev results : List (Ty Unit) := [.count, .count, .count, .count]

/-- The live counter has θ/succ feedback. A second θ self-feeds its
initializer, is referenced by the add, and occurs twice at the boundary. -/
private abbrev countSort (_ : Fin 7) : Ty Unit := .count

private def countRef (i : Fin 7) : Ref countSort .count := ⟨i, rfl⟩

private def pair (a b : Fin 7) : Tuple (Ref countSort) [.count, .count] :=
  .cons (countRef a) (.cons (countRef b) .nil)

private def graph (seed : Seed) : Graph Op params results 7 1 where
  forest := ⟨fun _ => none⟩
  sort := countSort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (pair 2 1)
    | 1 => .ofLabel (.op .succ) (.cons (countRef 0) .nil)
    | 2 => .ofLabel (.op .zero) .nil
    | 3 => .ofLabel (.param .head) .nil
    | 4 => .ofLabel (.theta 0) (pair seed.address 4)
    | 5 => .ofLabel (.op .add) (pair 4 0)
    | 6 => .ofLabel (.op .bad) .nil
  roots := .cons (countRef 4) (.cons (countRef 5) (pair 0 4))

private def nodeCount {n : Nat} (_ : Graph Op params results n 1) : Nat := n

private def optimizedRoots (seed : Seed) : Option (Nat × Nat × List Nat) :=
  (optimize (graph seed)).map fun result =>
    (result.site.val, nodeCount result.matched.extract, refNumbers result.matched.extract.roots)

#guard (optimize (graph .parameter)).isSome
#guard optimizedRoots .parameter == some (4, 6, [3, 4, 0, 3])
#guard optimizedRoots .bottom == some (4, 6, [5, 4, 0, 5])
#guard (admit (graph .changing)).isSome
#guard (matchAt (graph .changing) (show Fin 7 from 4)).isNone
#guard (optimize (graph .changing)).isNone

private def compactedEdges : Bool :=
  match optimize (graph .parameter) with
  | none => false
  | some result =>
    let target := result.matched.extract
    (target.node 0).label.thetaLoop == some 0 &&
      refNumbers (target.node 0).args == [2, 1] && refNumbers (target.node 1).args == [0] &&
      refNumbers (target.node 4).args == [3, 0]

#guard compactedEdges

private def arithmetic : Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .bad, .nil => none
    | .succ, .cons a .nil => some ⟨a.down + 1⟩
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩

private def input : Tuple arithmetic.Value params := .cons ⟨7⟩ .nil
private def clock (k : Nat) : Index 1 := fun _ => k

private def admitted (seed : Seed) : Admission (graph seed) :=
  (admit (graph seed)).get (by cases seed <;> decide)

private noncomputable def streams (seed : Seed) : (graph seed).Valuation arithmetic :=
  (graph seed).denote arithmetic input (admitted seed).demandWellFounded

private theorem equations (seed : Seed) : (graph seed).Solves arithmetic input (streams seed) :=
  (graph seed).denote_solves arithmetic input (admitted seed).demandWellFounded

private theorem previous : (clock 1).set 0 0 = clock 0 := by
  funext loop
  have h : loop = 0 := Subsingleton.elim _ _
  subst loop
  rfl

private theorem counterZero (seed : Seed) : streams seed (0, clock 0) = some ⟨0⟩ := by
  have init : streams seed (2, clock 0) = some ⟨0⟩ := equations seed (2, clock 0)
  exact (equations seed (0, clock 0)).trans init

private def ref (seed : Seed) (i : Fin 7) : Ref (graph seed).sort .count := ⟨i, rfl⟩

private theorem counterOne (seed : Seed) : streams seed (0, clock 1) = some ⟨1⟩ := by
  have count := equations seed (0, clock 1)
  change streams seed (0, clock 1) = streams seed (1, (clock 1).set 0 0) at count
  have step := Rules.unary_at (equations seed) (r := ref seed 1) (arg := ref seed 0)
    (op := Op.succ) HEq.rfl (clock 0)
  change streams seed (1, clock 0) =
    (streams seed (0, clock 0)).bind (fun x => some ⟨x.down + 1⟩) at step
  rw [counterZero] at step
  exact count.trans (previous ▸ step)

private theorem selfStep (seed : Seed) :
    streams seed (4, clock 1) = streams seed (4, clock 0) := by
  have eq := equations seed (4, clock 1)
  change streams seed (4, clock 1) = streams seed (4, (clock 1).set 0 0) at eq
  rwa [previous] at eq

-- The near miss retains zero while its initializer has advanced to one.
example : streams .changing (4, clock 1) ≠ streams .changing (0, clock 1) := by
  have zero : streams .changing (4, clock 0) = streams .changing (0, clock 0) :=
    equations .changing (4, clock 0)
  rw [selfStep, zero, counterZero, counterOne]
  intro impossible
  exact Nat.noConfusion (congrArg ULift.down (Option.some.inj impossible))

example : streams .bottom (4, clock 1) = none := by
  have bad : streams .bottom (6, clock 0) = none := equations .bottom (6, clock 0)
  have init : streams .bottom (4, clock 0) = streams .bottom (6, clock 0) :=
    equations .bottom (4, clock 0)
  exact (selfStep .bottom).trans (init.trans bad)

-- θ(init, θ) equals its parameter initializer in the source. Choosing
-- the θ representative for that initializer slot creates an initial-edge
-- self-cycle, while the ordered class check still succeeds.
private def seedSource : Graph Op params [.count] 2 1 where
  forest := ⟨fun _ => none⟩
  sort := fun _ => .count
  node i := Fin.cases (.ofLabel (.theta 0)
      (.cons ⟨1, rfl⟩ (.cons ⟨0, rfl⟩ .nil)))
    (fun _ => .ofLabel (.param .head) .nil) i
  roots := .cons ⟨0, rfl⟩ .nil

private def selfInitializer : Graph Op params [.count] 1 1 where
  forest := ⟨fun _ => none⟩
  sort := fun _ => .count
  node _ := .ofLabel (.theta 0) (.cons ⟨0, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
  roots := .cons ⟨0, rfl⟩ .nil

private def seedMatch : Match seedSource 0 := (matchAt seedSource 0).get (by decide)

private def selected : EPEG.Selection seedSource selfInitializer :=
  ⟨fun _ => ⟨0, rfl⟩, demandRank (fun _ => 0)⟩

private def selectedRows (i : Fin 1) : EPEG.Selection.Row selected i :=
  ⟨[.count, .count], .theta 0,
    .cons ⟨1, rfl⟩ (.cons ⟨0, rfl⟩ .nil),
    .cons ⟨0, rfl⟩ (.cons ⟨0, rfl⟩ .nil), HEq.rfl, rfl⟩

example : EPEG.Selection.checkRows selectedRows seedMatch.classes = true := by decide

private def seedAdmission : Admission seedSource := (admit seedSource).get (by decide)

example : seedMatch.classes.Valid
    (seedSource.denote arithmetic input seedAdmission.demandWellFounded) :=
  seedMatch.classes_valid seedAdmission.demandWellFounded

-- Assign every selected row true and every reachability variable false.
-- The source of each edge is θ, so no immediate implication fires.
example : EPEG.Selection.PrintedCycles selfInitializer (fun _ => true) (fun _ _ => false) := by
  constructor
  · intro i j kind chosen nonTheta edge
    cases nonTheta
  · intro i j k kind reaches
    cases reaches
  · intro i nonTheta
    rfl

example : ¬ selfInitializer.FeedbackCycles := by
  intro feedback
  have initial : selfInitializer.Edge 0 (.initial 0) 0 := ⟨⟨0, by decide⟩, rfl, rfl⟩
  have cycle : Walk selfInitializer.Edge 0 [.initial 0] 0 := .cons initial (.nil 0)
  obtain ⟨kind, member, feedbackEdge⟩ := feedback 0 _ cycle (by simp)
  simp only [List.mem_singleton] at member
  subst kind
  exact feedbackEdge

#guard (EPEG.Selection.FeedbackRank.infer selfInitializer).isNone
#guard ((EPEG.Selection.FeedbackRank.infer (graph .parameter))).isSome

-- The bounded optimizer returns a certified selection with a live
-- θ→succ→θ recurrence, in addition to eliminating the matched row.
private def liveMatch : Match (graph .parameter) 4 :=
  (matchAt (graph .parameter) 4).get (by decide)

private def liveRank : DemandRank 6 1 :=
  demandRank fun i => if i = 0 then 1 else if i = 1 ∨ i = 4 then 2 else 0

#guard (liveMatch.replay liveRank).isSome

example (replay : liveMatch.Replay liveRank) : liveMatch.extract.FeedbackCycles :=
  replay.feedbackCycles

example : Walk liveMatch.extract.Edge 0 [.feedback 0, .ordinary] 0 := by
  have feedback : liveMatch.extract.Edge 0 (.feedback 0) 1 := ⟨⟨1, by decide⟩, rfl, rfl⟩
  have ordinary : liveMatch.extract.Edge 1 .ordinary 0 := ⟨⟨0, by decide⟩, rfl, rfl⟩
  exact .cons feedback (.cons ordinary (.nil 0))

end Silmaril.SSA.Peggy.Optimizer.Cyclic.Tests

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Tests

open PEG
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | one : Op [] .count
  | initial : Op [] .count
  | succ : Op [.count] .count
  deriving DecidableEq

private abbrev outputs : List (Ty Unit) := [.count, .count, .count]
private abbrev countSort (_ : Fin 5) : Ty Unit := .count
private def ref (i : Fin 5) : Ref countSort .count := ⟨i, rfl⟩
private def pair (a b : Fin 5) : Tuple (Ref countSort) [.count, .count] :=
  .cons (ref a) (.cons (ref b) .nil)

/-- A live θ/successor cycle. Its base sample is the only eval row. -/
private def graph (literal : Op [] .count) : Graph Op [] outputs 5 1 where
  forest := ⟨fun _ => none⟩
  sort := countSort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (pair 1 2)
    | 1 => .ofLabel (.op .initial) .nil
    | 2 => .ofLabel (.op .succ) (.cons (ref 0) .nil)
    | 3 => .ofLabel (.op literal) .nil
    | _ => .ofLabel (.eval 0) (pair 0 3)
  roots := .cons (ref 4) (pair 0 4)

private def source : State Op [] outputs 5 1 := ⟨graph .zero, Classes.discrete⟩
private def matched : ZeroSample source.graph 4 .zero :=
  (ZeroSample.matchAt (g := source.graph) 4 .zero).get (by decide)

private def useFresh : Step matched.step.apply :=
  ⟨⟨_, _, .op .succ, .cons matched.row.fresh .nil⟩, [], 0⟩

private def plan : Plan source := .next matched.step (.next useFresh .stop)

private def evalOperands {n : Nat} (g : Graph Op [] outputs n 1) : List (List Nat) :=
  (List.finRange n).filterMap fun i =>
    match g.node i with
    | ⟨_, .eval _, args⟩ => some (refNumbers args)
    | _ => none

#guard (ZeroSample.matchAt (g := graph .one) 4 .zero).isNone
#guard evalOperands source.graph == [[0, 3]]
#guard (plan.run 0).1 == 5
#guard (plan.run 1).1 == 6
#guard (plan.run 2).1 == 7
#guard (plan.run 8).1 == 7
#guard (plan.run 1).2.classes ⟨4, by decide⟩ == (plan.run 1).2.classes ⟨5, by decide⟩
#guard (plan.run 2).2.classes ⟨4, by decide⟩ == (plan.run 2).2.classes ⟨5, by decide⟩
#guard evalOperands (plan.run 1).2.graph == [[0, 3], [1, 3]]
#guard refNumbers ((plan.run 2).2.graph.node ⟨6, by decide⟩).args == [5]
#guard refNumbers (plan.run 2).2.graph.roots == [4, 0, 4]

-- A step can append the row with no merge budget as well.
private def appendOnly : Step source := { matched.step with fuel := 0 }

#guard appendOnly.apply.classes 4 != appendOnly.apply.classes 5

private theorem wf : WellFounded source.graph.Demand :=
  source.graph.demandWellFounded_of_check
    [.phase (fun i => if i = 4 then 1 else 0), .counter 0,
      .phase (fun i => if i = 2 then 2 else if i = 0 then 1 else 0)]
    (by decide)

private def arithmetic (initial : Option (ULift Nat)) : Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .one, .nil => some ⟨1⟩
    | .initial, .nil => initial
    | .succ, .cons k .nil => some ⟨k.down + 1⟩

private theorem traceSound (initial : Option (ULift Nat)) (fuel : Nat) :
    let target := (plan.run fuel).2
    let after := plan.demandWellFounded fuel wf
    target.classes.Valid (target.graph.denote (arithmetic initial) .nil after) ∧
    ∀ idx, target.graph.observe (arithmetic initial) (target.graph.denote (arithmetic initial) .nil after) idx =
      source.graph.observe (arithmetic initial) (source.graph.denote (arithmetic initial) .nil wf) idx := by
  apply Plan.sound fuel plan wf Classes.discrete_valid
  cases fuel with
  | zero => trivial
  | succ fuel =>
    refine ⟨matched.holds (m := arithmetic initial) rfl, ?_⟩
    cases fuel with
    | zero => trivial
    | succ fuel =>
      refine ⟨?_, ?_⟩
      · rintro _ _ _ member
        cases member
      · cases fuel <;> trivial

private def clockZero : Index 1 := fun _ => 0

private theorem initially (initial : Option (ULift Nat)) :
    source.graph.observe (arithmetic initial) (source.graph.denote (arithmetic initial) .nil wf) clockZero =
      .cons initial (.cons initial (.cons initial .nil)) := by
  let streams := source.graph.denote (arithmetic initial) .nil wf
  have solves := source.graph.denote_solves (arithmetic initial) .nil wf
  have base : streams (1, clockZero) = initial := solves (1, clockZero)
  have theta : streams (0, clockZero) = initial := (solves (0, clockZero)).trans base
  have literal : Rules.readRef streams (ref 3) clockZero = some ⟨0⟩ := solves (3, clockZero)
  have sample := Rules.eval_zero solves (r := ref 4) (source := ref 0) (count := ref 3)
    (loop := 0) HEq.rfl literal
  have reset : clockZero.set 0 0 = clockZero := by funext i; simp [Index.set, clockZero]
  change streams (4, clockZero) = streams (0, clockZero.set 0 0) at sample
  rw [reset, theta] at sample
  change (show Tuple (fun t => Option ((arithmetic initial).Value t)) outputs from
    .cons (streams (4, clockZero)) (.cons (streams (0, clockZero))
      (.cons (streams (4, clockZero)) .nil))) = _
  rw [sample, theta]

example (initial : Option (ULift Nat)) :
    let target := (plan.run 2).2.graph
    target.observe (arithmetic initial) (target.denote (arithmetic initial) .nil
      (plan.demandWellFounded 2 wf)) clockZero = .cons initial (.cons initial (.cons initial .nil)) :=
  ((traceSound initial 2).2 clockZero).trans (initially initial)

/-- A competing extension has already added the same RHS and a different
row, then renumbered the original eval out of its old address. -/
private abbrev biggerSort (_ : Fin 7) : Ty Unit := .count
private def biggerRef (i : Fin 7) : Ref biggerSort .count := ⟨i, rfl⟩
private def biggerPair (a b : Fin 7) : Tuple (Ref biggerSort) [.count, .count] :=
  .cons (biggerRef a) (.cons (biggerRef b) .nil)

private def biggerGraph : Graph Op [] outputs 7 1 where
  forest := ⟨fun _ => none⟩
  sort := biggerSort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (biggerPair 1 2)
    | 1 => .ofLabel (.op .initial) .nil
    | 2 => .ofLabel (.op .succ) (.cons (biggerRef 0) .nil)
    | 3 => .ofLabel (.op .zero) .nil
    | 4 => .ofLabel (.op .one) .nil
    | 5 => .ofLabel (.eval 0) (biggerPair 1 3)
    | _ => .ofLabel (.eval 0) (biggerPair 0 3)
  roots := .cons (biggerRef 6) (biggerPair 0 6)

private def permutation : Equiv.Perm (Fin 7) := Equiv.swap 4 6

private def bigger : State Op [] outputs 7 1 :=
  ⟨biggerGraph, Classes.discrete.merge 6 5⟩

private def nonPrefix : Embedding source bigger where
  vertices :=
    ⟨⟨fun i => permutation.symm i.castSucc.castSucc, fun _ _ h =>
      Fin.castSucc_inj.mp (Fin.castSucc_inj.mp (permutation.symm.injective h))⟩,
      fun _ => rfl⟩
  rows i := by fin_cases i <;> rfl
  roots := rfl
  forest := rfl
  classes a b h := congrArg bigger.classes
    (congrArg (fun i : Fin 5 => permutation.symm i.castSucc.castSucc) (show a = b from h))

private def delayedMatch := matched.transport nonPrefix
private def delayedResult := delayedMatch.step.apply

#guard (nonPrefix.vertices.address 4).val == 6
#guard (ZeroSample.matchAt (g := bigger.graph) 6 .zero).isSome
#guard (ZeroSample.matchAt (g := bigger.graph) 4 .zero).isNone
#guard refNumbers bigger.graph.roots == [6, 0, 6]
#guard evalOperands bigger.graph == [[1, 3], [0, 3]]
#guard evalOperands delayedResult.graph == [[1, 3], [0, 3], [1, 3]]
#guard bigger.classes 5 == bigger.classes 6
#guard delayedResult.classes 5 == delayedResult.classes 7
#guard ((nonPrefix.appendVertices matched.row).address 5).val == 7

example : ZeroSample.matchAt (g := bigger.graph) 6 .zero = some delayedMatch :=
  matched.matchAt_transport nonPrefix

example : ∃ mapped : Embedding matched.step.apply delayedResult,
    mapped.vertices.address 4 = 6 ∧ mapped.vertices.address 5 = 7 := by
  obtain ⟨mapped, addresses⟩ := matched.simulate nonPrefix
  exact ⟨mapped, addresses 4, addresses 5⟩

private theorem takeSample : ZeroSampleAnalysis Op.zero ⟨5, source⟩ ⟨6, matched.step.apply⟩ :=
  .inr ⟨4, matched, rfl⟩

example : ∃ next, ZeroSampleAnalysis Op.zero ⟨6, matched.step.apply⟩ next ∧
    Comparable ⟨6, matched.step.apply⟩ next :=
  delayed_step (ZeroSampleAnalysis.monotone _) (ZeroSampleAnalysis.inflationary _) takeSample takeSample

-- Even with both RHS copies already in the same class, the transported
-- match permits another fresh append and prevents stability.
example : ¬ NormalForms.Stable Comparable (ZeroSampleFamily Op.zero) ⟨8, delayedResult⟩ :=
  delayedMatch.no_stable (.single delayedMatch.progress.1)

private def secondRedex : Row source.graph :=
  ⟨_, _, .eval 0, pair 0 3⟩

private def twoSites : State Op [] outputs 6 1 := ⟨secondRedex.append, Classes.discrete⟩
private def scope : List Nat := [4, 5]
private def firstVisit := Dedup.visit Op.zero ⟨6, twoSites⟩ 4
private def closed := Dedup.close Op.zero ⟨6, twoSites⟩ scope

#guard evalOperands twoSites.graph == [[0, 3], [0, 3]]
#guard firstVisit.1 == 7
#guard evalOperands firstVisit.2.graph == [[0, 3], [0, 3], [1, 3]]
#guard Dedup.checkDone Op.zero firstVisit 4
#guard !(Dedup.checkDone Op.zero firstVisit 5)
#guard closed.1 == 7
#guard evalOperands closed.2.graph == [[0, 3], [0, 3], [1, 3]]
#guard closed.2.classes ⟨4, by decide⟩ == closed.2.classes ⟨6, by decide⟩
#guard closed.2.classes ⟨5, by decide⟩ == closed.2.classes ⟨6, by decide⟩
#guard Dedup.checkClosed Op.zero closed scope
#guard refNumbers closed.2.graph.roots == [4, 0, 4]

private theorem scopedEligible : ∀ address ∈ scope, Dedup.EligibleAt Op.zero ⟨6, twoSites⟩ address := by
  intro address member
  have sites : address = 4 ∨ address = 5 := by simpa [scope] using member
  rcases sites with rfl | rfl
  · exact ⟨4, rfl, ⟨(ZeroSample.matchAt (g := twoSites.graph) 4 .zero).get (by decide)⟩⟩
  · exact ⟨5, rfl, ⟨(ZeroSample.matchAt (g := twoSites.graph) 5 .zero).get (by decide)⟩⟩

example : Dedup.close Op.zero closed scope = closed :=
  Dedup.close_fixed closed scope (Dedup.close_checked ⟨6, twoSites⟩ scope scopedEligible)

example (initial : Option (ULift Nat)) :
    ∃ after : WellFounded closed.2.graph.Demand,
      closed.2.classes.Valid (closed.2.graph.denote (arithmetic initial) .nil after) ∧
      closed.2.graph.observe (arithmetic initial) (closed.2.graph.denote (arithmetic initial) .nil after)
        clockZero = .cons initial (.cons initial (.cons initial .nil)) := by
  have before := secondRedex.demandWellFounded wf
  obtain ⟨after, valid, observed⟩ := Dedup.close_sound (m := arithmetic initial) (env := .nil)
    ⟨6, twoSites⟩ scope (zero := Op.zero) rfl before Classes.discrete_valid
  exact ⟨after, valid, (observed clockZero).trans
    ((secondRedex.observe_eq wf before clockZero).trans (initially initial))⟩

private def twoSiteInput : Output Op [] outputs 1 := ⟨6, twoSites⟩
private def twoSiteRun := Dedup.Worklist.run Op.zero 2 twoSiteInput
private def oneVisit := Dedup.Worklist.run Op.zero 1 twoSiteInput

#guard twoSiteRun.report.sites == [4, 5]
#guard twoSiteRun.report.stop == .fixed
#guard twoSiteRun.state.1 == 7
#guard oneVisit.report.sites == [4]
#guard oneVisit.report.stop == .exhausted
#guard Dedup.Worklist.enabledAt Op.zero oneVisit.state 5
#guard (Dedup.Worklist.check Op.zero 1 twoSiteInput oneVisit.report).isSome
#guard (Dedup.Worklist.check Op.zero 2 twoSiteInput ⟨[4, 5], .exhausted⟩).isNone
#guard (Dedup.Worklist.check Op.zero 2 twoSiteInput ⟨[5, 4], .fixed⟩).isSome
#guard (Dedup.Worklist.check Op.zero 2 twoSiteInput ⟨[4], .fixed⟩).isNone
#guard (Dedup.Worklist.check Op.zero 2 twoSiteInput ⟨[6], .exhausted⟩).isNone
#guard (Dedup.Worklist.check Op.zero 2 twoSiteInput ⟨[4, 4], .exhausted⟩).isNone
#guard (Dedup.Worklist.check Op.zero 1 twoSiteInput twoSiteRun.report).isNone

private abbrev nestedSort (_ : Fin 4) : Ty Unit := .count
private def nestedRef (i : Fin 4) : Ref nestedSort .count := ⟨i, rfl⟩
private def nestedPair (a b : Fin 4) : Tuple (Ref nestedSort) [.count, .count] :=
  .cons (nestedRef a) (.cons (nestedRef b) .nil)

/-- Sampling the outer theta at zero generates a new sample of the inner
theta. Both thetas use live self-feedback on the same loop clock. -/
private def nested : Graph Op [] outputs 4 1 where
  forest := ⟨fun _ => none⟩
  sort := nestedSort
  node i := match i with
    | 0 => .ofLabel (.op .zero) .nil
    | 1 => .ofLabel (.theta 0) (nestedPair 0 1)
    | 2 => .ofLabel (.theta 0) (nestedPair 1 2)
    | _ => .ofLabel (.eval 0) (nestedPair 2 0)
  roots := .cons (nestedRef 3) (nestedPair 2 1)

private def nestedInput : Output Op [] outputs 1 := ⟨4, ⟨nested, Classes.discrete⟩⟩
private def nestedPrefix := Dedup.Worklist.run Op.zero 1 nestedInput
private def nestedRun := Dedup.Worklist.run Op.zero 2 nestedInput

#guard evalOperands nested == [[2, 0]]
#guard Dedup.Worklist.next Op.zero nestedInput == some ⟨3, by decide⟩
#guard (Dedup.Worklist.run Op.zero 0 nestedInput).report.stop == .exhausted
#guard nestedPrefix.report.sites == [3]
#guard nestedPrefix.report.stop == .exhausted
#guard nestedPrefix.state.1 == 5
#guard (Dedup.close Op.zero nestedInput [3]).1 == 5
#guard Dedup.Worklist.enabledAt Op.zero (Dedup.close Op.zero nestedInput [3]) 4
#guard nestedRun.report.sites == [3, 4]
#guard nestedRun.report.stop == .fixed
#guard nestedRun.state.1 == 6
#guard evalOperands nestedRun.state.2.graph == [[2, 0], [1, 0], [0, 0]]
#guard refNumbers nestedRun.state.2.graph.roots == [3, 2, 1]
#guard (Dedup.Worklist.run Op.zero 0 nestedRun.state).report.stop == .fixed
#guard (Dedup.Worklist.check Op.zero 2 nestedInput nestedRun.report).isSome

private theorem nestedWF : WellFounded nested.Demand :=
  nested.demandWellFounded_of_check
    [.phase (fun i => if i = 3 then 1 else 0), .counter 0,
      .phase (fun i => if i = 2 then 2 else if i = 1 then 1 else 0)]
    (by decide)

example (initial : Option (ULift Nat)) :
    ∃ after : WellFounded nestedRun.state.2.graph.Demand,
      nestedRun.state.2.classes.Valid (nestedRun.state.2.graph.denote (arithmetic initial) .nil after) ∧
      ∀ idx, nestedRun.state.2.graph.observe (arithmetic initial)
        (nestedRun.state.2.graph.denote (arithmetic initial) .nil after) idx =
        nested.observe (arithmetic initial) (nested.denote (arithmetic initial) .nil nestedWF) idx := by
  have preserved : Dedup.Preserves (arithmetic initial) .nil nestedInput nestedRun.state :=
    Dedup.Worklist.check_sound (Dedup.Worklist.run_checked (zero := Op.zero) 2 nestedInput) rfl
  exact preserved nestedWF Classes.discrete_valid

/-- The roots anchor a redex and two exact RHS copies to distinct addresses. -/
private def anchored : Graph Op [] outputs 7 1 :=
  { biggerGraph with
    node := fun i => if i = 4 then .ofLabel (.eval 0) (biggerPair 1 3) else biggerGraph.node i
    roots := .cons (biggerRef 6) (biggerPair 4 5) }

private def anchoredSmall : State Op [] outputs 7 1 := ⟨anchored, Classes.discrete⟩
private def anchoredLarge : State Op [] outputs 7 1 := ⟨anchored, Classes.discrete.merge 6 5⟩
private def anchoredMatch : ZeroSample anchored 6 .zero :=
  (ZeroSample.matchAt (g := anchored) 6 .zero).get (by decide)

-- The smaller pass joins 6 to its first RHS, 4. The larger pass keeps
-- the existing join with 5. Ordered roots prevent swapping the copies.
example : Comparable ⟨7, anchoredSmall⟩ ⟨7, anchoredLarge⟩ ∧
    ¬ Comparable (Dedup.ensure (s := anchoredSmall) anchoredMatch)
      (Dedup.ensure (s := anchoredLarge) anchoredMatch) := by
  constructor
  · refine ⟨{ Embedding.refl anchoredSmall with classes := ?_ }⟩
    intro a b h
    rw [show a = b from h]
  · change ¬ Comparable
      ⟨7, ⟨anchored, Classes.discrete.merge 6 4⟩⟩ ⟨7, anchoredLarge⟩
    rintro ⟨e⟩
    have redex : e.vertices.address 6 = 6 :=
      (congrArg (fun roots => (roots.get .head).id) e.roots).symm
    have rhs : e.vertices.address 4 = 4 :=
      (congrArg (fun roots => (roots.get (.tail .head)).id) e.roots).symm
    have clash := e.classes 6 4 (Classes.merge_equates Classes.discrete 6 4)
    rw [redex, rhs] at clash
    exact (by decide : anchoredLarge.classes 6 ≠ anchoredLarge.classes 4) clash

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Tests

namespace Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Tests

private abbrev Marks := Bool × Bool

private def covers (a b : Marks) : Prop :=
  (a.1 = true → b.1 = true) ∧ (a.2 = true → b.2 = true)

private theorem covers_refl (a : Marks) : covers a a := ⟨id, id⟩

private theorem covers_trans ⦃a b c : Marks⦄ (left : covers a b) (right : covers b c) : covers a c :=
  ⟨right.1 ∘ left.1, right.2 ∘ left.2⟩

private theorem covers_antisymm ⦃a b : Marks⦄ (left : covers a b) (right : covers b a) : a = b := by
  rcases a with ⟨(_ | _), (_ | _)⟩ <;> rcases b with ⟨(_ | _), (_ | _)⟩ <;>
    simp_all [covers]

private def mark (chooseFirst : Bool) (a : Marks) : Marks :=
  if chooseFirst then (true, a.2) else (a.1, true)

private def marking : Family Marks Bool :=
  fun label a b => b = a ∨ b = mark label a

private theorem marking_inflationary (label : Bool) : Inflationary covers (marking label) := by
  rintro a b (rfl | rfl)
  · exact covers_refl _
  · cases label <;> simp [covers, mark]

private theorem marking_monotone (label : Bool) : MonotoneSimulation covers (marking label) := by
  rintro a b next above (rfl | rfl)
  · exact ⟨b, .inl rfl, above⟩
  · refine ⟨mark label b, .inr rfl, ?_⟩
    cases label with
    | false => exact ⟨above.1, fun _ => rfl⟩
    | true => exact ⟨fun _ => rfl, above.2⟩

private theorem marking_terminal : ∀ next, ¬ PaperStep marking (true, true) next := by
  rintro next ⟨⟨label, rfl | rfl⟩, unequal⟩
  · exact unequal rfl
  · exact unequal (by cases label <;> rfl)

private theorem marking_first_then_second :
    Relation.ReflTransGen (PaperStep marking) (false, false) (true, true) := by
  have first : PaperStep marking (false, false) (true, false) := ⟨⟨true, .inr rfl⟩, by decide⟩
  have second : PaperStep marking (true, false) (true, true) := ⟨⟨false, .inr rfl⟩, by decide⟩
  exact (Relation.ReflTransGen.single first).tail second

private theorem marking_second_then_first :
    Relation.ReflTransGen (PaperStep marking) (false, false) (true, true) := by
  have first : PaperStep marking (false, false) (false, true) := ⟨⟨false, .inr rfl⟩, by decide⟩
  have second : PaperStep marking (false, true) (true, true) := ⟨⟨true, .inr rfl⟩, by decide⟩
  exact (Relation.ReflTransGen.single first).tail second

-- Both schedules take strict steps. Their common final state still admits
-- a stuttering analysis, and every paper normal form must equal it.
example : PaperNormalForm marking (false, false) (true, true) ∧
    Step marking (true, true) (true, true) ∧
    ∀ final, PaperNormalForm marking (false, false) final → final = (true, true) := by
  have stable : PaperNormalForm marking (false, false) (true, true) :=
    ⟨marking_first_then_second, marking_terminal⟩
  have alternate : PaperNormalForm marking (false, false) (true, true) :=
    ⟨marking_second_then_first, stable.2⟩
  exact ⟨stable, ⟨true, .inl rfl⟩, fun _ normal =>
    paperNormalForm_unique covers_refl covers_trans covers_antisymm
      marking_inflationary marking_monotone normal alternate⟩

/-- State zero is below both terminal representatives, which compare in
both directions but have distinct identities. -/
private def sameInfo (a b : Fin 3) : Prop := a = 0 ∨ b ≠ 0
private def aliases : Family (Fin 3) Unit := fun _ a b => b = a ∨ a = 0

private theorem sameInfo_refl (a : Fin 3) : sameInfo a a := Classical.em _

private theorem sameInfo_trans ⦃a b c : Fin 3⦄ (ab : sameInfo a b) (bc : sameInfo b c) : sameInfo a c :=
  ab.elim Or.inl fun hb => Or.inr (bc.resolve_left hb)

private theorem aliases_inflationary (label : Unit) : Inflationary sameInfo (aliases label) := by
  rintro a b (rfl | seed)
  · exact sameInfo_refl _
  · exact .inl seed

private theorem aliases_monotone (label : Unit) : MonotoneSimulation sameInfo (aliases label) := by
  intro a b next _ _
  by_cases seed : b = 0
  · exact ⟨next, .inr seed, sameInfo_refl _⟩
  · exact ⟨b, .inl rfl, .inr seed⟩

private theorem alias_terminal {a : Fin 3} (nonseed : a ≠ 0) : ∀ next, ¬ PaperStep aliases a next := by
  rintro next ⟨⟨_, rfl | seed⟩, different⟩
  · exact different rfl
  · exact nonseed seed

private theorem alias_paper_normal {a : Fin 3} (nonseed : a ≠ 0) : PaperNormalForm aliases 0 a :=
  ⟨.single ⟨⟨(), .inr rfl⟩, Ne.symm nonseed⟩, alias_terminal nonseed⟩

private theorem alias_stable_normal {a : Fin 3} (nonseed : a ≠ 0) : StableNormalForm sameInfo aliases 0 a := by
  refine ⟨.single ⟨(), .inr rfl⟩, ?_⟩
  rintro next ⟨_, rfl | seed⟩
  · exact sameInfo_refl _
  · exact (nonseed seed).elim

-- Literal uniqueness fails if antisymmetry is dropped, even for reachable
-- states that are terminal under the paper's inequality filter.
example : PaperNormalForm aliases 0 1 ∧ PaperNormalForm aliases 0 2 ∧ (1 : Fin 3) ≠ 2 :=
  ⟨alias_paper_normal (by decide), alias_paper_normal (by decide), by decide⟩

example : sameInfo 1 2 ∧ sameInfo 2 1 :=
  stableNormalForm_unique sameInfo_refl sameInfo_trans aliases_inflationary aliases_monotone
    (alias_stable_normal (by decide)) (alias_stable_normal (by decide))

end Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Tests

namespace Silmaril.SSA.Peggy.Worked.EvalScale.Tests

open PEG
open RVSDG (Tuple)
open PEG.Simple (Stmt Expr Exec)
open PEG.Simple.Revert.While.Region
open EPEG (Classes)
open EPEG.Saturation.Extension (State)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | five : Op [] .count
  | succ : Op [.count] .count
  | exit : Op [.count] .bool
  | atLeast : Op [.count, .count] .bool
  | negate : Op [.bool] .bool
  | mul : Op [.count, .count] .count
  | add : Op [.count, .count] .count
  deriving DecidableEq

private abbrev result : List (Ty Unit) := [.count, .count, .count, .count]

private abbrev sort (i : Fin 8) : Ty Unit := if i = 3 then .bool else .count

private def r (i : Fin 8) (ty : sort i = .count) : Ref sort .count := ⟨i, ty⟩
private def pair (a b : Ref sort .count) : Tuple (Ref sort) [.count, .count] :=
  .cons a (.cons b .nil)

/-- Figure 6(b) with an explicit exit predicate x ≥ 3 and additional
observations of the unscaled result and the exit index. -/
private def graph (varyingFactor : Bool) : Graph Op [] result 8 1 where
  forest := ⟨fun _ => none⟩
  sort := sort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (pair (r 1 rfl) (r 2 rfl))
    | 1 => .ofLabel (.op .zero) .nil
    | 2 => .ofLabel (.op .succ) (.cons (r 0 rfl) .nil)
    | 3 => .ofLabel (.op .exit) (.cons (r 0 rfl) .nil)
    | 4 => .ofLabel (.pass 0) (.cons ⟨3, rfl⟩ .nil)
    | 5 => .ofLabel (.eval 0) (pair (r 0 rfl) (r 4 rfl))
    | 6 => .ofLabel (.op .five) .nil
    | 7 => .ofLabel (.op .mul) (pair (if varyingFactor then r 0 rfl else r 6 rfl) (r 5 rfl))
  roots := .cons (r 7 rfl) (.cons (r 5 rfl) (pair (r 4 rfl) (r 7 rfl)))

private def source : State Op [] result 8 1 := ⟨graph false, Classes.discrete⟩
private def exitRef : Ref source.graph.sort .bool := ⟨3, rfl⟩
private def found : Match source.graph 7 .five .mul :=
  (Match.atSite source.graph 7 .five .mul).get (by decide)

private def expectedMatch : Match source.graph 7 .five .mul :=
  ⟨rfl, 0, r 6 rfl, r 5 rfl, r 0 rfl, r 4 rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

private def phase {n : Nat} (i : Fin n) : Nat :=
  match i.val with
  | 9 => 4
  | 7 => 3
  | 5 => 2
  | 4 | 8 => 1
  | _ => 0

private def rank (n : Nat) : DemandRank n 1 :=
  [.phase phase, .counter 0,
    .phase fun i => if i.val = 2 ∨ i.val = 3 then 2 else if i.val = 0 then 1 else 0]

#guard (Match.atSite (graph true) 7 .five .mul).isNone
#guard (found.plan.run 0).1 == 8
#guard (found.plan.run 1).1 == 9
#guard (found.plan.run 2).1 == 10
#guard found.saturated.classes 7 == found.saturated.classes 9
#guard refNumbers (found.extract.node 8).args == [6, 0]
#guard refNumbers (found.extract.node 9).args == [8, 4]
#guard refNumbers found.extract.roots == [9, 5, 4, 9]
#guard found.checkExtraction (rank 10)
#guard !(found.checkExtraction [])

private theorem wf : WellFounded source.graph.Demand :=
  source.graph.demandWellFounded_of_check (rank 8) (by decide)

private def model (failsAtZero : Bool) : Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .five, .nil => some ⟨5⟩
    | .succ, .cons a .nil => some ⟨a.down + 1⟩
    | .exit, .cons a .nil => some ⟨decide (3 ≤ a.down)⟩
    | .atLeast, .cons a (.cons b .nil) => some ⟨decide (b.down ≤ a.down)⟩
    | .negate, .cons b .nil => some ⟨!b.down⟩
    | .mul, .cons a (.cons b .nil) =>
      if failsAtZero && b.down == 0 then none else some ⟨a.down * b.down⟩
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩

private theorem totalLaw : Law (model false) Op.five Op.mul :=
  ⟨⟨5⟩, rfl, fun _ => rfl⟩

private def clock (k : Nat) : Index 1 := fun _ => k

private theorem reset (idx : Index 1) (k : Nat) : idx.set 0 k = clock k := by
  funext loop
  have h : loop = 0 := Subsingleton.elim _ _
  subst loop
  rfl

private noncomputable def values (fault : Bool) := source.graph.denote (model fault) .nil wf

private theorem solves (fault : Bool) : source.graph.Solves (model fault) .nil (values fault) :=
  source.graph.denote_solves (model fault) .nil wf

private theorem counter (fault : Bool) (k : Nat) :
    Rules.readRef (values fault) (r 0 rfl) (clock k) = some ⟨k⟩ := by
  induction k with
  | zero =>
    exact (Rules.theta_zero (solves fault) (r := r 0 rfl) (initial := r 1 rfl)
      (feedback := r 2 rfl) (loop := 0) HEq.rfl rfl).trans (solves fault (1, clock 0))
  | succ k ih =>
    rw [Rules.theta_succ (solves fault) (r := r 0 rfl) (initial := r 1 rfl)
      (feedback := r 2 rfl) (loop := 0) HEq.rfl (k := k) rfl, reset]
    rw [Rules.unary_at (solves fault) (r := r 2 rfl) (arg := r 0 rfl) (op := Op.succ) HEq.rfl, ih]
    rfl

private theorem predicate (fault : Bool) (k : Nat) :
    Rules.readRef (values fault) exitRef (clock k) = some ⟨decide (3 ≤ k)⟩ := by
  rw [Rules.unary_at (solves fault) (r := exitRef) (arg := r 0 rfl) (op := Op.exit) HEq.rfl, counter]
  rfl

private theorem exitIndex (fault : Bool) (idx : Index 1) :
    Rules.readRef (values fault) (r 4 rfl) idx = some ⟨3⟩ := by
  rw [Rules.pass_at (solves fault) (r := r 4 rfl) (cond := exitRef) (loop := 0) HEq.rfl]
  have samples : (fun j => (Rules.readRef (values fault)
      exitRef (idx.set 0 j)).map ULift.down) = fun j => some (decide (3 ≤ j)) := by
    funext j
    rw [reset, predicate]
    rfl
  rw [samples]
  have first : firstTrue (fun j => some (decide (3 ≤ j))) = some 3 := by
    apply (firstTrue_eq_some_iff _ _).mpr
    constructor
    · exact (monotonize_eq_some_iff _ _ _).mpr ⟨rfl, fun _ _ => rfl⟩
    · intro j earlier yes
      have impossible := ((monotonize_eq_some_iff _ _ _).mp yes).1
      exact (Nat.not_le_of_lt earlier) (of_decide_eq_true (Option.some.inj impossible))
  rw [first]
  rfl

private theorem sampled (fault : Bool) (idx : Index 1) :
    Rules.readRef (values fault) (r 5 rfl) idx = some ⟨3⟩ := by
  rw [Rules.eval_at (solves fault) (r := r 5 rfl) (source := r 0 rfl) (count := r 4 rfl)
    (loop := 0) HEq.rfl, exitIndex]
  change monotonize (fun j => Rules.readRef (values fault) (r 0 rfl) (idx.set 0 j)) 3 = some ⟨3⟩
  apply (monotonize_eq_some_iff _ _ _).mpr
  exact ⟨by rw [reset, counter], fun j _ => by rw [reset, counter]; rfl⟩

private theorem scaled (fault : Bool) (idx : Index 1) :
    Rules.readRef (values fault) (r 7 rfl) idx = some ⟨15⟩ := by
  have five : Rules.readRef (values fault) (r 6 rfl) idx = some ⟨5⟩ := solves fault (6, idx)
  rw [binary_at (solves fault) (r := r 7 rfl) (a := r 6 rfl) (b := r 5 rfl) (op := Op.mul)
    HEq.rfl, five, sampled]
  cases fault <;> rfl

private theorem observed (idx : Index 1) :
    source.graph.observe (model false) (values false) idx =
      .cons (some ⟨15⟩) (.cons (some ⟨3⟩) (.cons (some ⟨3⟩) (.cons (some ⟨15⟩) .nil))) := by
  change (show Tuple (fun t => Option ((model false).Value t)) result from
    .cons (Rules.readRef (values false) (r 7 rfl) idx)
      (.cons (Rules.readRef (values false) (r 5 rfl) idx)
        (.cons (Rules.readRef (values false) (r 4 rfl) idx)
          (.cons (Rules.readRef (values false) (r 7 rfl) idx) .nil)))) = _
  rw [scaled, sampled, exitIndex]

private theorem ranked : (rank 10).check found.extract = true := by
  rw [show found = expectedMatch from rfl]
  decide

private theorem checked : found.checkExtraction (rank 10) = true :=
  found.check_of_rank (rank 10) ranked

example (idx : Index 1) :
    found.extract.observe (model false)
      (found.extract.denote (model false) .nil
        ((found.selection (rank 10)).demandWellFounded (Bool.and_eq_true_iff.mp checked).1)) idx =
      .cons (some ⟨15⟩) (.cons (some ⟨3⟩) (.cons (some ⟨3⟩) (.cons (some ⟨15⟩) .nil))) :=
  (found.extract_sound (m := model false) (env := .nil) wf Classes.discrete_valid totalLaw
    (rank 10) checked idx).symm.trans (observed idx)

-- Dropping totality changes the result on the same native counter stream.
private noncomputable def unsafeSample (k : Nat) : Option (ULift Nat) :=
  Rules.readRef (values true) (r 0 rfl) (clock k)

private def partialScale (a : ULift Nat) : Option (ULift Nat) :=
  (model true).run Op.mul (.cons ⟨5⟩ (.cons a .nil))

example : ¬ Law (model true) Op.five Op.mul := by
  rintro ⟨k, literal, total⟩
  have fixed : k = ⟨5⟩ := (Option.some.inj literal).symm
  subst k
  have bad := total ⟨0⟩
  cases bad

example (idx : Index 1) :
    Rules.readRef (values true) (r 7 rfl) idx = some ⟨15⟩ ∧
      monotonize (fun j => (unsafeSample j).bind partialScale) 3 = none := by
  refine ⟨scaled true idx, ?_⟩
  cases yes : monotonize (fun j => (unsafeSample j).bind partialScale) 3 with
  | none => rfl
  | some value =>
    have defined := ((monotonize_eq_some_iff _ _ _).mp yes).2 0 (by decide)
    rw [unsafeSample, counter] at defined
    cases defined

private def strengthOps : StrengthReduction.Profile Op := ⟨.zero, .five, .succ, .mul, .add⟩

private def reduced : StrengthReduction.Match found.extract 8 strengthOps :=
  (StrengthReduction.Match.atSite found.extract 8 strengthOps).get (by decide)

private def strengthRank : DemandRank 11 1 :=
  [.phase fun i => if i.val = 8 ∨ i.val = 10 then 0 else phase i,
    .counter 0,
    .phase fun i => if i.val = 2 ∨ i.val = 3 ∨ i.val = 10 then 2
      else if i.val = 0 ∨ i.val = 8 then 1 else 0]

#guard (reduced.candidate.node 8).label.thetaLoop == some 0
#guard refNumbers (reduced.candidate.node 8).args == [1, 10]
#guard refNumbers (reduced.candidate.node 10).args == [6, 8]
#guard refNumbers (reduced.candidate.node 9).args == [8, 4]
#guard refNumbers (reduced.candidate.node 4).args == [3]
#guard refNumbers reduced.candidate.roots == [9, 5, 4, 9]
#guard strengthRank.check reduced.candidate
#guard !(DemandRank.check [] reduced.candidate)
#guard (PEG.Projection.dependencyRows reduced.candidate).map (List.map Fin.val) ==
  some [0, 1, 2, 3, 4, 5, 6, 8, 9, 10]

private def strengthLaw : StrengthReduction.Law (model false) strengthOps where
  baseValue := ⟨0⟩
  factorValue := ⟨5⟩
  definedBase := rfl
  definedFactor := rfl
  fixedBase := rfl
  feedback a := by
    change some (ULift.up (5 * (a.down + 1))) = some (ULift.up (5 + 5 * a.down))
    rw [Nat.mul_succ, Nat.add_comm (5 * a.down) 5]

private def expectedReduced : StrengthReduction.Match expectedMatch.extract 8 strengthOps :=
  ⟨rfl, 0, ⟨6, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 800000 in
private theorem strengthRanked : strengthRank.check reduced.candidate = true := by
  change strengthRank.check expectedReduced.candidate = true
  apply List.all_eq_true.mpr
  intro i _
  fin_cases i <;> decide

private theorem figure6_rewrites (idx : Index 1) :
    source.graph.observe (model false) (values false) idx =
      reduced.candidate.observe (model false)
        (reduced.candidate.denote (model false) .nil
          (reduced.candidate.demandWellFounded_of_check strengthRank strengthRanked)) idx := by
  have motion := found.extract_sound (m := model false) (env := .nil) wf Classes.discrete_valid totalLaw
    (rank 10) checked idx
  have strength := reduced.candidate_sound (env := .nil) strengthLaw
    ((found.selection (rank 10)).demandWellFounded (Bool.and_eq_true_iff.mp checked).1)
    strengthRank strengthRanked idx
  exact motion.trans strength

example (idx : Index 1) :
    reduced.candidate.observe (model false)
      (reduced.candidate.denote (model false) .nil
        (reduced.candidate.demandWellFounded_of_check strengthRank strengthRanked)) idx =
      .cons (some ⟨15⟩) (.cons (some ⟨3⟩) (.cons (some ⟨3⟩) (.cons (some ⟨15⟩) .nil))) :=
  (figure6_rewrites idx).symm.trans (observed idx)

-- The reverter receives instruction identities only. It obtains the
-- carried vector and the ordered readouts from the actual rewritten PEG.
private def roles : Closed.Automatic.Roles Op := ⟨.zero, .succ, .negate⟩

private def checkedRegion := Closed.Automatic.extract reduced.candidate roles

private def relocation : Equiv.Perm (Fin 11) :=
  (Equiv.swap 0 8).trans ((Equiv.swap 4 9).trans (Equiv.swap 3 6))

private def relocated := reduced.candidate.reindex relocation (Equiv.refl (Fin 1))
private def checkedRelocated := Closed.Automatic.extract relocated roles

-- A second, well-typed pass for the same predicate does not satisfy the
-- shared-pass boundary when one of the evals names it instead.
private def wrongPass : Graph Op [] result 11 1 :=
  { reduced.candidate with node := fun i =>
    if h : i = 5 then h.symm ▸ Node.ofLabel (.eval 0) (.cons ⟨0, rfl⟩ (.cons ⟨7, rfl⟩ .nil))
    else if h : i = 7 then h.symm ▸ Node.ofLabel (.pass 0) (.cons ⟨3, rfl⟩ .nil)
    else reduced.candidate.node i }

-- Keep the tick opcode and zero initializer but wire the tick to the
-- other θ. Neither carried slot now implements the unit recurrence.
private def wrongClock : Graph Op [] result 11 1 :=
  { reduced.candidate with node := fun i =>
    if h : i = 2 then h.symm ▸ Node.ofLabel (.op Op.succ) (.cons ⟨8, rfl⟩ .nil)
    else reduced.candidate.node i }

private def asList : {ts : List (Ty Unit)} → Tuple (model false).Value ts → List Nat
  | _, .nil => []
  | .count :: _, .cons value rest => value.down :: asList rest
  | .bool :: _, .cons _ rest | .data _ :: _, .cons _ rest => asList rest

private def runFigure6 {g : Graph Op [] result 11 1}
    (recovered : Option (Closed.Automatic.Recovered g roles)) (fuel : Nat) : Option (List Nat) := do
  let cert ← recovered
  (cert.certificate.runFuel (model false) fuel .nil).map asList

private def opcode {is : List (Ty Unit)} {t : Ty Unit} : Op is t → String
  | .zero => "zero" | .five => "five" | .succ => "succ" | .exit => "exit"
  | .atLeast => "atLeast"
  | .mul => "mul" | .add => "add" | .negate => "negate"

mutual
private def exprOpcodes {vars : List (Ty Unit)} {t : Ty Unit} : Expr Op vars t → List String
  | .var _ => []
  | .op instr args => opcode instr :: argsOpcodes args
private def argsOpcodes {vars args : List (Ty Unit)} : PEG.Simple.Args Op vars args → List String
  | .nil => []
  | .cons e es => exprOpcodes e ++ argsOpcodes es
end

private def opcodes {loops : Bool} {vars outs : List (Ty Unit)} : Stmt Op loops vars outs → List String
  | .assign e => exprOpcodes e
  | .project _ => []
  | .seq a b => opcodes a ++ opcodes b
  | .branch e a b => exprOpcodes e ++ opcodes a ++ opcodes b
  | .while _ e body => exprOpcodes e ++ opcodes body

#guard runFigure6 checkedRegion 3 == some [15, 3, 3, 15]
#guard (runFigure6 checkedRegion 2).isNone
#guard (checkedRegion.map fun recovered => opcodes recovered.certificate.revert) ==
  some ["zero", "exit", "negate", "succ", "five", "add", "exit"]
#guard (checkedRegion.bind fun recovered => do
  let cert := recovered.certificate
  let initial ← cert.startCode.runLoopFree (model false) .nil
  (cert.body.runLoopFree (model false) initial).map asList) == some [1, 5]

#guard runFigure6 checkedRelocated 3 == some [15, 3, 3, 15]
#guard (runFigure6 checkedRelocated 2).isNone
#guard (checkedRelocated.map fun recovered => opcodes recovered.certificate.step.lower) ==
  some ["five", "add", "succ"]
#guard (checkedRelocated.map fun recovered =>
  let d := recovered.certificate.descriptor
  ((d.theta.get d.clock).id.val, d.pass.id.val, d.exit.id.val)) == some (8, 9, 6)

#guard (Closed.Automatic.inferRank wrongPass).check wrongPass
#guard (Closed.Automatic.inferRank wrongClock).check wrongClock
#guard (Closed.Automatic.extract wrongPass roles).isNone
#guard (Closed.Automatic.extract wrongClock roles).isNone

private theorem figure6Laws : roles.Laws (model false) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

example (recovered : Closed.Automatic.Recovered reduced.candidate roles)
    (idx : Index 1) (out : Tuple (model false).Value result)
    (ran : Exec (model false) recovered.certificate.revert .nil (some out)) :
    source.graph.observe (model false) (values false) idx = out.map (fun _ => some) :=
  (figure6_rewrites idx).trans (recovered.observe_of_exec figure6Laws .nil idx ran)

private abbrev external : List (Ty Unit) := [.count, .bool, .count, .count]
private abbrev parameterResults : List (Ty Unit) := .bool :: result

private def parameterSort (i : Fin 16) : Ty Unit :=
  if i = 3 ∨ i = 14 then .bool else .count

private def c (i : Fin 16) (typed : parameterSort i = .count) : Ref parameterSort .count :=
  ⟨i, typed⟩

private def two (x y : Ref parameterSort .count) : Tuple (Ref parameterSort) [.count, .count] :=
  .cons x (.cons y .nil)

-- Clock starts at zero. The accumulator starts at base + delta and
-- advances by delta plus the old clock. Parameter rows 8 and 15 alias
-- the same input, with one read inside the loop and one in the readout.
private def parameterLoop : Graph Op external parameterResults 16 1 where
  forest := ⟨fun _ => none⟩
  sort := parameterSort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (two (c 1 rfl) (c 2 rfl))
    | 1 => .ofLabel (.op .zero) .nil
    | 2 => .ofLabel (.op .succ) (.cons (c 0 rfl) .nil)
    | 3 => .ofLabel (.op .atLeast) (two (c 0 rfl) (c 6 rfl))
    | 4 => .ofLabel (.pass 0) (.cons ⟨3, rfl⟩ .nil)
    | 5 => .ofLabel (.theta 0) (two (c 9 rfl) (c 11 rfl))
    | 6 => .ofLabel (.param .head) .nil
    | 7 => .ofLabel (.param (.tail (.tail .head))) .nil
    | 8 => .ofLabel (.param (.tail (.tail (.tail .head)))) .nil
    | 9 => .ofLabel (.op .add) (two (c 7 rfl) (c 8 rfl))
    | 10 => .ofLabel (.op .add) (two (c 5 rfl) (c 8 rfl))
    | 11 => .ofLabel (.op .add) (two (c 10 rfl) (c 0 rfl))
    | 12 => .ofLabel (.eval 0) (two (c 5 rfl) (c 4 rfl))
    | 13 => .ofLabel (.op .add) (two (c 12 rfl) (c 15 rfl))
    | 14 => .ofLabel (.param (.tail .head)) .nil
    | 15 => .ofLabel (.param (.tail (.tail (.tail .head)))) .nil
    | ⟨k + 16, bounded⟩ => False.elim (by omega)
  roots := .cons ⟨14, rfl⟩ (.cons (c 13 rfl) (.cons (c 4 rfl) (two (c 12 rfl) (c 13 rfl))))

private def parameterInputFor (m : Interpretation.{0,0,0} Op) (limit base delta : Nat)
    (echo : Bool) : Tuple m.Value external :=
  .cons ⟨limit⟩ (.cons ⟨echo⟩ (.cons ⟨base⟩ (.cons ⟨delta⟩ .nil)))

private abbrev parameterInput := parameterInputFor (model false)

private def inferredParameters := Closed.Automatic.extract parameterLoop roles

private def runParameters (fuel limit delta : Nat) (echo : Bool) : Option (Bool × List Nat) := do
  let recovered ← inferredParameters
  let .cons flag counts ←
    recovered.certificate.runFuel (model false) fuel (parameterInput limit 2 delta echo)
  return (flag.down, asList counts)

#guard runParameters 0 0 4 false == some (false, [10, 0, 6, 10])
#guard runParameters 3 3 4 true == some (true, [25, 3, 21, 25])
#guard runParameters 3 3 1 true == some (true, [10, 3, 9, 10])
#guard (runParameters 2 3 4 true).isNone
#guard (inferredParameters.map fun recovered => opcodes recovered.certificate.finish.lower) ==
  some ["add"]

-- The pass is well-ranked but is outside initializer scope.
private def earlyPass : Graph Op external parameterResults 16 1 :=
  { parameterLoop with node := fun i =>
    if h : i = 5 then h.symm ▸ Node.ofLabel (.theta 0) (two (c 4 rfl) (c 11 rfl))
    else parameterLoop.node i }

#guard (Closed.Automatic.inferRank earlyPass).check earlyPass
#guard (Closed.Automatic.extract earlyPass roles).isNone

example (recovered : Closed.Automatic.Recovered parameterLoop roles) (idx : Index 1)
    (input : Tuple (model false).Value external) (fuel : Nat)
    (output : Tuple (model false).Value parameterResults)
    (ran : recovered.certificate.runFuel (model false) fuel input = some output) :
    parameterLoop.observe (model false)
      (parameterLoop.denote (model false) input recovered.certificate.demandWellFounded) idx =
      output.map (fun _ => some) :=
  recovered.observe_of_exec figure6Laws input idx (recovered.certificate.exec_of_runFuel fuel input ran)

private theorem parameterCounter {m : Interpretation.{0,0,0} Op}
    {input : Tuple m.Value external} {vs : parameterLoop.Valuation m}
    (solved : parameterLoop.Solves m input vs) (laws : roles.Laws m) (k : Nat) :
    Rules.readRef vs (c 0 rfl) (clock k) = some ⟨k⟩ := by
  induction k with
  | zero =>
    rw [Rules.theta_zero solved (r := c 0 rfl) (initial := c 1 rfl) (feedback := c 2 rfl)
      (loop := 0) HEq.rfl rfl]
    exact (solved (1, clock 0)).trans laws.zero
  | succ k ih =>
    rw [Rules.theta_succ solved (r := c 0 rfl) (initial := c 1 rfl) (feedback := c 2 rfl)
      (loop := 0) HEq.rfl (k := k) rfl, reset,
      Rules.unary_at solved (r := c 2 rfl) (arg := c 0 rfl) (op := Op.succ) HEq.rfl,
      ih]
    exact laws.tick k

set_option backward.isDefEq.respectTransparency false in
private theorem parameterPass {m : Interpretation.{0,0,0} Op}
    {limit base delta : Nat} {echo : Bool}
    {vs : parameterLoop.Valuation m}
    (solved : parameterLoop.Solves m (parameterInputFor m limit base delta echo) vs)
    (laws : roles.Laws m)
    (ge : ∀ k : Nat, m.run Op.atLeast (.cons ⟨k⟩ (.cons ⟨limit⟩ .nil)) =
      some ⟨decide (limit ≤ k)⟩) (idx : Index 1) :
    Rules.readRef vs (c 4 rfl) idx = some ⟨limit⟩ := by
  let predRef : Ref parameterSort .bool := ⟨3, rfl⟩
  have flags (j : Nat) : Rules.readRef vs predRef (clock j) = some ⟨decide (limit ≤ j)⟩ := by
    have inputRead : Rules.readRef vs (c 6 rfl) (clock j) = some ⟨limit⟩ :=
      solved (6, clock j)
    rw [Rules.at_label solved (r := predRef)
      (label := .op Op.atLeast) (args := two (c 0 rfl) (c 6 rfl)) HEq.rfl]
    simp only [Label.interpret, two, collect, portAt, Fin.cases_zero, Fin.cases_succ, Option.elim]
    have left : Rules.readRef vs ((two (c 0 rfl) (c 6 rfl)).get .head) (clock j) = some ⟨j⟩ :=
      parameterCounter solved laws j
    have right : Rules.readRef vs ((two (c 0 rfl) (c 6 rfl)).get (.tail .head))
        (clock j) = some ⟨limit⟩ := inputRead
    erw [left, right]
    exact ge j
  have samples : (fun j => (Rules.readRef vs predRef (idx.set 0 j)).map ULift.down) =
      fun j => some (decide (limit ≤ j)) := by
    funext j
    rw [reset, flags]
    rfl
  rw [Rules.pass_at solved (r := c 4 rfl) (cond := predRef) (loop := 0) HEq.rfl, samples]
  have first : firstTrue (fun j => some (decide (limit ≤ j))) = some limit :=
    (PEG.Simple.firstTrue_eq_some_iff_samples _ _).mpr
      ⟨by simp, fun j lt => by simp [Nat.not_le_of_lt lt]⟩
  rw [first]
  rfl

private def accAt (base delta : Nat) : Nat → Nat
  | 0 => base + delta
  | k + 1 => accAt base delta k + delta + k

private theorem parameterAccumulator {limit base delta : Nat} {echo : Bool}
    {vs : parameterLoop.Valuation (model false)}
    (solved : parameterLoop.Solves (model false) (parameterInput limit base delta echo) vs)
    (k : Nat) :
    Rules.readRef vs (c 5 rfl) (clock k) = some ⟨accAt base delta k⟩ := by
  have increment (i : Index 1) : Rules.readRef vs (c 8 rfl) i = some ⟨delta⟩ := solved (8, i)
  induction k with
  | zero =>
    have seed : Rules.readRef vs (c 7 rfl) (clock 0) = some ⟨base⟩ := solved (7, clock 0)
    rw [Rules.theta_zero solved (r := c 5 rfl) (initial := c 9 rfl) (feedback := c 11 rfl)
      (loop := 0) HEq.rfl rfl,
      binary_at solved (r := c 9 rfl) (a := c 7 rfl) (b := c 8 rfl) (op := Op.add) HEq.rfl,
      seed, increment]
    rfl
  | succ k ih =>
    rw [Rules.theta_succ solved (r := c 5 rfl) (initial := c 9 rfl) (feedback := c 11 rfl)
      (loop := 0) HEq.rfl (k := k) rfl, reset,
      binary_at solved (r := c 11 rfl) (a := c 10 rfl) (b := c 0 rfl) (op := Op.add) HEq.rfl,
      binary_at solved (r := c 10 rfl) (a := c 5 rfl) (b := c 8 rfl) (op := Op.add) HEq.rfl,
      ih, increment, parameterCounter solved figure6Laws k]
    rfl

private def parameterOutput (limit base delta : Nat) (echo : Bool) :
    Tuple (model false).Value parameterResults :=
  let acc := accAt base delta limit
  .cons ⟨echo⟩
    (.cons ⟨acc + delta⟩ (.cons ⟨limit⟩ (.cons ⟨acc⟩ (.cons ⟨acc + delta⟩ .nil))))

private theorem parameterObserved {limit base delta : Nat} {echo : Bool}
    {vs : parameterLoop.Valuation (model false)}
    (solved : parameterLoop.Solves (model false) (parameterInput limit base delta echo) vs)
    (idx : Index 1) :
    parameterLoop.observe (model false) vs idx =
      (parameterOutput limit base delta echo).map (fun _ => some) := by
  have pass := parameterPass solved figure6Laws (fun _ => rfl) idx
  have sampled : Rules.readRef vs (c 12 rfl) idx = some ⟨accAt base delta limit⟩ := by
    rw [Rules.eval_at solved (r := c 12 rfl) (source := c 5 rfl) (count := c 4 rfl) (loop := 0)
      HEq.rfl, pass]
    change monotonize (fun j => Rules.readRef vs (c 5 rfl) (idx.set 0 j)) limit = _
    simp only [reset]
    exact (monotonize_eq_some_iff _ _ _).mpr
      ⟨parameterAccumulator solved limit, fun j _ => by rw [parameterAccumulator solved]; rfl⟩
  have inc : Rules.readRef vs (c 15 rfl) idx = some ⟨delta⟩ := solved (15, idx)
  have sum : Rules.readRef vs (c 13 rfl) idx = some ⟨accAt base delta limit + delta⟩ := by
    rw [binary_at solved (r := c 13 rfl) (a := c 12 rfl) (b := c 15 rfl) (op := Op.add)
      HEq.rfl, sampled, inc]
    rfl
  have flag : Rules.readRef vs (⟨14, rfl⟩ : Ref parameterSort .bool) idx = some ⟨echo⟩ :=
    solved (14, idx)
  change Tuple.cons (F := fun t => Option ((model false).Value t))
    (Rules.readRef vs (⟨14, rfl⟩ : Ref parameterSort .bool) idx)
    (.cons (Rules.readRef vs (c 13 rfl) idx) (.cons (Rules.readRef vs (c 4 rfl) idx)
      (.cons (Rules.readRef vs (c 12 rfl) idx) (.cons (Rules.readRef vs (c 13 rfl) idx) .nil)))) = _
  rw [flag, sum, pass, sampled]
  rfl

private theorem parameterTotal : ∀ {ins out} (op : Op ins out) args,
    ∃ val, (model false).run op args = some val
  | _, _, .zero, .nil => ⟨_, rfl⟩
  | _, _, .five, .nil => ⟨_, rfl⟩
  | _, _, .succ, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .exit, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .negate, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .atLeast, .cons _ (.cons _ .nil) => ⟨_, rfl⟩
  | _, _, .add, .cons _ (.cons _ .nil) => ⟨_, rfl⟩
  | _, _, .mul, .cons _ (.cons _ .nil) => ⟨_, rfl⟩

private def isPass {t : Ty Unit} (row : Node Op external (Fin 1) parameterSort t) : Bool :=
  match t, row with
  | .count, ⟨_, .pass _, _⟩ => true
  | _, _ => false

private theorem isPass_cast {a b : Ty Unit} (h : a = b)
    (row : Node Op external (Fin 1) parameterSort a) : isPass (h ▸ row) = isPass row := by
  cases h
  rfl

private theorem parameterPassRef {r : Ref parameterSort .count} {guard : Ref parameterSort .bool}
    (wired : Closed.nodeAt parameterLoop r = .ofLabel (.pass 0) (.cons guard .nil)) :
    r = c 4 rfl := by
  have shape (i : Fin 16) : isPass (parameterLoop.node i) = decide (i = 4) := by
    fin_cases i <;> rfl
  have label : isPass (parameterLoop.node r.id) = true :=
    (isPass_cast r.typed (parameterLoop.node r.id)).symm.trans (congrArg isPass wired)
  have addr := of_decide_eq_true ((shape r.id).symm.trans label)
  obtain ⟨i, typed⟩ := r
  change i = 4 at addr
  subst i
  rfl

private theorem runFromPEG (recovered : Closed.Automatic.Recovered parameterLoop roles)
    (limit base delta : Nat) (echo : Bool) :
    recovered.certificate.runFuel (model false) limit (parameterInput limit base delta echo) =
      some (parameterOutput limit base delta echo) := by
  let cert := recovered.certificate
  let inputs := parameterInput limit base delta echo
  have solved := parameterLoop.denote_solves (model false) inputs cert.demandWellFounded
  have pass : cert.FirstExit (model false)
      (parameterLoop.denote (model false) inputs cert.demandWellFounded) (clock 0) limit := by
    unfold Closed.Accepted.FirstExit
    rw [parameterPassRef cert.boundary.pass]
    exact parameterPass solved figure6Laws (fun _ => rfl) _
  exact recovered.runFuel_of_firstExit figure6Laws (cert.total_of_primitives parameterTotal)
    inputs (clock 0) limit pass (parameterObserved solved _)

/-- Each successful discovery carries a SIMPLE derivation proved from
the PEG pass and ordered observations. -/
private def certifiedParameterRun (limit base delta : Nat) (echo : Bool) :
    Option {a : Closed.Automatic.Recovered parameterLoop roles //
      Exec (model false) a.certificate.revert (parameterInput limit base delta echo)
        (some (parameterOutput limit base delta echo))} :=
  inferredParameters.map fun a =>
    ⟨a, a.certificate.exec_of_runFuel limit _ (runFromPEG a limit base delta echo)⟩

#guard (certifiedParameterRun 0 2 4 false).isSome
#guard (certifiedParameterRun 3 2 4 true).isSome

-- Returning only the pass leaves the accumulator unobserved in Figure 11.
-- SIMPLE still commits the entire vector, whose first update adds 6 and 4.
private def passOnly := parameterLoop.withRoots (.cons (c 4 rfl) .nil)

private def partialUpdate : Interpretation.{0,0,0} Op where
  carrier := (model false).carrier
  run instr args := match instr, args with
    | .add, .cons a (.cons b .nil) =>
      if a.down = 6 ∧ b.down = 4 then none else some ⟨a.down + b.down⟩
    | instr, args => (model false).run instr args

private abbrev partialInput := parameterInputFor partialUpdate 3 2 4 true

private noncomputable def partialValues (a : Closed.Automatic.Recovered passOnly roles) :=
  passOnly.denote partialUpdate partialInput a.certificate.demandWellFounded

private theorem partialPass (a : Closed.Automatic.Recovered passOnly roles) :
    Rules.readRef (partialValues a) (c 4 rfl) (clock 0) = some ⟨3⟩ :=
  parameterPass (passOnly.denote_solves partialUpdate partialInput a.certificate.demandWellFounded)
    (⟨rfl, fun _ => rfl, fun _ => rfl⟩ : roles.Laws partialUpdate) (fun _ => rfl) (clock 0)

private theorem partialObservations (a : Closed.Automatic.Recovered passOnly roles) :
    a.certificate.FirstExit partialUpdate (partialValues a) (clock 0) 3 ∧
    passOnly.observe partialUpdate (partialValues a) (clock 0) = .cons (some ⟨3⟩) .nil := by
  refine ⟨?_, ?_⟩
  · unfold Closed.Accepted.FirstExit
    rw [parameterPassRef a.certificate.boundary.pass]
    exact partialPass a
  · change Tuple.cons (F := fun t => Option (partialUpdate.Value t))
      (Rules.readRef (partialValues a) (c 4 rfl) (clock 0)) .nil = _
    rw [partialPass]

private theorem noSuccessfulRun (a : Closed.Automatic.Recovered passOnly roles)
    {store : Tuple partialUpdate.Value a.certificate.storeTypes}
    (start : a.certificate.startCode.runLoopFree partialUpdate partialInput = some store)
    (test : a.certificate.test.eval partialUpdate store = some ⟨true⟩)
    (update : a.certificate.body.runLoopFree partialUpdate store = none) :
    ¬ ∃ out, Exec partialUpdate a.certificate.revert partialInput (some out) := by
  rintro ⟨_, ran⟩
  have failure : Exec partialUpdate a.certificate.revert partialInput none :=
    .seq (start ▸ a.certificate.startCode.runLoopFree_enableWhile partialInput)
      (.firstFailed (.whileBodyFailed test (update ▸ a.certificate.body.runLoopFree_enableWhile store)))
  have impossible := Exec.deterministic failure ran
  cases impossible

private def partialCounterexample :
    Option {a : Closed.Automatic.Recovered passOnly roles //
      (a.certificate.FirstExit partialUpdate (partialValues a) (clock 0) 3 ∧
        passOnly.observe partialUpdate (partialValues a) (clock 0) = .cons (some ⟨3⟩) .nil) ∧
        ¬ ∃ out, Exec partialUpdate a.certificate.revert partialInput (some out)} := do
  let a ← Closed.Automatic.extract passOnly roles
  match start : a.certificate.startCode.runLoopFree partialUpdate partialInput with
  | none => none
  | some store =>
    match test : a.certificate.test.eval partialUpdate store with
    | some ⟨true⟩ =>
      match update : a.certificate.body.runLoopFree partialUpdate store with
      | none => some ⟨a, partialObservations a, noSuccessfulRun a start test update⟩
      | some _ => none
    | _ => none

#guard partialCounterexample.isSome

private def wrongAdd : Interpretation.{0,0,0} Op where
  carrier := (model false).carrier
  run instr args := match instr, args with
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down + 1⟩
    | instr, args => (model false).run instr args

-- Definedness and invariance still hold, but the feedback law fails at zero.
example : Law wrongAdd Op.five Op.mul ∧ ¬ Nonempty (StrengthReduction.Law wrongAdd strengthOps) := by
  refine ⟨⟨⟨5⟩, rfl, fun _ => rfl⟩, ?_⟩
  rintro ⟨law⟩
  have factorEquals : law.factorValue = ⟨5⟩ := (Option.some.inj law.definedFactor).symm
  have step := law.feedback ⟨0⟩
  rw [factorEquals] at step
  have different : (5 : Nat) = 6 := congrArg ULift.down (Option.some.inj step)
  omega

end Silmaril.SSA.Peggy.Worked.EvalScale.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Tests

open RVSDG (Port Tuple)
open Simple.Revert.While.Region

private inductive Op : InstructionSet Unit where
  | zero : Op [] .count
  | succ : Op [.count] .count
  | atLeast : Op [.count, .count] .bool
  | add : Op [.count, .count] .count
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .succ, .cons n .nil => some ⟨n.down + 1⟩
    | .atLeast, .cons a (.cons b .nil) => some ⟨decide (b.down ≤ a.down)⟩
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private abbrev inputs := ([.count, .count] : List (Ty Unit))
private abbrev outputs := ([.count, .count, .count, .count] : List (Ty Unit))

private def pair {F : Ty Unit → Type} (a b : F .count) : Tuple F inputs :=
  .cons a (.cons b .nil)

private def four {F : Ty Unit → Type} (a b c d : F .count) : Tuple F outputs :=
  .cons a (.cons b (pair c d))

private def stageSort (i : Fin 9) : Ty Unit := if i = 3 then .bool else .count
private def s (i : Fin 9) (h : stageSort i = .count) : Ref stageSort .count := ⟨i, h⟩

-- The first stage returns succ(eval clock), the forwarded seed, the
-- pass count, and a repeated first result. The second uses the first
-- result as its limit and adds the seed to its own final counter.
private def stage (second : Bool) : Graph Op inputs outputs 9 1 where
  forest := ⟨fun _ => none⟩
  sort := stageSort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (pair (s 1 rfl) (s 2 rfl))
    | 1 => .ofLabel (.op .zero) .nil
    | 2 => .ofLabel (.op .succ) (.cons (s 0 rfl) .nil)
    | 3 => .ofLabel (.op .atLeast) (pair (s 0 rfl) (s 6 rfl))
    | 4 => .ofLabel (.pass 0) (.cons ⟨3, rfl⟩ .nil)
    | 5 => .ofLabel (.eval 0) (pair (s 0 rfl) (s 4 rfl))
    | 6 => .ofLabel (.param .head) .nil
    | 7 => .ofLabel (.param (.tail .head)) .nil
    | 8 =>
      if second then .ofLabel (.op .add) (pair (s 5 rfl) (s 7 rfl))
      else .ofLabel (.op .succ) (.cons (s 5 rfl) .nil)
  roots := if second then four (s 8 rfl) (s 4 rfl) (s 6 rfl) (s 8 rfl)
    else four (s 8 rfl) (s 7 rfl) (s 4 rfl) (s 8 rfl)

private def sort (i : Fin 16) : Ty Unit := if i = 3 ∨ i = 12 then .bool else .count
private def r (i : Fin 16) (h : sort i = .count) : Ref sort .count := ⟨i, h⟩

-- These are the actual original wires. The second guard uses row 8,
-- which is the first stage's computed exit observation. Row 7 is shared.
private def graph : Graph Op inputs outputs 16 2 where
  forest := ⟨fun _ => none⟩
  sort := sort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (pair (r 1 rfl) (r 2 rfl))
    | 1 => .ofLabel (.op .zero) .nil
    | 2 => .ofLabel (.op .succ) (.cons (r 0 rfl) .nil)
    | 3 => .ofLabel (.op .atLeast) (pair (r 0 rfl) (r 6 rfl))
    | 4 => .ofLabel (.pass 0) (.cons ⟨3, rfl⟩ .nil)
    | 5 => .ofLabel (.eval 0) (pair (r 0 rfl) (r 4 rfl))
    | 6 => .ofLabel (.param .head) .nil
    | 7 => .ofLabel (.param (.tail .head)) .nil
    | 8 => .ofLabel (.op .succ) (.cons (r 5 rfl) .nil)
    | 9 => .ofLabel (.theta 1) (pair (r 10 rfl) (r 11 rfl))
    | 10 => .ofLabel (.op .zero) .nil
    | 11 => .ofLabel (.op .succ) (.cons (r 9 rfl) .nil)
    | 12 => .ofLabel (.op .atLeast) (pair (r 9 rfl) (r 8 rfl))
    | 13 => .ofLabel (.pass 1) (.cons ⟨12, rfl⟩ .nil)
    | 14 => .ofLabel (.eval 1) (pair (r 9 rfl) (r 13 rfl))
    | 15 => .ofLabel (.op .add) (pair (r 14 rfl) (r 7 rfl))
    | ⟨k + 16, bound⟩ => False.elim (by omega)
  roots := four (r 15 rfl) (r 13 rfl) (r 8 rfl) (r 15 rfl)

private def layout : Layout graph (stage false) (stage true) where
  first i := match i with
    | 0 => r 0 rfl
    | 1 => r 1 rfl
    | 2 => r 2 rfl
    | 3 => ⟨3, rfl⟩
    | 4 => r 4 rfl
    | 5 => r 5 rfl
    | 6 => r 6 rfl
    | 7 => r 7 rfl
    | 8 => r 8 rfl
  second i := match i with
    | 0 => r 9 rfl
    | 1 => r 10 rfl
    | 2 => r 11 rfl
    | 3 => ⟨12, rfl⟩
    | 4 => r 13 rfl
    | 5 => r 14 rfl
    | 6 => r 8 rfl
    | 7 => r 7 rfl
    | 8 => r 15 rfl
  inputs := pair (r 6 rfl) (r 7 rfl)
  route := pair .head (.tail .head)

private def rank : DemandRank 16 2 :=
  [.phase (fun i => if 9 ≤ i.val then 1 else 0),
   .phase (fun i => match i.val with
      | 8 | 15 => 3 | 5 | 14 => 2 | 4 | 13 => 1 | _ => 0),
   .counter 0, .counter 1,
   .phase (fun i => match i.val with | 2 | 3 | 11 | 12 => 2 | 0 | 9 => 1 | _ => 0)]

private def roles : Closed.Automatic.Roles Op := ⟨.zero, .succ, .not⟩
private theorem laws : roles.Laws model := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

private structure Linked where
  first : Closed.Automatic.Recovered (stage false) roles
  second : Closed.Automatic.Recovered (stage true) roles
  accepted : Accepted graph first.certificate second.certificate

private def linked (d : Layout graph (stage false) (stage true)) : Option Linked := do
  let first ← Closed.Automatic.extract (stage false) roles
  let second ← Closed.Automatic.extract (stage true) roles
  let accepted ← check graph first.certificate second.certificate d rank
  return ⟨first, second, accepted⟩

private def input (limit : Nat) : Tuple model.Value inputs := pair ⟨limit⟩ ⟨10⟩

private def run (fuel₁ fuel₂ limit : Nat) : Option (List Nat) := do
  let a ← linked layout
  let .cons x (.cons y (.cons z (.cons w .nil))) ← a.accepted.runFuel model fuel₁ fuel₂ (input limit)
  return [x.down, y.down, z.down, w.down]

private def runFirst : Option (List Nat) := do
  let a ← linked layout
  let .cons x (.cons y (.cons z (.cons w .nil))) ← a.first.certificate.runFuel model 2 (input 2)
  return [x.down, y.down, z.down, w.down]

#guard runFirst == some [3, 10, 2, 3]
#guard rank.check graph
#guard run 2 3 2 == some [13, 3, 3, 13]
#guard (run 1 3 2).isNone
#guard (run 2 2 2).isNone
#guard run 1 2 1 == some [12, 2, 2, 12]
-- Both arguments are counts, so a type-only check would allow this swap.
#guard (linked { layout with route := pair (.tail .head) .head }).isNone

private def certifiedRun :
    Option {a : Linked //
      Exec model a.accepted.revert (input 2) (some (four ⟨13⟩ ⟨3⟩ ⟨3⟩ ⟨13⟩)) ∧
      ∀ idx, ∃ mid, a.accepted.Observations model
        (graph.denote model (input 2) a.accepted.demandWellFounded) idx mid (four ⟨13⟩ ⟨3⟩ ⟨3⟩ ⟨13⟩)} := do
  let a ← linked layout
  match result : a.accepted.runFuel model 2 3 (input 2) with
  | some (.cons ⟨13⟩ (.cons ⟨3⟩ (.cons ⟨3⟩ (.cons ⟨13⟩ .nil)))) =>
    have ran := a.accepted.exec_of_runFuel 2 3 (input 2) result
    return ⟨a, ran, fun idx => a.accepted.observations_of_exec
      (a.first.laws laws) (a.second.laws laws) (input 2) idx ran⟩
  | _ => none

#guard certifiedRun.isSome

end Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Tests
