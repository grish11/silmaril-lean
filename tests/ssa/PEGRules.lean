module

import Silmaril.SSA.PEG.Rules.Thms

namespace Silmaril.SSA.PEG.Rules.Tests

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | one : Op [] .count
  | bottomCount : Op [] .count
  | done : Op [] .bool
  | more : Op [] .bool
  | bottomFlag : Op [] .bool
  | succ : Op [.count] .count

private def model : Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, _ => some ⟨0⟩
    | .one, _ => some ⟨1⟩
    | .bottomCount, _ => none
    | .done, _ => some ⟨true⟩
    | .more, _ => some ⟨false⟩
    | .bottomFlag, _ => none
    | .succ, args => some ⟨(args.get .head).down + 1⟩

/-- The frozen stream samples a genuinely varying theta. The self-feedback row uses that
stream as its initializer. The later rows test bottom and the pass shift rule. -/
private def raw : RawGraph Op [] [.count, .count, .count, .count] 17 1 where
  forest := ⟨fun _ => none⟩
  sort i := match i with
    | 5 | 9 | 10 | 11 | 15 => .bool
    | _ => .count
  node i := match i with
    | 0 => ⟨_, .op .zero, []⟩
    | 1 => ⟨_, .op .one, []⟩
    | 2 => ⟨_, .theta 0, [0, 1]⟩
    | 3 => ⟨_, .eval 0, [2, 0]⟩
    | 4 => ⟨_, .theta 0, [3, 4]⟩
    | 5 => ⟨_, .op .bottomFlag, []⟩
    | 6 => ⟨_, .phi, [5, 1, 1]⟩
    | 7 => ⟨_, .op .bottomCount, []⟩
    | 8 => ⟨_, .eval 0, [1, 7]⟩
    | 9 => ⟨_, .op .done, []⟩
    | 10 => ⟨_, .op .more, []⟩
    | 11 => ⟨_, .theta 0, [10, 9]⟩
    | 12 => ⟨_, .pass 0, [11]⟩
    | 13 => ⟨_, .pass 0, [9]⟩
    | 14 => ⟨_, .op .succ, [13]⟩
    | 15 => ⟨_, .eval 0, [11, 0]⟩
    | _ => ⟨_, .phi, [15, 0, 14]⟩
  roots := [4, 6, 8, 12]

private def graph : Graph Op [] [.count, .count, .count, .count] 17 1 :=
  raw.check.get (by decide)

private def rank : DemandRank 17 1 := [.phase Fin.val, .counter 0]
private theorem wf : WellFounded graph.Demand := graph.demandWellFounded_of_check rank (by decide)
private noncomputable def values : graph.Valuation model := graph.denote model .nil wf
private theorem solves : graph.Solves model .nil values := graph.denote_solves model .nil wf

private def zero : Ref graph.sort .count := ⟨0, rfl⟩
private def one : Ref graph.sort .count := ⟨1, rfl⟩
private def varying : Ref graph.sort .count := ⟨2, rfl⟩
private def frozen : Ref graph.sort .count := ⟨3, rfl⟩
private def carry : Ref graph.sort .count := ⟨4, rfl⟩
private def bottomFlag : Ref graph.sort .bool := ⟨5, rfl⟩
private def branch : Ref graph.sort .count := ⟨6, rfl⟩
private def bottomCount : Ref graph.sort .count := ⟨7, rfl⟩
private def sampled : Ref graph.sort .count := ⟨8, rfl⟩
private def done : Ref graph.sort .bool := ⟨9, rfl⟩
private def more : Ref graph.sort .bool := ⟨10, rfl⟩
private def delayed : Ref graph.sort .bool := ⟨11, rfl⟩
private def delayedPass : Ref graph.sort .count := ⟨12, rfl⟩
private def donePass : Ref graph.sort .count := ⟨13, rfl⟩
private def shiftedPass : Ref graph.sort .count := ⟨14, rfl⟩
private def firstSample : Ref graph.sort .bool := ⟨15, rfl⟩
private def peeledPass : Ref graph.sort .count := ⟨16, rfl⟩

private theorem zeroValue (i : Index 1) : readRef values zero i = some ⟨0⟩ :=
  at_label solves (show HasNode zero (.op Op.zero) .nil from HEq.rfl) i

private theorem oneValue (i : Index 1) : readRef values one i = some ⟨1⟩ :=
  at_label solves (show HasNode one (.op Op.one) .nil from HEq.rfl) i

private theorem doneValue (i : Index 1) : readRef values done i = some ⟨true⟩ :=
  at_label solves (show HasNode done (.op Op.done) .nil from HEq.rfl) i

private theorem moreValue (i : Index 1) : readRef values more i = some ⟨false⟩ :=
  at_label solves (show HasNode more (.op Op.more) .nil from HEq.rfl) i

private theorem bottomFlagValue (i : Index 1) : readRef values bottomFlag i = none :=
  at_label solves (show HasNode bottomFlag (.op Op.bottomFlag) .nil from HEq.rfl) i

private theorem bottomCountValue (i : Index 1) : readRef values bottomCount i = none :=
  at_label solves (show HasNode bottomCount (.op Op.bottomCount) .nil from HEq.rfl) i

private theorem frozenInvariant : InvariantAt graph 0 frozen.id := by
  refine invariantAt_largest (fun v => v = 0 ∨ v = 3) ?_ ?_ (.inr rfl)
  · rintro v (rfl | rfl) <;> decide
  · rintro a b kind ⟨⟨slot, rfl, rfl⟩, notSample⟩ (rfl | rfl)
    · exact slot.elim0
    · have countEdge : ∀ s : Fin 2, (graph.node 3).label.kind s ≠ .sample 0 →
          ((graph.node 3).arg s).id = 0 := by
        intro s
        refine Fin.cases (fun notSample => (notSample rfl).elim) (fun t => ?_) s
        have ht : t = 0 := Subsingleton.elim _ _
        subst t
        intro _
        rfl
      exact .inl (countEdge slot notSample)

example : ¬ InvariantAt graph 0 varying.id := fun guard => invariantAt_notTheta guard rfl

private theorem carryEqualsFrozen : StreamEq values carry frozen :=
  theta_self solves (show HasNode carry (.theta 0) (.cons frozen (.cons carry .nil)) from HEq.rfl)
    (fun _ => rfl) (denote_invariant wf (env := .nil) frozenInvariant)

-- This is the same-sort vertex stream equality required by an E-PEG merge receipt.
example : graph.sort carry.id = graph.sort frozen.id ∧
    ∀ i, HEq (values (carry.id, i)) (values (frozen.id, i)) :=
  (streamEq_iff_vertex carry frozen).1 carryEqualsFrozen

example (i : Index 1) : readRef values carry i = some ⟨0⟩ :=
  (carryEqualsFrozen i).trans ((eval_zero solves
    (show HasNode frozen (.eval 0) (.cons varying (.cons zero .nil)) from HEq.rfl) (zeroValue i)).trans
    ((theta_zero solves (show HasNode varying (.theta 0) (.cons zero (.cons one .nil)) from HEq.rfl)
      (by simp [Index.set])).trans (zeroValue (i.set 0 0))))

private theorem passShift : StreamEq values delayedPass shiftedPass :=
  pass_theta_false_succ solves
    (show HasNode delayedPass (.pass 0) (.cons delayed .nil) from HEq.rfl)
    (show HasNode delayed (.theta 0) (.cons more (.cons done .nil)) from HEq.rfl)
    (show HasNode donePass (.pass 0) (.cons done .nil) from HEq.rfl)
    (show HasNode shiftedPass (.op Op.succ) (.cons donePass .nil) from HEq.rfl)
    (fun i => moreValue (i.set 0 0)) (fun _ => rfl)

example : StreamEq values delayedPass peeledPass := by
  apply pass_peel_phi solves
    (show HasNode delayedPass (.pass 0) (.cons delayed .nil) from HEq.rfl)
    (show HasNode donePass (.pass 0) (.cons done .nil) from HEq.rfl)
    (show HasNode firstSample (.eval 0) (.cons delayed (.cons zero .nil)) from HEq.rfl)
    (show HasNode shiftedPass (.op Op.succ) (.cons donePass .nil) from HEq.rfl)
    (show HasNode peeledPass .phi (.cons firstSample (.cons zero (.cons shiftedPass .nil))) from HEq.rfl)
    zeroValue (fun _ => rfl)
  intro i k
  have reset : (i.set 0 (k + 1)).set 0 k = i.set 0 k := by
    funext j
    by_cases h : j = 0 <;> simp [Index.set, h]
  rw [theta_succ solves (show HasNode delayed (.theta 0) (.cons more (.cons done .nil)) from HEq.rfl)
    (i := i.set 0 (k + 1)) (k := k) (by simp [Index.set]), reset]

example (i : Index 1) : readRef values delayedPass i = some ⟨1⟩ := by
  have atZero := pass_zero solves (show HasNode donePass (.pass 0) (.cons done .nil) from HEq.rfl)
    (doneValue (i.set 0 0))
  rw [passShift i, unary_at solves
    (show HasNode shiftedPass (.op Op.succ) (.cons donePass .nil) from HEq.rfl) i, atZero]
  rfl

-- Equal branches cannot remove a bottom guard.
example : ¬ StreamEq values branch one := by
  intro equal
  let i : Index 1 := fun _ => 0
  have bad := equal i
  rw [phi_at solves (show HasNode branch .phi (.cons bottomFlag (.cons one (.cons one .nil))) from HEq.rfl) i,
    bottomFlagValue i, oneValue i] at bad
  cases bad

-- The source is invariant, but a bottom count still makes eval bottom.
example : Invariant values 0 one ∧ ¬ StreamEq values sampled one := by
  refine ⟨fun i j _ => (oneValue i).trans (oneValue j).symm, ?_⟩
  intro equal
  let i : Index 1 := fun _ => 0
  have bad := equal i
  rw [eval_at solves (show HasNode sampled (.eval 0) (.cons one (.cons bottomCount .nil)) from HEq.rfl) i,
    bottomCountValue i, oneValue i] at bad
  cases bad

end Silmaril.SSA.PEG.Rules.Tests
