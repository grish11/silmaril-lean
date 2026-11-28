module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Correctness
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery

open Diamond (ValueSort)
open FixedPoint (Refines classCount)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open TwoBackedges (WordSlot)

variable {regs : List (ValueSort Unit)}
variable (p : Program Opcode regs word)

theorem slot_surjective (port : WordSlot regs) : ∃ i : Lane regs, slot i = port :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.slot_surjective port

theorem initial_eq_iff (i j : Lane regs) :
    initial p i = initial p j ↔ entryKey p i = entryKey p j :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.initial_eq p i j

theorem refine_eq_iff (classes : Classes regs) (i j : Lane regs) :
    refine p classes i = refine p classes j ↔
      classes i = classes j ∧ feedbackKeys p classes i = feedbackKeys p classes j :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.refine_eq p classes i j

theorem checkStable_eq_true_iff (classes : Classes regs) :
    checkStable p classes = true ↔ Stable p classes :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.check_stable p classes

theorem refine_no_merges (classes : Classes regs) : Refines (refine p classes) classes :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.refine_refines p classes

theorem refine_classCount_lt (classes : Classes regs) (unstable : ¬ Stable p classes) :
    classCount classes < classCount (refine p classes) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.refine_count p classes unstable

theorem run_no_merges (fuel : Nat) (classes : Classes regs) :
    Refines (run p fuel classes) classes :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.run_refines p fuel classes

/-- One round per possible additional class suffices. -/
theorem run_stable_of_fuel (fuel : Nat) (classes : Classes regs)
    (enough : (slots regs).length - classCount classes ≤ fuel) : Stable p (run p fuel classes) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.run_stable p fuel classes enough

theorem normalize_stable : Stable p (normalize p) ∧ Refines (normalize p) (initial p) :=
  ⟨run_stable_of_fuel p _ _ (Nat.sub_le ..), run_no_merges p _ _⟩

theorem normalize_fixed (i j : Lane regs) :
    refine p (normalize p) i = refine p (normalize p) j ↔ normalize p i = normalize p j :=
  (refine_eq_iff p _ i j).trans ⟨And.left, fun same => ⟨same, (normalize_stable p).1 i j same⟩⟩

/-- The coarse seed replaces the argument leaves of the fine key.
This uses the actual seed and independently preserves both feedback occurrences. -/
theorem feedbackKeys_coarsen {fine coarse : Classes regs} (related : Refines fine coarse) (i : Lane regs) :
    let rename := WordNumber.Key.substitute (fun arg => (Family.seed (equations coarse)).get arg)
    Prod.map rename rename (feedbackKeys p fine i) = feedbackKeys p coarse i :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.feedback_coarsens p related i

theorem refine_monotone {fine coarse : Classes regs} (related : Refines fine coarse) :
    Refines (refine p fine) (refine p coarse) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.refine_monotone p related

theorem stable_refines_round {fine coarse : Classes regs} (stable : Stable p fine)
    (related : Refines fine coarse) : Refines fine (refine p coarse) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.stable_refines_round p stable related

/-- Every stable refinement of the starting partition refines every executable run prefix. -/
theorem stable_refines_run {fine : Classes regs} (stable : Stable p fine) (fuel : Nat)
    (classes : Classes regs) (related : Refines fine classes) : Refines fine (run p fuel classes) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.stable_refines_run p stable fuel classes related

/-- Together with `normalize_stable`, this characterizes the coarsest stable
refinement of the structural entry classes, up to the same-class relation. -/
theorem normalize_coarsest {fine : Classes regs} (stable : Stable p fine)
    (entry : Refines fine (initial p)) : Refines fine (normalize p) :=
  stable_refines_run p stable _ _ entry

/-- The discovered equations pass the existing entry and both feedback
checks. Admission of a proposed return redirect only depends on its exit key. -/
theorem certify?_isSome_iff (replacement : WordSlot regs) :
    (certify? p replacement).isSome = true ↔ Family.exitMatches p (discover p) replacement = true := by
  rw [certify?, Family.certify?_isSome_iff]
  have stable := normalize_stable p
  simp only [discover, Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.equations_entry p _ stable.2,
    Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.equations_feedback p _ stable.1, true_and]

/-- Request a native invariant certificate with no return redirection. -/
theorem certify?_original_isSome : (certify? p p.result).isSome = true :=
  (certify?_isSome_iff p p.result).mpr (WordNumber.Key.matches_self _)

theorem same_class_at_arrival {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) {i j : Lane regs} (same : normalize p i = normalize p j) :
    old.get (slot i) = old.get (slot j) := by
  let cert := (certify? p p.result).get (certify?_original_isSome p)
  exact Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.class_values
    (normalize p) old (cert.arrives arrived) same

theorem rewrite_step_of_arrives {replacement : WordSlot regs} {target : Program Opcode regs word}
    (accepted : rewrite? p replacement = some target)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : target.step model old = p.step model old :=
  Family.rewrite_step_of_arrives accepted arrived

theorem rewrite_run_eq {replacement : WordSlot regs} {target : Program Opcode regs word}
    (accepted : rewrite? p replacement = some target) (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  Family.rewrite_run_eq accepted fuel input

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery
