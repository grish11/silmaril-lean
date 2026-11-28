module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Thms
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort dataPorts)
open GVN.Cyclic (classesOf classesOf_eq_iff classesOf_preserves_key)
open GVN.Cyclic.Activation (inputSlot)
open GVN.Cyclic.Builder (argumentPorts)
open GVN.Cyclic.TwoBackedges (Keys WordSlot)
open GVN.Cyclic.FixedPoint (Refines classCount classCount_le_vertices classCount_lt_of_split)
open GVN.Cyclic.TwoBackedges.Family (Equation Holds entryMatches feedbackMatches seed seed_interprets seed_matches)
open GVN.Cyclic.TwoBackedges.Family.Discovery
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)
open Silmaril.SSA.RVSDG (Port)

open scoped GVN.Cyclic.TwoBackedges.Family.Discovery Pure.WordNormalize

variable {regs : List (ValueSort Unit)}

private theorem mem_slots (port : WordSlot regs) : port ∈ slots regs := by
  induction regs with
  | nil => cases port
  | cons sort tail ih =>
    cases sort with
    | predicate =>
      have listed : slots (.predicate :: tail) = (slots tail).map Port.tail := by
        simp [slots, argumentPorts, List.map_map, inputSlot]
      rw [listed]
      cases port with
      | tail prior => exact List.mem_map.mpr ⟨prior, ih prior, rfl⟩
    | data tag =>
      cases tag
      have listed : slots (.data () :: tail) = .head :: (slots tail).map Port.tail := by
        simp [slots, argumentPorts, List.map_map, inputSlot]
      rw [listed]
      cases port with
      | head => exact List.mem_cons_self ..
      | tail prior => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨prior, ih prior, rfl⟩)

theorem slot_surjective (port : WordSlot regs) : ∃ i : Lane regs, slot i = port :=
  List.mem_iff_get.mp (mem_slots port)

private theorem get_ofFn {A : Type} {n : Nat} (f : Fin n → A) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  cases i
  simp [Vector.get, Fin.cast]

theorem initial_eq (p : Program Opcode regs word) (i j : Lane regs) :
    initial p i = initial p j ↔ entryKey p i = entryKey p j := by
  simp only [initial, get_ofFn, classesOf_eq_iff]

theorem refine_eq (p : Program Opcode regs word) (classes : Classes regs) (i j : Lane regs) :
    refine p classes i = refine p classes j ↔
      classes i = classes j ∧ feedbackKeys p classes i = feedbackKeys p classes j := by
  simp only [refine, get_ofFn, classesOf_eq_iff, Prod.mk.injEq, feedbackKeys]

theorem check_stable (p : Program Opcode regs word) (classes : Classes regs) :
    checkStable p classes = true ↔ Stable p classes := by
  constructor
  · intro checked i j same
    have row := List.all_eq_true.mp checked i (List.mem_finRange i)
    have accepted := List.all_eq_true.mp row j (List.mem_finRange j)
    simpa [same, feedbackKeys] using accepted
  · intro stable
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    by_cases same : classes i = classes j
    · simpa [same, feedbackKeys] using stable i j same
    · simp [same]

theorem refine_refines (p : Program Opcode regs word) (classes : Classes regs) :
    Refines (refine p classes) classes :=
  fun i j same => ((refine_eq p classes i j).mp same).1

theorem refine_count (p : Program Opcode regs word) (classes : Classes regs)
    (unstable : ¬ Stable p classes) : classCount classes < classCount (refine p classes) := by
  by_contra notGrowing
  apply unstable
  intro i j same
  by_contra disagree
  have split : refine p classes i ≠ refine p classes j :=
    fun refined => disagree ((refine_eq p classes i j).mp refined).2
  exact notGrowing (classCount_lt_of_split (refine_refines p classes) same split)

theorem run_refines (p : Program Opcode regs word) (fuel : Nat) (classes : Classes regs) :
    Refines (run p fuel classes) classes := by
  induction fuel generalizing classes with
  | zero => exact fun _ _ same => same
  | succ fuel ih =>
    rw [run]
    split
    · exact fun _ _ same => same
    · exact fun i j same => refine_refines p classes i j (ih _ i j same)

theorem run_stable (p : Program Opcode regs word) (fuel : Nat) (classes : Classes regs)
    (enough : (slots regs).length - classCount classes ≤ fuel) : Stable p (run p fuel classes) := by
  induction fuel generalizing classes with
  | zero =>
    change Stable p classes
    by_contra unstable
    have growing := refine_count p classes unstable
    have bound := classCount_le_vertices (refine p classes)
    omega
  | succ fuel ih =>
    rw [run]
    split
    · exact (check_stable p classes).mp ‹_›
    · have unstable := mt (check_stable p classes).mpr ‹¬ checkStable p classes = true›
      have growing := refine_count p classes unstable
      exact ih (refine p classes) (by omega)

private theorem equation_of_mem (classes : Classes regs) {eq : Equation regs}
    (mem : eq ∈ equations classes) : ∃ i, eq = ⟨slot (classesOf classes.labels.get i), slot i⟩ := by
  obtain ⟨i, _, found⟩ := List.mem_filterMap.mp mem
  dsimp only at found
  rw [get_ofFn] at found
  split at found
  · contradiction
  · exact ⟨i, (Option.some.inj found).symm⟩

private theorem matches_of_eq {args : List (Diamond.Ty Unit)} {lhs rhs : GVN.WordNumber.Key args} (same : lhs = rhs) :
    lhs.matches rhs = true :=
  same ▸ lhs.matches_self

theorem equations_entry (p : Program Opcode regs word) (classes : Classes regs)
    (related : Refines classes (initial p)) : entryMatches p (equations classes) = true := by
  apply List.all_eq_true.mpr
  intro eq mem
  obtain ⟨i, rfl⟩ := equation_of_mem classes mem
  exact matches_of_eq ((initial_eq p _ _).mp (related _ _ (classesOf_preserves_key classes.labels.get i)))

theorem equations_feedback (p : Program Opcode regs word) (classes : Classes regs)
    (stable : Stable p classes) (side : Bool) : feedbackMatches p (equations classes) side = true := by
  apply List.all_eq_true.mpr
  intro eq mem
  obtain ⟨i, rfl⟩ := equation_of_mem classes mem
  have paired := stable _ _ (classesOf_preserves_key classes.labels.get i)
  simp only [feedbackKeys, feedbackTable, get_ofFn] at paired
  cases side
  · exact matches_of_eq (congrArg Prod.snd paired)
  · exact matches_of_eq (congrArg Prod.fst paired)

private theorem member_read {A : Type*} (classes : Classes regs) (i : Lane regs)
    (read : WordSlot regs → A)
    (holds : ∀ eq ∈ equations classes, read eq.representative = read eq.member) :
    read (slot (classesOf classes.labels.get i)) = read (slot i) := by
  by_cases own : classesOf classes.labels.get i = i
  · rw [own]
  · apply holds ⟨slot (classesOf classes.labels.get i), slot i⟩
    refine List.mem_filterMap.mpr ⟨i, List.mem_finRange _, ?_⟩
    dsimp only
    rw [get_ofFn, ite_eq_right own]

private theorem class_reads {A : Type*} (classes : Classes regs) {i j : Lane regs}
    (read : WordSlot regs → A)
    (holds : ∀ eq ∈ equations classes, read eq.representative = read eq.member)
    (same : classes i = classes j) : read (slot i) = read (slot j) := by
  have representative := (classesOf_eq_iff classes.labels.get i j).mpr same
  exact (member_read classes i read holds).symm.trans
    ((congrArg (fun lane => read (slot lane)) representative).trans (member_read classes j read holds))

theorem class_values (classes : Classes regs) {i j : Lane regs}
    (bank : Bank (regs := regs) model) (holds : Holds (equations classes) bank)
    (same : classes i = classes j) : bank.get (slot i) = bank.get (slot j) :=
  class_reads classes (fun port => bank.get port) holds same

private theorem seed_coarsens {fine coarse : Classes regs} (related : Refines fine coarse) :
    ∀ port : WordSlot regs, ((seed (equations fine)).get port).substitute
      (fun arg => (seed (equations coarse)).get arg) = (seed (equations coarse)).get port := by
  let values := fun port : WordSlot regs => (seed (equations coarse)).get port
  refine seed_interprets (equations fine) (GVN.WordNumber.Key.substitute values) values (fun _ => rfl) ?_
  intro eq mem
  obtain ⟨i, rfl⟩ := equation_of_mem fine mem
  exact class_reads coarse values
    (fun equation found => GVN.WordNumber.Key.eq_of_matches (List.all_eq_true.mp (seed_matches _) equation found))
    (related _ _ (classesOf_preserves_key fine.labels.get i))

theorem feedback_coarsens (p : Program Opcode regs word) {fine coarse : Classes regs}
    (related : Refines fine coarse) (i : Lane regs) :
    let rename := GVN.WordNumber.Key.substitute (fun arg => (seed (equations coarse)).get arg)
    Prod.map rename rename (feedbackKeys p fine i) = feedbackKeys p coarse i := by
  let arguments := fun port : WordSlot regs => (seed (equations coarse)).get port
  have header := Keys.substitute_block p.header arguments (seed_coarsens related)
  have branch (side : Bool) := Keys.substitute_block (p.feedback side) arguments header (slot i)
  simp only [feedbackKeys, feedbackTable, get_ofFn, Prod.map]
  exact congrArg₂ Prod.mk (branch true) (branch false)

theorem refine_monotone (p : Program Opcode regs word) {fine coarse : Classes regs}
    (related : Refines fine coarse) : Refines (refine p fine) (refine p coarse) := by
  intro i j same
  obtain ⟨prior, feedback⟩ := (refine_eq p fine i j).mp same
  refine (refine_eq p coarse i j).mpr ⟨related i j prior, ?_⟩
  rw [← feedback_coarsens p related i, ← feedback_coarsens p related j, feedback]

theorem stable_refines_round (p : Program Opcode regs word) {fine coarse : Classes regs}
    (stable : Stable p fine) (related : Refines fine coarse) : Refines fine (refine p coarse) :=
  fun i j same => refine_monotone p related i j ((refine_eq p fine i j).mpr ⟨same, stable i j same⟩)

theorem stable_refines_run (p : Program Opcode regs word) {fine : Classes regs}
    (stable : Stable p fine) (fuel : Nat) (classes : Classes regs)
    (related : Refines fine classes) : Refines fine (run p fuel classes) := by
  induction fuel generalizing classes with
  | zero => exact related
  | succ fuel ih =>
    rw [run]
    split
    · exact related
    · exact ih _ (stable_refines_round p stable related)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery
