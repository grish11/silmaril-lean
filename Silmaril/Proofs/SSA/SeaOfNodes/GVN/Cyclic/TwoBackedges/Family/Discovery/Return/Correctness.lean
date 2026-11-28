module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort dataPorts)
open GVN.Cyclic.Activation (inputSlot)
open GVN.Cyclic.Builder (argumentPorts origin_eq)
open GVN.Cyclic.TwoBackedges (WordSlot redirect)
open GVN.Cyclic.TwoBackedges.Family (exitMatches headerKeys)
open GVN.Cyclic.TwoBackedges.Family.Discovery
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return
open Pure.SubZero (word wordPort)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open Silmaril.SSA.RVSDG (Address Origin Port)

open scoped Pure.WordNormalize

variable {regs : List (ValueSort Unit)}

private theorem slots_ordered (regs : List (ValueSort Unit)) :
    (slots regs).Pairwise (fun first second => first.index < second.index) := by
  induction regs with
  | nil => exact .nil
  | cons sort tail ih =>
    cases sort with
    | predicate =>
      have listed : slots (.predicate :: tail) = (slots tail).map Port.tail := by
        simp [slots, argumentPorts, List.map_map, inputSlot]
      rw [listed, List.pairwise_map]
      exact ih.imp (fun before => Nat.succ_lt_succ before)
    | data tag =>
      cases tag
      have listed : slots (.data () :: tail) = .head :: (slots tail).map Port.tail := by
        simp [slots, argumentPorts, List.map_map, inputSlot]
      rw [listed, List.pairwise_cons, List.pairwise_map]
      refine ⟨?_, ih.imp (fun before => Nat.succ_lt_succ before)⟩
      intro port mem
      obtain ⟨prior, _, rfl⟩ := List.mem_map.mp mem
      exact Nat.zero_lt_succ prior.index

theorem slot_index_order : StrictMono (fun i : Lane regs => (slot i).index) :=
  fun ⦃i j⦄ earlier => List.Pairwise.rel_getElem_of_lt i.isLt j.isLt (slots_ordered regs) earlier

private theorem slot_injective : Function.Injective (@slot regs) :=
  fun _ _ same => slot_index_order.injective (congrArg Port.index same)

variable (p : Program Opcode regs word)

theorem returned_none : returnedLane? p = none ↔ returnOrigin p ≠ .arg p.result := by
  by_cases same : (returnOrigin p).address = .arg p.result.index
  · have origin := origin_eq (returnOrigin p) (.arg p.result) same
    obtain ⟨i, actual⟩ := slot_surjective p.result
    constructor
    · intro absent
      have missing := List.find?_eq_none.mp (by simpa only [returnedLane?, ite_eq_left same] using absent)
      exact (missing i (List.mem_finRange i) (by simp [actual])).elim
    · exact fun differs => (differs origin).elim
  · have differs : returnOrigin p ≠ .arg p.result := fun eq => same (congrArg Origin.address eq)
    simp [returnedLane?, same, differs]

theorem returned_some {original : Lane regs} (found : returnedLane? p = some original) :
    slot original = p.result ∧ returnOrigin p = .arg (slot original) := by
  unfold returnedLane? at found
  split at found
  · rename_i originAddress
    have indexEq : (slot original).index = p.result.index :=
      of_decide_eq_true (List.find?_some (p := fun i => decide ((slot i).index = p.result.index)) found)
    have sourceEq := Origin.arg.inj (origin_eq (Origin.arg (past := []) (slot original)) (.arg p.result)
      (congrArg Address.arg indexEq))
    refine ⟨sourceEq, ?_⟩
    rw [sourceEq]
    exact origin_eq (returnOrigin p) (.arg p.result) originAddress
  · contradiction

theorem returned_reads {original : Lane regs} (found : returnedLane? p = some original)
    (old : Bank (regs := regs) model) :
    (p.header.eval model old).get p.result = old.get (slot original) := by
  let transfer := Quads.CFG.compileBlock p.header (Quads.initial regs)
  have read := Quads.CFG.compileBlock_read (past := []) p.header model old PUnit.unit (Quads.initial regs)
  rw [Quads.read_initial_tuple] at read
  change transfer.outgoing.read old (transfer.flow.eval model old PUnit.unit) =
    p.header.eval model old at read
  rw [← read, Quads.read_get]
  change Diamond.read model (returnOrigin p) old (transfer.flow.eval model old PUnit.unit) = _
  rw [(returned_some p found).2]
  rfl

theorem best_spec (classes : Classes regs) {original : Lane regs} (actual : slot original = p.result) :
    Eligible p classes original (best p classes original) ∧
      ∀ candidate, Eligible p classes original candidate → best p classes original ≤ candidate := by
  let keys := headerKeys p (equations classes)
  let test := fun candidate : Lane regs =>
    decide (classes original = classes candidate) && (keys.get p.result).matches (keys.get (slot candidate))
  have tested (candidate : Lane regs) : test candidate = true ↔ Eligible p classes original candidate := by
    simp only [test, keys, Eligible, exitMatches, Bool.and_eq_true, decide_eq_true_eq]
  have originalTest : test original = true := (tested original).mpr ⟨rfl, by
    rw [actual]
    exact GVN.WordNumber.Key.matches_self _⟩
  cases found : (List.finRange (slots regs).length).find? test with
  | none => exact (List.find?_eq_none.mp found original (List.mem_finRange original) originalTest).elim
  | some candidate =>
    have chosen : best p classes original = candidate := by
      change ((List.finRange (slots regs).length).find? test).getD original = candidate
      rw [found, Option.getD_some]
    have first := (List.find?_ofFn_eq_some_of_injective (f := fun (i : Lane regs) => i)
      Function.injective_id).mp found
    rw [chosen]
    exact ⟨(tested candidate).mp first.1, fun other eligible =>
      le_of_not_gt (fun earlier => first.2 other earlier ((tested other).mpr eligible))⟩

theorem best_rewrite {original : Lane regs} (found : returnedLane? p = some original) :
    GVN.Cyclic.TwoBackedges.Family.Discovery.rewrite? p (slot (best p (normalize p) original)) =
      some (redirect p (slot (best p (normalize p) original))) := by
  have fits := (best_spec p (normalize p) (returned_some p found).1).1.2
  exact GVN.Cyclic.TwoBackedges.Family.rewrite?_eq_some_iff.mpr
    ⟨(GVN.Cyclic.TwoBackedges.Family.Discovery.certify?_isSome_iff p _).mpr fits, rfl⟩

theorem optimize_carried {original : Lane regs} (found : returnedLane? p = some original) :
    optimize p = redirect p (slot (best p (normalize p) original)) := by
  simp only [optimize, found]
  split
  · rename_i same
    rw [same, (returned_some p found).1]
    cases p
    rfl
  · change (GVN.Cyclic.TwoBackedges.Family.Discovery.rewrite? p (slot (best p (normalize p) original))).getD p = _
    rw [best_rewrite p found, Option.getD_some]

theorem optimize_canonical {original : Lane regs} (found : returnedLane? p = some original) :
    optimize p = p ↔ ∀ candidate, Eligible p (normalize p) original candidate → original ≤ candidate := by
  have actual := (returned_some p found).1
  have chosen := best_spec p (normalize p) actual
  rw [optimize_carried p found]
  constructor
  · intro unchanged candidate fits
    have same : slot (best p (normalize p) original) = p.result := congrArg Program.result unchanged
    have laneEq := slot_injective (same.trans actual.symm)
    simpa [laneEq] using chosen.2 candidate fits
  · intro least
    have equal := le_antisymm (chosen.2 original ⟨rfl, by rw [actual]; exact GVN.WordNumber.Key.matches_self _⟩)
      (least _ chosen.1)
    rw [equal, actual]
    cases p
    rfl

theorem optimize_step {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : (optimize p).step model old = p.step model old := by
  cases found : returnedLane? p with
  | none => simp [optimize, found]
  | some original =>
    rw [optimize_carried p found]
    exact rewrite_step_of_arrives p (best_rewrite p found) arrived

private theorem optimize_entry : (optimize p).preheader = p.preheader := by
  cases found : returnedLane? p with
  | none => simp [optimize, found]
  | some original => rw [optimize_carried p found]; rfl

theorem optimize_arrives (input old : Bank (regs := regs) model) (via : Incoming) (count : Nat) :
    (optimize p).Arrives model input via count old ↔ p.Arrives model input via count old := by
  constructor
  · intro h
    induction h with
    | entry => rw [optimize_entry p]; exact .entry
    | feedback _ taken prior =>
      rw [optimize_step p prior] at taken
      exact .feedback prior taken
  · intro h
    induction h with
    | entry => rw [← optimize_entry p]; exact .entry
    | feedback original taken prior =>
      exact .feedback prior ((optimize_step p original).trans taken)

theorem optimize_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (optimize p).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  cases found : returnedLane? p with
  | none => simp [optimize, found]
  | some original => rw [optimize_carried p found]; exact rewrite_run_eq p (best_rewrite p found) fuel input

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return
