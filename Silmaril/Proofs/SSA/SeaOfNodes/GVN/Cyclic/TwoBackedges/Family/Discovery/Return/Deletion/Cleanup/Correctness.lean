module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup

open Silmaril.SSA.SeaOfNodes
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup
open Diamond (ValueSort)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)

variable {regs : List (ValueSort Unit)}
variable {p next : Program Opcode regs word}

theorem first_some {index : Nat} :
    first? p = some index ↔
      index < p.header.length ∧ check p index = true ∧ ∀ j < index, check p j = false := by
  simp only [first?, List.find?_eq_some_iff_getElem, List.getElem_range, List.length_range]
  constructor
  · rintro ⟨checked, i, inRange, rfl, prior⟩
    exact ⟨inRange, checked, fun j before => by simpa using prior j before⟩
  · rintro ⟨inRange, checked, prior⟩
    exact ⟨checked, index, inRange, rfl, fun j before => by simpa using prior j before⟩

theorem step_none :
    step? p = none ↔ ∀ index < p.header.length, check p index = false := by
  simp only [step?, Option.map_eq_none_iff, first?, List.find?_eq_none, List.mem_range, Bool.not_eq_true]

theorem step_checked (found : step? p = some next) : ∃ index, first? p = some index ∧
    delete? p index = some next := by
  cases picked : first? p with
  | none => simp [step?, picked] at found
  | some index =>
    have exactNext : erase p index = next := by simpa only [step?, picked, Option.map_some, Option.some.injEq] using found
    exact ⟨index, rfl, delete?_eq_some_iff.mpr ⟨(first_some.mp picked).2.1, exactNext.symm⟩⟩

theorem step_shorter (found : step? p = some next) : next.header.length + 1 = p.header.length :=
  let ⟨_, _, checked⟩ := step_checked found
  delete?_shorter checked

theorem run_stops (fuel : Nat) (p : Program Opcode regs word) (enough : p.header.length ≤ fuel) :
    step? (run fuel p) = none := by
  induction fuel generalizing p with
  | zero =>
    have empty : p.header.length = 0 := Nat.eq_zero_of_le_zero enough
    apply step_none.mpr
    intro index bound
    change index < p.header.length at bound
    rw [empty] at bound
    exact (Nat.not_lt_zero index bound).elim
  | succ fuel ih =>
    cases found : step? p with
    | none => simp only [run, found]
    | some next =>
      have room := step_shorter found
      simpa only [run, found] using ih next (by omega)

theorem run_preserves (fuel : Nat) (p : Program Opcode regs word) :
    let final := run fuel p
    { final with header := p.header } = p ∧
      (∀ old, final.step model old = p.step model old) ∧
      (∀ input (via : Incoming) count old, final.Arrives model input via count old ↔
        p.Arrives model input via count old) ∧
      (∀ budget input, final.source.runFrom model budget 0 input = p.source.runFrom model budget 0 input) := by
  induction fuel generalizing p with
  | zero => exact ⟨rfl, fun _ => rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩
  | succ fuel ih =>
    cases found : step? p with
    | none => simp [run, found]
    | some next =>
      obtain ⟨index, _, checked⟩ := step_checked found
      have same : { next with header := p.header } = p := by
        rw [(delete?_eq_some_iff.mp checked).2]
        rfl
      obtain ⟨interface, stepEq, arrives, runEq⟩ := ih next
      simp only [run, found]
      exact ⟨(congrArg (fun q : Program Opcode regs word => { q with header := p.header }) interface).trans same,
        fun old => (stepEq old).trans (delete?_step_eq checked old),
        fun input via count old => (arrives input via count old).trans (delete?_arrives_iff checked input old via count),
        fun budget input => (runEq budget input).trans (delete?_run_eq checked budget input)⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup
