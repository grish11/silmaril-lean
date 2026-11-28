module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Proofs

open RVSDG (Origin Port Tuple)
open Memory.Forwarding (originKey originKey_injective)
open Memory.Forwarding.Disjoint (Certificate cell)
open Discovery.MemRef.CF (entryTransition run lowerDiamond_entryTransition lowerDiamond_run)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}
variable {facts : AddressContract args} {input : Tuple (Val cells) args}

theorem check_iff_valid (facts : AddressContract args) (input : Tuple (Val cells) args) :
    facts.check input = true ↔ facts.Valid input := by
  simp [AddressContract.check, AddressContract.Valid, Certificate.check_iff_valid]

private theorem same_cell (port : Port args .address)
    (same : facts.same port = true) (valid : facts.Valid input) :
    cell input facts.disjoint.observed = cell input port := by
  rcases Bool.or_eq_true_iff.mp same with reflexive | listed
  · exact (facts.disjoint.matches_read (.arg port) reflexive input PUnit.unit).symm
  · obtain ⟨other, member, eqIndex⟩ := List.any_eq_true.mp listed
    have key : originKey (.arg port : Origin args [] .address) = originKey (.arg other : Origin args [] .address) :=
      congrArg Sum.inl (beq_iff_eq.mp eqIndex)
    have equal : port = other := Origin.arg.inj (originKey_injective key)
    rw [equal]
    exact valid.2 other member

private theorem tail_agrees {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
    (selected : PrefixStore args) (anchor : cell input selected.address = cell input facts.disjoint.observed)
    (accepted : checkTail facts tail = true) (valid : facts.Valid input) :
    Load.checkOverwrite selected input tail = true := by
  induction tail with
  | ret => contradiction
  | load _ address rest ih =>
    cases address with
    | output => contradiction
    | arg reader =>
      obtain ⟨covered, safeRest⟩ := Bool.and_eq_true_iff.mp accepted
      have different : cell input selected.address ≠ cell input reader :=
        anchor ▸ facts.disjoint.covers_read (.arg reader) covered input PUnit.unit valid.1
      simp [Load.checkOverwrite, different, ih safeRest]
  | store _ address _ rest ih =>
    cases address with
    | output => contradiction
    | arg writer =>
      by_cases same : facts.same writer = true
      · have equal := anchor.trans (same_cell writer same valid)
        simp [Load.checkOverwrite, equal]
      · simp only [checkTail, ite_eq_right same] at accepted
        obtain ⟨covered, safeRest⟩ := Bool.and_eq_true_iff.mp accepted
        have different : cell input selected.address ≠ cell input writer :=
          anchor ▸ facts.disjoint.covers_read (.arg writer) covered input PUnit.unit valid.1
        simp [Load.checkOverwrite, different, ih safeRest]

private theorem cutWith_agrees {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (accepted : Load.cutWith (fun store {_ _} tail =>
      facts.disjoint.matches (past := []) (.arg store.address) && checkTail facts tail) version body = some (selected, retained))
    (valid : facts.Valid input) :
    Load.cutOverwrite version input body = some (selected, retained) := by
  induction body generalizing selected with
  | ret => contradiction
  | load => contradiction
  | @store _ live _ address word rest ih =>
    cases address with
    | output => contradiction
    | arg address =>
      cases word with
      | output => contradiction
      | arg word =>
        by_cases chosen : live + 1 = version
        · simp only [Load.cutWith, ite_eq_left chosen] at accepted
          split at accepted
          next safe =>
            obtain ⟨matched, acceptedTail⟩ := Bool.and_eq_true_iff.mp safe
            have anchor := facts.disjoint.matches_read (.arg address) matched input PUnit.unit
            have concrete := tail_agrees rest ⟨address, word⟩ anchor acceptedTail valid
            simpa only [Load.cutOverwrite, Load.cutWith, ite_eq_left chosen, ite_eq_left concrete] using accepted
          next => contradiction
        · simp only [Load.cutWith, ite_eq_right chosen] at accepted
          obtain ⟨⟨store, suffix⟩, checked, rebuilt⟩ := Option.map_eq_some_iff.mp accepted
          simp only [Load.cutOverwrite, Load.cutWith, ite_eq_right chosen]
          exact Option.map_eq_some_iff.mpr ⟨(store, suffix), ih checked, rebuilt⟩

theorem cut_agrees {entry retained : Memory.Graph args} {selected : PrefixStore args} {version : Nat}
    (accepted : cut facts version entry = some (selected, retained)) (valid : facts.Valid input) :
    Load.cutOverwrite version input entry = some (selected, retained) := by
  unfold cut at accepted
  split at accepted
  · exact cutWith_agrees accepted valid
  · contradiction

private theorem cleanup_denote (entry : Memory.Graph args)
    (prior : Option (Memory.DeadStore.Candidate × Port args .address)) (input : Tuple (Val cells) args)
    (initial : Heap cells) :
    (cleanup entry prior).denote input initial = entry.denote input initial := by
  cases prior with
  | none => rfl
  | some candidate =>
    obtain ⟨candidate, port⟩ := candidate
    unfold cleanup
    change ((Memory.DeadStore.rewriteWith entry candidate ⟨port, []⟩).getD entry).denote input initial = _
    cases accepted : Memory.DeadStore.rewriteWith entry candidate ⟨port, []⟩ with
    | none => rfl
    | some edited =>
      exact Memory.DeadStore.rewriteWith_denote accepted input (by simp [Certificate.Valid]) initial

private theorem edited_denote (entry : Memory.Graph args)
    (version : Nat) (prior : Option (Memory.DeadStore.Candidate × Port args .address))
    (valid : facts.Valid input) (initial : Heap cells) :
    let current := cleanup entry prior
    (((cut facts version current).map Prod.snd).getD current).denote input initial = entry.denote input initial := by
  dsimp only
  cases accepted : cut facts version (cleanup entry prior) with
  | none => simpa only [accepted, Option.map_none, Option.getD_none] using cleanup_denote entry prior input initial
  | some edit =>
    obtain ⟨selected, retained⟩ := edit
    simp only [Option.map_some, Option.getD_some]
    exact ((Load.cutOverwrite_preserves input (cut_agrees accepted valid)).2 PUnit.unit initial).symm.trans
      (cleanup_denote entry prior input initial)

theorem lower_entryTransition_eq (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (prior : Option (Memory.DeadStore.Candidate × Port args .address))
    (valid : facts.Valid input) (guard : Bool) (initial : Buffer cells) :
    let programs := lower cells graph entry version facts prior
    entryTransition programs.optimized input guard initial = entryTransition programs.original input guard initial := by
  simp only [lower, lowerDiamond_entryTransition, edited_denote entry version prior valid initial.cell]

theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (prior : Option (Memory.DeadStore.Candidate × Port args .address))
    (valid : facts.Valid input) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := lower cells graph entry version facts prior
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original input guard fuel initial = expected ∧
      run programs.optimized input guard fuel initial = expected := by
  simp only [lower, lowerDiamond_run, edited_denote entry version prior valid initial.cell, and_self]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Proofs
