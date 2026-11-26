module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Proofs

open RVSDG (Origin Port Tuple)
open Retained.Load.Static.Sequence.Search
open Discovery.MemRef.CF (entryDestination lowerDiamond lowerDiamond_entryTransition lowerDiamond_run run)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations storeCount)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)

variable {args : List ValueSort} {cells : Nat}
variable {facts : Certificate args} {input : Tuple (Val cells) args}

private theorem checkTail_readers {past : List (List ValueSort)} {live : Nat}
    {tail : Memory.Body args past live} {readers : List (Port args .address)}
    (store : PrefixStore args) (valid : facts.Valid input)
    (accepted : checkTail facts store tail = true) (listed : readPorts tail = some readers) :
    ∀ reader ∈ readers, cell input store.address ≠ cell input reader := by
  simp only [checkTail, listed, Bool.and_eq_true_iff] at accepted
  obtain ⟨anchor, _, checked⟩ := accepted
  have readersSafe := List.all_eq_true.mp checked
  intro reader member
  have covered := (Bool.and_eq_true_iff.mp (readersSafe reader member)).2
  have matched : cell input store.address = cell input facts.observed :=
    facts.matches_read (.arg store.address : Origin args [] .address) anchor input PUnit.unit
  rw [matched]
  exact facts.covers_read (.arg reader : Origin args [] .address) covered input PUnit.unit valid

private theorem readPorts_safe {past : List (List ValueSort)} {live : Nat}
    {tail : Memory.Body args past live} {readers : List (Port args .address)}
    (store : PrefixStore args) (listed : readPorts tail = some readers)
    (distinct : ∀ reader ∈ readers, cell input store.address ≠ cell input reader) :
    Retained.Load.checkTail store input tail = true := by
  induction tail generalizing readers with
  | ret => rfl
  | store => contradiction
  | load _ address rest ih =>
    cases address with
    | output => contradiction
    | arg reader =>
      obtain ⟨remaining, checked, packed⟩ := Option.map_eq_some_iff.mp listed
      cases packed
      have first := distinct reader (List.mem_cons_self ..)
      have next := ih checked (fun port member => distinct port (List.mem_cons_of_mem _ member))
      simp [Retained.Load.checkTail, first, next]

theorem checkTail_disjoint {past : List (List ValueSort)} {live : Nat}
    (tail : Memory.Body args past live) (store : PrefixStore args)
    (safe : checkTail facts store tail = true) (valid : facts.Valid input) :
    Retained.Load.checkTail store input tail = true := by
  cases listed : readPorts tail with
  | none => simp [checkTail, listed] at safe
  | some readers => exact readPorts_safe store listed (checkTail_readers store valid safe listed)

theorem checkTail_read_word {past : List (List ValueSort)} {live : Nat}
    {tail : Memory.Body args past live} {readers : List (Port args .address)}
    (store : PrefixStore args) (valid : facts.Valid input)
    (accepted : checkTail facts store tail = true) (listed : readPorts tail = some readers)
    (reader : Port args .address) (member : reader ∈ readers) (initial : Heap cells) :
    ((store.table.denote input initial).2).read (cell input reader) = initial.read (cell input reader) :=
  initial.read_write_other (cell input store.address) (cell input reader)
    (input.get store.value) (checkTail_readers store valid accepted listed reader member).symm

theorem checkTail_load_word {past : List (List ValueSort)} {live : Nat}
    {memory returnedMemory : MemoryInput live} {reader : Port args .address}
    {returned : Origin args ([.word] :: past) .word}
    (store : PrefixStore args) (valid : facts.Valid input)
    (accepted : checkTail facts store (.load memory (.arg reader) (.ret returnedMemory returned)) = true)
    (initial : Heap cells) :
    ((store.table.denote input initial).2).read (cell input reader) = initial.read (cell input reader) :=
  checkTail_read_word store valid accepted (show readPorts _ = some [reader] from rfl) reader (.head _) initial

theorem cut_preserves {entry retained : Memory.Graph args} {version : Nat} {store : PrefixStore args}
    (accepted : cut facts version entry = some (store, retained)) (valid : facts.Valid input) (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial =
        ((retained.denote input initial).1, (store.table.denote input (retained.denote input initial).2).2) := by
  obtain ⟨order, same⟩ := Retained.Load.cutWith_disjoint_preserves input (checkTail facts)
    (fun tail selected safe => checkTail_disjoint tail selected safe valid) accepted
  exact ⟨order, same PUnit.unit initial⟩

variable {graph : Graph args} {entry : Memory.Graph args} {version : Nat} {artifacts : Artifacts cells args}

theorem emit_replay (emitted : emit cells graph entry version facts = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store retained edited, cut facts version entry = some (store, retained) ∧
      Discovery.rewrite ⟨store, graph⟩ input = some edited ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retained)⟩ := by
  obtain ⟨⟨store, retained⟩, checked, next⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨edited, accepted, packed⟩ := Option.bind_eq_some_iff.mp next
  exact ⟨store, retained, edited, checked, Static.rewrite_replay accepted input, (Option.some.inj packed).symm⟩

theorem emit_observations (emitted : emit cells graph entry version facts = some artifacts)
    (valid : facts.Valid input) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryWord artifacts.optimized input initial = entryWord artifacts.original input initial ∧
      entryDestination artifacts.optimized input guard initial = entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected := by
  obtain ⟨store, retained, edited, checked, replay, rfl⟩ := emit_replay emitted input
  have transfer := (cut_preserves checked valid initial.cell).2
  have word := congrArg Prod.fst transfer
  have heap := congrArg Prod.snd transfer
  have same := (Discovery.rewrite_denote input replay guard (Memory.Graph.denote retained input initial.cell).2).trans
    (congrArg (graph.denote guard input) heap.symm)
  constructor
  · change some (observe retained input initial).1 = some (observe entry input initial).1
    rw [lower_run, lower_run]
    exact congrArg some word.symm
  constructor
  · simp only [entryDestination, lowerDiamond_entryTransition, Discovery.rewrite_merge input replay]
  · simp only [lowerDiamond_run, same, and_self]

variable {result : LoadTail.Result cells args}

theorem lower_checked (emitted : lower graph entry input facts = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Retained.Load.Static.Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.routes with
      | none => result.programs = result.entryOnly.programs
      | some artifacts =>
        facts.Valid input ∧ emit cells graph result.entryOnly.entry (storeCount result.entryOnly.entry) facts = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized := by
  have stage := Inference.lower_eq_ok graph entry input
  simp only [lower, Inference.lower_eq_ok] at emitted
  cases Except.ok.inj emitted
  refine ⟨stage, (Inference.lower_checked stage).1, ?_⟩
  by_cases valid : facts.check input = true
  · cases routed : emit cells graph (discover entry (Inference.inferContracts entry)).entry
      (storeCount (discover entry (Inference.inferContracts entry)).entry) facts with
    | none => simp [valid, Result.programs]
    | some artifacts =>
      obtain ⟨_, _, _, _, _, packed⟩ := emit_replay routed input
      simp only [ite_eq_left valid, true_and]
      exact ⟨(facts.check_iff_valid input).mp valid, congrArg Artifacts.original packed⟩
  · simp [valid, Result.programs]

theorem lower_observations (emitted : lower graph entry input facts = .ok result)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let observed := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (observed.1, Buffer.mk observed.2)
    entryDestination programs.optimized programs.input guard initial =
      entryDestination programs.original programs.input guard initial ∧
      run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨entryReplay, _, routeReplay⟩ := lower_checked emitted
  have first := Inference.lower_observations entryReplay guard fuel initial
  let stage := result.entryOnly.programs
  have sameDestination : entryDestination stage.optimized stage.input guard initial =
      entryDestination stage.original stage.input guard initial :=
    congrArg Prod.fst first.1
  cases outcome : result.routes with
  | none => simpa only [Result.programs, outcome] using And.intro sameDestination first.2
  | some artifacts =>
    rw [outcome] at routeReplay
    obtain ⟨valid, routed, linked⟩ := routeReplay
    have second := (emit_observations routed valid guard fuel initial).2
    rw [linked] at second
    have sameInput : stage.input = input := by
      rw [Inference.lower_eq_ok] at entryReplay
      exact congrArg (fun emission : Emission cells args => emission.programs.input) (Except.ok.inj entryReplay).symm
    rw [← sameInput] at second
    simp only [Result.programs, outcome]
    exact ⟨second.1.trans sameDestination, first.2.1, (second.2.2.trans second.2.1.symm).trans first.2.2⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Proofs
