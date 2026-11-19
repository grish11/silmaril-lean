module

public import Silmaril.Elf.Region.Calls.Examples.Defs
public import Silmaril.Elf.Region.Calls.Thms
public import Silmaril.Elf.Region.Calls.Semantic.Thms

public section
namespace Silmaril.Elf.Region.Calls.Examples.Proofs
open Silmaril.Semantics.Function
open Silmaril.X86 (Byte MState)
open Silmaril.Process (Memory ByteMemory)

theorem fetch_initial {addr : Nat} (fits : addr + 5 ≤ fixtureCode.length)
    (permitted : initial.memory.Permitted .execute addr 5) :
    initial.memory.fetchBytes addr 5 = some ((fixtureCode.drop addr).take 5) := by
  have len : ((fixtureCode.drop addr).take 5).length = 5 := by
    simp only [List.length_take, List.length_drop]
    omega
  have read := Memory.readWith_eq initial.memory .execute addr ((fixtureCode.drop addr).take 5)
    (len.symm ▸ permitted) fun index bound => by
      have inCode : addr + index < fixtureCode.length := by omega
      simpa only [initial, Nat.zero_add, List.getElem_take, List.getElem_drop] using
        Memory.install_get (∅ : ByteMemory) 0 fixtureCode (addr + index) inCode
  simpa only [Memory.fetchBytes, len] using read

theorem fetch_entry : initial.memory.fetchBytes initial.core.rip.toNat 5 = some callBytes :=
  fetch_initial (addr := 0) (by decide) (by decide +kernel)

theorem fetch_worker : afterEntry.memory.fetchBytes afterEntry.core.rip.toNat 5 = some callBytes := by
  have allowed : initial.memory.Permitted .write 40 8 := by decide +kernel
  have written := Silmaril.X86.pushWord_eq_some (s := initial.core) (value := 5) allowed
  have frame : Memory.WritesOnly initial.memory afterEntry.memory 40 8 := Silmaril.X86.pushWord_writesOnly written
  have spared := (Memory.writesOnly_iff_writesWithin ..).mp frame
  change afterEntry.memory.fetchBytes 6 5 = _
  rw [spared.fetchBytes (fun offset bound => by omega)]
  exact fetch_initial (addr := 6) (by decide) (by decide +kernel)

theorem observation_entry : observe plan initial = some (0, .localFn 6) := by
  simp only [observe, fetch_entry]; rfl

theorem observation_worker : observe plan afterEntry = some (6, .foreign external) := by
  simp only [observe, fetch_worker]; rfl

theorem cover : SiteCoverage plan owner fixture inventory := by
  rintro caller pre site callee (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) observeEq
  · rw [observation_entry] at observeEq
    cases observeEq
    exact ⟨extractRow fixture plan entry, List.Mem.head _, 6, List.Mem.head _⟩
  · rw [observation_worker] at observeEq
    cases observeEq
    exact ⟨extractRow fixture plan worker, List.Mem.tail _ (List.Mem.head _), 12, List.Mem.head _⟩

theorem retired (exit : BitVec 64) {pre : MState}
    (fetched : pre.memory.fetchBytes pre.core.rip.toNat 5 = some callBytes)
    (writable : pre.memory.Permitted .write (pre.core.read .rsp - 8#64).toNat 8) :
    (Silmaril.Machine.Region.X86.system exit).step pre []
      (afterCall pre (pre.core.rip + 5#64 + (1#32).signExtend 64)) :=
  call_retirement (exit := exit) (displacement := 1) fetched rfl (Silmaril.X86.pushWord_eq_some writable)

theorem actual_entry : machine.callStep fixture entryCall initial afterEntry := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, [], ?_, ⟨observation_entry, rfl, rfl⟩, rfl⟩
  exact retired 60 fetch_entry (by decide +kernel)

theorem actual_worker : machine.callStep fixture workerCall afterEntry afterWorker := by
  refine ⟨Or.inr ⟨rfl, rfl⟩, [], ?_, ⟨observation_worker, rfl, rfl⟩, rfl⟩
  exact retired 60 fetch_worker (by decide +kernel)

theorem refined_entry : refinedMachine.callStep fixture entryCall initial afterEntry := by
  refine ⟨⟨Or.inl ⟨rfl, rfl⟩, rfl⟩, [], ?_, ⟨observation_entry, rfl, rfl⟩, rfl⟩
  exact retired 64 fetch_entry (by decide +kernel)

theorem refined_worker : refinedMachine.callStep fixture workerCall afterEntry afterWorker := by
  refine ⟨⟨Or.inr ⟨rfl, rfl⟩, rfl⟩, [], ?_, ⟨observation_worker, rfl, rfl⟩, rfl⟩
  exact retired 64 fetch_worker (by decide +kernel)

theorem exit_entry {trace : List Empty} {final : MState}
    (run : Silmaril.Semantics.Region.FirstExit (machine.system fixture) (fun label => entry.Covers label)
      initial trace final) : trace = [] ∧ final = afterEntry := by
  have unique {events : List Empty} {state : MState}
      (step : (machine.system fixture).step initial events state) : events = [] ∧ state = afterEntry :=
    ⟨step.1, Silmaril.X86.Ext.Outcome.retired.inj (step.2.symm.trans (retired 60 fetch_entry (by decide +kernel)).2)⟩
  cases run with
  | leave _ step _ => exact unique step
  | step _ step rest =>
    obtain ⟨_, rfl⟩ := unique step
    have outside : ¬ entry.Covers ((machine.system fixture).pc afterEntry) := by
      change ¬ (0 ≤ 6 ∧ 6 < 0 + 6)
      decide
    cases rest with
    | leave inside _ _ => exact (outside inside).elim
    | step inside _ _ => exact (outside inside).elim

theorem certificate : Correspondence entryBoundary fixture entryCandidates (analysis inventory) := by
  constructor
  · rintro name row ⟨rfl, rfl, _, _⟩
    refine ⟨trivial, ?_, ⟨initial, rfl⟩, fun _ eq => eq ▸ rfl, fun _ _ => trivial, ?_⟩
    · change 0 ≤ 0 ∧ 0 < 0 + 6
      decide
    rintro _ trace final rfl run
    obtain ⟨_, rfl⟩ := exit_entry run
    rfl
  · rintro name row ⟨rfl, rfl, _, _⟩ _ trace final rfl run
    obtain ⟨rfl, rfl⟩ := exit_entry run
    exact Or.inr ⟨entryCall, initial, rfl, actual_entry, [], [], rfl, .refl (by
      change 0 ≤ 0 ∧ 0 < 0 + 6
      decide),
      retired 60 fetch_entry (by decide +kernel), observation_entry, rfl, rfl⟩
  · intro edge pre post step
    exact ext_covers 60 cover ⟨pre, post, step⟩

theorem entry_effects : entryEffects.Sound (fun _ => targetBound) := by
  rintro state dest ⟨edge, post, step, rfl⟩
  exact Set.singleton_subset_iff.mpr ⟨edge, certificate.may_cover ⟨state, post, step⟩, rfl⟩

theorem mixed_no_execution : ¬ ∃ final,
    Consecutive mixedMachine mixedObject (.localFn 0) mixedInitial (.foreign mixedExternal) final := by
  have fetched : mixedInitial.memory.fetchBytes mixedInitial.core.rip.toNat 5 = some (mixedCode.take 5) := by
    have permitted : mixedInitial.memory.Permitted .execute 0 (mixedCode.take 5).length := by decide +kernel
    refine Memory.readWith_eq mixedInitial.memory .execute 0 (mixedCode.take 5) permitted ?_
    intro index bound
    have inCode : index < mixedCode.length := by rw [List.length_take] at bound; omega
    simpa only [mixedInitial, Nat.zero_add, List.getElem_take] using
      Memory.install_get (∅ : ByteMemory) 0 mixedCode index inCode
  have unsupported : observe mixedPlan mixedInitial = none := by
    simp only [observe, fetched]
    rfl
  have noStep {edge : Edge signature} {post : MState} :
      ¬ mixedMachine.callStep mixedObject edge mixedInitial post := by
    rintro ⟨_, _, _, ⟨observed, _, _⟩, _⟩
    rw [unsupported] at observed
    cases observed
  have first {model : Machine signature} {context : signature.Context}
      {source dest : Node signature} {pre post : model.State}
      (path : Consecutive model context source pre dest post) : ∃ edge mid, model.callStep context edge pre mid := by
    cases path with
    | single step => exact ⟨_, _, step⟩
    | cons step _ => exact ⟨_, _, step⟩
  rintro ⟨_, path⟩
  obtain ⟨_, _, step⟩ := first path
  exact noStep step

theorem widening_admits (site : CallSite signature) (dest : Node signature)
    (admitted : admits (targetSet mixedTargets site) dest) : admits (targetSet widenedTargets site) dest := by
  by_cases main : site.caller = 0
  · simp [targetSet, mixedTargets, widenedTargets, main, admits] at admitted ⊢
    exact Or.inl admitted
  · simp [targetSet, widenedTargets, main, admits]

end Silmaril.Elf.Region.Calls.Examples.Proofs
