module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Proofs

open RVSDG (Locals Origin Port Tuple)
open Memory.Forwarding (originKey_injective)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {past : List (List ValueSort)} {live cells : Nat}

private theorem readAt_store (memory : MemoryInput live) (address : Origin args past .address)
    (word : Origin args past .word) (rest : Body args past (live + 1)) (index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (.store memory address word rest) index input locals heap =
      readAt rest index input locals (heap.write (readValue address input locals) (readValue word input locals)) := by
  simp [readAt, throughLoad, Option.map_map, Function.comp_def, Body.denote]

private theorem readAt_load (memory : MemoryInput live) (address : Origin args past .address)
    (rest : Body args ([.word] :: past) live) (index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (.load memory address rest) (index + 1) input locals heap =
      readAt rest index input (.cons (heap.read (readValue address input locals)) .nil, locals) heap := by
  simp [readAt, throughLoad, Option.map_map, Function.comp_def, Body.denote]

private theorem throughLoad_reindex (body : Body args past live) (target index : Nat) :
    throughLoad (reindexMemory body target) index =
      (throughLoad body index).map (fun selected => reindexMemory selected target) := by
  induction body generalizing target index with
  | ret => rfl
  | load _ _ _ ih =>
    cases index with
    | zero => rfl
    | succ index => simp [reindexMemory, throughLoad, ih, Option.map_map, Function.comp_def]
  | store _ _ _ _ ih => simp [reindexMemory, throughLoad, ih, Option.map_map, Function.comp_def]

private theorem readAt_reindex (body : Body args past live) (target index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (reindexMemory body target) index input locals heap = readAt body index input locals heap := by
  simp [readAt, throughLoad_reindex, Option.map_map, Function.comp_def, reindexMemory_denote]

private theorem adjacent_replay {version : Nat} {address : Port args .address} (body : Body args past live)
    (accepted : adjacentAddress version body = some address) :
    ∃ rewritten, rewriteAt ⟨version, version + 1⟩ ⟨address, []⟩ body = some rewritten ∧
      ∀ {cells : Nat} (index : Nat) (input : Tuple (Val cells) args)
        (locals : Locals (Val cells) past) (heap : Heap cells),
        readAt rewritten index input locals heap = readAt body index input locals heap := by
  induction body with
  | ret => contradiction
  | load memory reader rest ih =>
    obtain ⟨rewritten, replay, coupled⟩ := ih accepted
    refine ⟨.load memory reader rewritten, by simp [rewriteAt, replay], ?_⟩
    intro cells index input locals heap
    cases index with
    | zero => rfl
    | succ index =>
      rw [readAt_load, readAt_load]
      exact coupled index input _ heap
  | @store scope live memory earlier word rest ih =>
    by_cases nominated : live + 1 = version
    · subst version
      cases earlier with
      | output => cases rest <;> simp [adjacentAddress] at accepted
      | arg first =>
        cases rest with
        | ret => simp [adjacentAddress] at accepted
        | load => simp [adjacentAddress] at accepted
        | store laterMemory later retainedWord suffix =>
          cases later with
          | output => simp [adjacentAddress] at accepted
          | arg second =>
            by_cases same : first.index = second.index
            · have anchor : first = address := by simpa [adjacentAddress, same] using accepted
              have pointers : (Origin.arg first : Origin args scope .address) = .arg second :=
                originKey_injective (congrArg Sum.inl same)
              have equal := Origin.arg.inj pointers
              subst second
              subst address
              refine ⟨reindexMemory (.store laterMemory (.arg first) retainedWord suffix) live, ?_, ?_⟩
              · simp [rewriteAt, noReadUntil, Certificate.matches]
              · intro cells index input locals heap
                rw [readAt_reindex, readAt_store, readAt_store, readAt_store]
                exact congrArg (readAt suffix index input locals)
                  (Function.update_idem (β := fun _ : Address cells => Word)
                    (readValue word input locals) (readValue retainedWord input locals) heap).symm
            · simp [adjacentAddress, same] at accepted
    · have later : adjacentAddress version rest = some address := by
        simpa only [adjacentAddress, ite_eq_right nominated] using accepted
      obtain ⟨rewritten, replay, coupled⟩ := ih later
      refine ⟨.store memory earlier word rewritten, by simp [rewriteAt, nominated, replay], ?_⟩
      intro cells index input locals heap
      rw [readAt_store, readAt_store]
      exact coupled index input locals _

theorem rewrite_checked {graph rewritten : Graph args} {version : Nat}
    (success : rewrite graph version = some rewritten) :
    usersOf version graph = [.store (version + 1)] ∧
      ∃ address, adjacentAddress version graph = some address ∧
        DeadStore.rewriteWith graph ⟨version, version + 1⟩ ⟨address, []⟩ = some rewritten := by
  unfold rewrite at success
  split at success
  next unique =>
    obtain ⟨address, selected, replay⟩ := Option.bind_eq_some_iff.mp success
    exact ⟨unique, address, selected, replay⟩
  next => contradiction

theorem rewrite_exists_iff (graph : Graph args) (version : Nat) :
    (∃ rewritten, rewrite graph version = some rewritten) ↔
      usersOf version graph = [.store (version + 1)] ∧
        ∃ address, adjacentAddress version graph = some address := by
  constructor
  · rintro ⟨rewritten, checked⟩
    obtain ⟨users, address, pair, _⟩ := rewrite_checked checked
    exact ⟨users, address, pair⟩
  · rintro ⟨users, address, pair⟩
    obtain ⟨rewritten, replay, _⟩ := adjacent_replay graph pair
    exact ⟨rewritten, by simpa [rewrite, users, pair, rewriteWith] using replay⟩

theorem rewrite_readAt {graph rewritten : Graph args} {version : Nat}
    (success : rewrite graph version = some rewritten) (index : Nat)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    readAt rewritten index input PUnit.unit heap = readAt graph index input PUnit.unit heap := by
  obtain ⟨_, _, selected, replay⟩ := rewrite_checked success
  obtain ⟨retained, expected, coupled⟩ := adjacent_replay graph selected
  rw [rewriteWith] at replay
  rw [replay] at expected
  cases Option.some.inj expected
  exact coupled index input PUnit.unit heap

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Proofs
