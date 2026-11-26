module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Proofs

open RVSDG (Locals Origin Port Tuple)
open Memory.Forwarding (originKey_injective)
open Memory.Forwarding.Disjoint (Certificate cell)

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}
variable {facts : Certificate args}

theorem reindexMemory_denote (body : Body args past version) (live : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    (reindexMemory body live).denote input locals heap = body.denote input locals heap := by
  induction body generalizing live heap with
  | ret => rfl
  | load _ _ _ ih => exact ih _ _ _
  | store _ _ _ _ ih => exact ih _ _ _

theorem readAt_store (memory : MemoryInput version) (address : Origin args past .address)
    (word : Origin args past .word) (rest : Body args past (version + 1)) (index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (.store memory address word rest) index input locals heap =
      readAt rest index input locals (heap.write (readValue address input locals) (readValue word input locals)) := by
  simp [readAt, throughLoad, Option.map_map, Function.comp_def, Body.denote]

theorem readAt_load (memory : MemoryInput version) (address : Origin args past .address)
    (rest : Body args ([.word] :: past) version) (index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (.load memory address rest) (index + 1) input locals heap =
      readAt rest index input (.cons (heap.read (readValue address input locals)) .nil, locals) heap := by
  simp [readAt, throughLoad, Option.map_map, Function.comp_def, Body.denote]

private theorem throughLoad_reindex (body : Body args past version) (target index : Nat) :
    throughLoad (reindexMemory body target) index =
      (throughLoad body index).map (fun selected => reindexMemory selected target) := by
  induction body generalizing target index with
  | ret => rfl
  | load _ _ _ ih =>
    cases index with
    | zero => rfl
    | succ index => simp [reindexMemory, throughLoad, ih, Option.map_map, Function.comp_def]
  | store _ _ _ _ ih => simp [reindexMemory, throughLoad, ih, Option.map_map, Function.comp_def]

theorem reindexMemory_readAt (body : Body args past version) (target index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (reindexMemory body target) index input locals heap = readAt body index input locals heap := by
  simp [readAt, throughLoad_reindex, Option.map_map, Function.comp_def, reindexMemory_denote]

private theorem arg_read (port other : Port args .address) (same : port.index = other.index)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) :
    readValue (.arg port) input locals = cell input other := by
  have wire : (Origin.arg port : Origin args past .address) = .arg other :=
    originKey_injective (congrArg Sum.inl same)
  exact congrArg (fun address => readValue address input locals) wire

private theorem matches_read (address : Origin args past .address) (matched : facts.matches address = true)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) :
    readValue address input locals = cell input facts.observed := by
  cases address with
  | arg port => exact arg_read port _ (beq_iff_eq.mp matched) input locals
  | output => cases matched

private theorem covers_read (address : Origin args past .address) (covered : facts.covers address = true)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (valid : facts.Valid input) :
    cell input facts.observed ≠ readValue address input locals := by
  cases address with
  | arg port =>
    obtain ⟨other, listed, same⟩ := List.any_eq_true.mp covered
    rw [arg_read port other (beq_iff_eq.mp same) input locals]
    exact valid other listed
  | output => cases covered

private def AgreeOutside (observed : Address cells) (first second : Heap cells) : Prop :=
  ∀ other, other ≠ observed → first.read other = second.read other

private theorem writes_agree {observed written : Address cells} {first second : Heap cells}
    (agrees : AgreeOutside observed first second) (word : Word) :
    AgreeOutside observed (first.write written word) (second.write written word) := by
  intro other distinct
  by_cases same : other = written
  · subst other
    simp only [Heap.read_write_same]
  · simpa only [Heap.read_write_other _ _ _ _ same] using agrees other distinct

private theorem overwrite_agrees {observed : Address cells} {first second : Heap cells}
    (agrees : AgreeOutside observed first second) (word : Word) :
    first.write observed word = second.write observed word := by
  funext other
  change (first.write observed word).read other = (second.write observed word).read other
  by_cases same : other = observed
  · subst other
    simp only [Heap.read_write_same]
  · exact writes_agree agrees word other same

private theorem noReadUntil_observations (overwrite : Nat) (body : Body args past version)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (valid : facts.Valid input)
    (first second : Heap cells) (agrees : AgreeOutside (cell input facts.observed) first second)
    (checked : noReadUntil facts overwrite body = true) :
    body.denote input locals first = body.denote input locals second ∧
      ∀ index, readAt body index input locals first = readAt body index input locals second := by
  induction body generalizing first second with
  | ret => cases checked
  | load _ address _ ih =>
    obtain ⟨reader, rest⟩ := Bool.and_eq_true_iff.mp checked
    have disjoint := covers_read address (Bool.and_eq_true_iff.mp reader).2 input locals valid
    have same := agrees (readValue address input locals) disjoint.symm
    obtain ⟨result, reads⟩ := ih _ _ _ agrees rest
    refine ⟨by simpa only [Body.denote, same] using result, ?_⟩
    intro index
    cases index with
    | zero => exact congrArg some same
    | succ index => simpa only [readAt_load, same] using reads index
  | @store _ version memory address value _ ih =>
    by_cases hit : version + 1 = overwrite
    · have matched : facts.matches address = true := by
        simpa only [noReadUntil, ite_eq_left hit] using checked
      have addressEq := matches_read address matched input locals
      have heaps := overwrite_agrees agrees (readValue value input locals)
      exact ⟨by simp only [Body.denote, addressEq, heaps],
        fun index => by simp only [readAt_store memory, addressEq, heaps]⟩
    · have rest := show noReadUntil facts overwrite _ = true by
        simpa only [noReadUntil, ite_eq_right hit] using checked
      obtain ⟨result, reads⟩ := ih _ _ _ (writes_agree agrees (readValue value input locals)) rest
      exact ⟨result, fun index => by simpa only [readAt_store memory] using reads index⟩

theorem noReadUntil_write (overwrite : Nat) (graph : Graph args)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells) (word : Word)
    (checked : noReadUntil facts overwrite graph = true) :
    let written := initial.write (cell input facts.observed) word
    graph.denote input initial = graph.denote input written ∧
      ∀ index, readAt graph index input PUnit.unit initial = readAt graph index input PUnit.unit written :=
  noReadUntil_observations overwrite graph input PUnit.unit valid initial _
    (fun other distinct => (initial.read_write_other _ other word distinct).symm) checked

private theorem rewriteAt_observations (candidate : Candidate) (body rewritten : Body args past version)
    (success : rewriteAt candidate facts body = some rewritten)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (valid : facts.Valid input)
    (heap : Heap cells) :
    rewritten.denote input locals heap = body.denote input locals heap ∧
      ∀ index, readAt rewritten index input locals heap = readAt body index input locals heap := by
  induction body generalizing heap with
  | ret => cases success
  | load memory _ _ ih =>
    obtain ⟨tail, accepted, rfl⟩ := Option.map_eq_some_iff.mp success
    obtain ⟨result, reads⟩ := ih tail accepted _ _
    refine ⟨result, ?_⟩
    intro index
    cases index with
    | zero => rfl
    | succ index => simpa only [readAt_load memory] using reads index
  | @store _ version memory address value rest ih =>
    by_cases hit : version + 1 = candidate.removeVersion
    · simp only [rewriteAt, ite_eq_left hit] at success
      split at success
      next checked =>
        have same := Option.some.inj success
        subst rewritten
        obtain ⟨matched, safe⟩ := Bool.and_eq_true_iff.mp checked
        have outside : AgreeOutside (cell input facts.observed) heap
            (heap.write (readValue address input locals) (readValue value input locals)) := by
          intro other distinct
          rw [matches_read address matched input locals]
          exact (Heap.read_write_other heap _ _ _ distinct).symm
        obtain ⟨result, reads⟩ := noReadUntil_observations candidate.overwriteVersion rest input locals
          valid _ _ outside safe
        refine ⟨(reindexMemory_denote rest version input locals heap).trans result, fun index => ?_⟩
        rw [reindexMemory_readAt, readAt_store memory]
        exact reads index
      next => cases success
    · simp only [rewriteAt, ite_eq_right hit] at success
      obtain ⟨tail, accepted, rfl⟩ := Option.map_eq_some_iff.mp success
      obtain ⟨result, reads⟩ := ih tail accepted _ _
      exact ⟨result, fun index => by simpa only [readAt_store memory] using reads index⟩

theorem rewriteWith_observations {graph rewritten : Graph args} {candidate : Candidate}
    (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap ∧
      ∀ index, readAt rewritten index input PUnit.unit heap = readAt graph index input PUnit.unit heap :=
  rewriteAt_observations candidate graph rewritten success input PUnit.unit valid heap

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Proofs
