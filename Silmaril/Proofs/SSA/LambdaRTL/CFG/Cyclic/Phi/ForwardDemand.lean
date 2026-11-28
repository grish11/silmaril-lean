module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Demand.Defs

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

universe v w

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

omit [DecidableEq V] in
/-- Looking up the key of a member of a list with distinct keys, after the
values were mapped by a function of the entry. -/
theorem lookup_mapped_proof {B C : Type*} (f : K → B → C) :
    (entries : List (K × B)) → (entries.map Prod.fst).Nodup → {key : K} → {value : B} →
    (key, value) ∈ entries →
    (entries.map fun (k, b) => (k, f k b)).lookup key = some (f key value)
  | [], _, _, _, member => by cases member
  | (k, b) :: rest, distinct, key, value, member => by
    simp only [List.map, List.nodup_cons] at distinct
    simp only [List.map, List.lookup]
    rcases List.mem_cons.mp member with head | tail
    · cases head
      simp
    · have other : key ≠ k := fun eq =>
        distinct.1 (eq ▸ List.mem_map.mpr ⟨(key, value), tail, rfl⟩)
      have differs : (key == k) = false := by simp [other]
      rw [differs]
      exact lookup_mapped_proof f rest distinct.2 tail

omit [DecidableEq V] in
/-- A found value of a list whose values were mapped by a function of the
entry is the image of an entry at that key. -/
theorem lookup_mapped_some_proof {B C : Type*} (f : K → B → C) :
    (entries : List (K × B)) → {key : K} → {value : C} →
    (entries.map fun (k, b) => (k, f k b)).lookup key = some value →
    ∃ source, (key, source) ∈ entries ∧ value = f key source
  | [], _, _, found => by cases found
  | (k, b) :: rest, key, value, found => by
    simp only [List.map, List.lookup] at found
    split at found
    · rename_i same
      cases found
      rw [eq_of_beq same]
      exact ⟨b, List.mem_cons_self, rfl⟩
    · obtain ⟨source, member, eq⟩ := lookup_mapped_some_proof f rest found
      exact ⟨source, List.mem_cons_of_mem _ member, eq⟩

/-- The demand of a block has none of the registers the block defines and
none of the declared inputs. -/
theorem demandOf_outside_proof (routed : Graph V K F) (inputs : List V) (next : K → List V)
    (key : K) (source : Block V K F) {register : V}
    (demanded : register ∈ demandOf routed inputs next key source) :
    register ∉ source.rows.map Row.dst ∧ register ∉ GlobalSSA.bodyDefinitions source.body ∧
      register ∉ inputs := by
  simp only [demandOf, List.mem_dedup, List.mem_filter] at demanded
  simpa [not_or, and_assoc] using demanded.2

/-- A register that the inferred table gives a block is in the demand of
some block of the graph with that label. -/
theorem received_infer_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    {key : K} {register : V} (received : register ∈ (infer graph exits inputs).received key) :
    ∃ source, (key, source) ∈ graph.blocks ∧
      register ∈ demandOf (OrderedExits.forScope graph exits) inputs
        (demand graph (OrderedExits.forScope graph exits) inputs graph.blocks.length) key source := by
  simp only [Table.received] at received
  cases found : (infer graph exits inputs).lookup key with
  | none =>
    rw [found] at received
    cases received
  | some value =>
    rw [found] at received
    obtain ⟨source, member, rfl⟩ := lookup_mapped_some_proof _ graph.blocks found
    exact ⟨source, member, received⟩

/-- The inferred table never forwards a declared input. -/
theorem infer_input_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    {key : K} {register : V} (received : register ∈ (infer graph exits inputs).received key) :
    register ∉ inputs := by
  obtain ⟨source, _, demanded⟩ := received_infer_proof graph exits inputs received
  exact (demandOf_outside_proof _ inputs _ key source demanded).2.2

/-- The inferred table passes the check of the normalization when the
labels of the blocks are distinct. -/
theorem check_infer_proof (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (distinct : (graph.blocks.map Prod.fst).Nodup) :
    check graph (infer graph exits inputs) = true := by
  simp only [check, List.all_eq_true]
  intro ⟨key, source⟩ member register received
  have found : (infer graph exits inputs).lookup key =
      some (demandOf (OrderedExits.forScope graph exits) inputs
        (demand graph (OrderedExits.forScope graph exits) inputs graph.blocks.length) key source) :=
    lookup_mapped_proof _ graph.blocks distinct member
  simp only [Table.received, found, Option.getD_some] at received
  have outside := demandOf_outside_proof _ inputs _ key source received
  simp [outside.1, outside.2.1]

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
