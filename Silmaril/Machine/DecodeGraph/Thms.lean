module

public import Silmaril.Machine.DecodeGraph.Defs
import Silmaril.Proofs.Machine.DecodeGraph.Laws

public section

namespace Silmaril.Machine.DecodeGraph

open scoped SetRel

variable {Context Source Middle Target : Type*}

theorem ofDecoder_deterministic (decoder : Decoder Source) :
    Deterministic (ofDecoder (Context := Context) decoder) := by
  intro input left right hleft hright
  exact Option.some.inj ((show decoder.decode input.2 = some left from hleft).symm.trans hright)

theorem ofDecoder_positive (decoder : Decoder Source) : Positive (ofDecoder (Context := Context) decoder) :=
  fun _ _ _ _ h => decoder.decode_length_pos h

theorem ofDecoder_fits (decoder : Decoder Source) : Fits (ofDecoder (Context := Context) decoder) :=
  fun _ _ _ _ h => decoder.decode_length_le h

theorem ofDecoder_prefixLocal (decoder : Decoder Source) :
    PrefixLocal (ofDecoder (Context := Context) decoder) :=
  fun _ _ _ _ bound => decoder.decode_eq_some_iff_take.trans (and_iff_right bound)

theorem ofDecoder_encode (decoder : Decoder Source) (ctx : Context) (instr : Source) (rest : Bytes) :
    ((ctx, decoder.encode instr ++ rest), (instr, (decoder.encode instr).length)) ∈ ofDecoder decoder :=
  decoder.decode_encode_append instr rest

/-- Inclusion does not resolve a conflict: the join retains both successes. -/
theorem not_deterministic_sup {first second : Graph Context Source} {input left right}
    (hleft : (input, left) ∈ first) (hright : (input, right) ∈ second) (different : left ≠ right) :
    ¬ Deterministic (first ⊔ second) :=
  fun unique => different (unique (Or.inl hleft) (Or.inr hright))

@[simp] theorem onSpan_id : onSpan (SetRel.id : SetRel Source Source) = SetRel.id := by
  ext ⟨⟨left, width⟩, ⟨right, count⟩⟩
  simp [onSpan, SetRel.id]

theorem onSpan_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    onSpan (first ○ second) = onSpan first ○ onSpan second :=
  Proofs.onSpan_comp first second

@[simp] theorem transport_id (graph : Graph Context Source) : transport SetRel.id graph = graph := by
  simp [transport]

theorem transport_comp (first : SetRel Source Middle) (second : SetRel Middle Target)
    (graph : Graph Context Source) :
    transport (first ○ second) graph = transport second (transport first graph) := by
  simp only [transport, onSpan_comp, SetRel.comp_assoc]

theorem transport_mono {first first' : SetRel Source Target} {graph graph' : Graph Context Source}
    (hrel : first ⊆ first') (hgraph : graph ⊆ graph') :
    transport first graph ⊆ transport first' graph' :=
  Proofs.transport_mono hrel hgraph

@[simp] theorem map_id (graph : Graph Context Source) : map id graph = graph :=
  transport_id graph

theorem map_comp (first : Source → Middle) (second : Middle → Target) (graph : Graph Context Source) :
    map (second ∘ first) graph = map second (map first graph) := by
  simp only [map, Function.graph_comp, transport_comp]

@[simp] theorem pointwise_id : pointwise (SetRel.id : SetRel Source Source) = SetRel.id := by
  ext ⟨left, right⟩
  simp [pointwise]

theorem pointwise_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    pointwise (first ○ second) = pointwise first ○ pointwise second :=
  Proofs.pointwise_comp first second

theorem pointwise_mono {first second : SetRel Source Target} (h : first ⊆ second) :
    pointwise first ⊆ pointwise second := fun _ aligned => List.Forall₂.imp (fun _ _ hab => h hab) aligned

theorem pointwise_append {rel : SetRel Source Target} {left right left' right'}
    (first : (left, right) ∈ pointwise rel) (second : (left', right') ∈ pointwise rel) :
    (left ++ left', right ++ right') ∈ pointwise rel := List.rel_append first second

theorem blocks_mono {first second : Graph (Context × Nat) Source}
    (h : first ⊆ second) (ends : Context → Nat → Source → Prop) (fuel : Nat) :
    blocks first ends fuel ⊆ blocks second ends fuel :=
  Proofs.blocks_mono h ends fuel

theorem path_bounds {decoder : Graph (Context × Nat) Source} {ends : Context → Nat → Source → Prop}
    {fuel ctx addr bytes code span} (path : Path decoder ends fuel ctx addr bytes code span) :
    0 < code.length ∧ code.length ≤ fuel ∧ code.length ≤ span ∧ span ≤ bytes.length :=
  Proofs.path_bounds path

theorem blocks_deterministic {decoder : Graph (Context × Nat) Source} (unique : Deterministic decoder)
    (ends : Context → Nat → Source → Prop) (fuel : Nat) : Deterministic (blocks decoder ends fuel) :=
  Proofs.blocks_deterministic unique ends fuel

/-- Each factored block is a successful legacy sequential decode on exactly the
claimed byte prefix. The converse is not required: a prefix can lack an exit. -/
theorem blocks_subset_sequentialPrefixes (decoder : Decoder Source) (ends : Context → Nat → Source → Prop)
    (fuel : Nat) : blocks (ofDecoder decoder) ends fuel ⊆ sequentialPrefixes decoder fuel :=
  Proofs.blocks_subset_sequentialPrefixes decoder ends fuel

@[simp] theorem rebase_id {Base Observation : Type*} (machine : Observed Base Observation) :
    rebase SetRel.id machine = machine := SetRel.id_comp _

theorem rebase_comp {Input Base Intermediate Observation : Type*} (first : SetRel Input Intermediate)
    (second : SetRel Intermediate Base) (machine : Observed Base Observation) :
    rebase (first ○ second) machine = rebase first (rebase second machine) := SetRel.comp_assoc ..

/-- Observable refinement by inclusion on a shared base transports to the
new inputs. This statement alone does not imply availability of observations. -/
theorem rebase_mono {Input Base Observation : Type*} {first second : SetRel Input Base}
    {lower upper : Observed Base Observation} (adapters : first ⊆ second) (refines : lower ⊆ upper) :
    rebase first lower ⊆ rebase second upper := SetRel.comp_subset_comp adapters refines

/-- Horizontal composition of comparisons commutes with their vertical
composition. The two composites are equal as proofs of inclusion in the same
relation hom-poset, not as executable witnesses or traces. -/
theorem rebase_interchange {Input Base Observation : Type*} {first middle last : SetRel Input Base}
    {lower mid upper : Observed Base Observation}
    (firstAdapter : first ⊆ middle) (secondAdapter : middle ⊆ last)
    (firstModel : lower ⊆ mid) (secondModel : mid ⊆ upper) :
    (rebase_mono firstAdapter firstModel).trans (rebase_mono secondAdapter secondModel) =
      rebase_mono (firstAdapter.trans secondAdapter) (firstModel.trans secondModel) :=
  Subsingleton.elim _ _

/-- If every possible decoded input has an observation, the rebased machine
has an observation exactly on the domain of the adapter. -/
theorem dom_rebase_of_covered {Input Base Observation : Type*} (adapter : SetRel Input Base)
    (machine : Observed Base Observation) (available : adapter.cod ⊆ machine.dom) :
    (rebase adapter machine).dom = adapter.dom :=
  Proofs.dom_rebase_of_covered adapter machine available

end Silmaril.Machine.DecodeGraph
