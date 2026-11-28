module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Proofs

open CategoryTheory
open RVSDG (Origin Port Tuple)
open Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Diamond.Institution (PortMap mapBody mapOrigin mapGraph pullInput pullInput_get
  denote_mapBody observe_mapGraph)
open Memory.Forwarding (originKey originKey_injective)
open Memory.Forwarding.Disjoint (Certificate cell)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition run lowerDiamond_entryTransition)

variable {args target : List ValueSort} {cells : Nat}
variable {facts : AddressContract args} {mapped : AddressContract target}

private theorem port_eq {p q : Port args .address} (index : p.index = q.index) : p = q :=
  Origin.arg.inj (originKey_injective (past := [])
    (x := .arg p) (y := .arg q) (congrArg Sum.inl index))

private theorem matches_iff (facts : AddressContract args) (port : Port args .address) :
    facts.disjoint.matches (past := []) (.arg port) = true ↔ port = facts.disjoint.observed := by
  change (port.index == facts.disjoint.observed.index) = true ↔ _
  exact ⟨fun h => port_eq (beq_iff_eq.mp h), fun h => by simp [h]⟩

private theorem covers_iff (facts : AddressContract args) (port : Port args .address) :
    facts.disjoint.covers (past := []) (.arg port) = true ↔ port ∈ facts.disjoint.writers := by
  simp only [Certificate.covers, List.any_eq_true, beq_iff_eq]
  refine ⟨?_, fun h => ⟨port, h, rfl⟩⟩
  rintro ⟨other, member, index⟩
  exact (port_eq index).symm ▸ member

private theorem same_iff (facts : AddressContract args) (port : Port args .address) :
    facts.same port = true ↔ port = facts.disjoint.observed ∨ port ∈ facts.aliases := by
  simp only [AddressContract.same, Bool.or_eq_true_iff, matches_iff, List.any_eq_true, beq_iff_eq]
  refine or_congr_right ⟨?_, fun h => ⟨port, h, rfl⟩⟩
  rintro ⟨other, member, index⟩
  exact (port_eq index).symm ▸ member

private theorem transport_checked (rename : PortMap args target)
    (accepted : facts.transport rename = some mapped) :
    (facts.mapPorts rename).consistent = true ∧ mapped = facts.mapPorts rename := by
  simp only [AddressContract.transport] at accepted
  split at accepted
  · exact ⟨by assumption, (Option.some.inj accepted).symm⟩
  · contradiction

theorem transport_refuses_collapse (rename : PortMap args target) (port : Port args .address)
    (required : port ∈ facts.disjoint.writers)
    (collapsed : rename port = rename facts.disjoint.observed ∨
      ∃ other ∈ facts.aliases, rename port = rename other) :
    facts.transport rename = none := by
  have conflict : (facts.mapPorts rename).same (rename port) = true := by
    apply (same_iff _ _).mpr
    rcases collapsed with same | ⟨other, member, same⟩
    · exact Or.inl same
    · exact Or.inr (same.symm ▸ List.mem_map_of_mem (f := fun p => rename p) member)
  have inconsistent : ¬ (facts.mapPorts rename).consistent = true := by
    intro consistent
    have member : rename port ∈ (facts.mapPorts rename).disjoint.writers :=
      List.mem_map_of_mem (f := fun p => rename p) required
    have distinct := List.all_eq_true.mp consistent (rename port) member
    simp [conflict] at distinct
  simp [AddressContract.transport, inconsistent]

theorem valid_transport (rename : PortMap args target) (accepted : facts.transport rename = some mapped)
    (input : Tuple (Val cells) target) :
    mapped.Valid input ↔ facts.Valid (pullInput rename input) := by
  rw [(transport_checked rename accepted).2]
  simp only [AddressContract.Valid, AddressContract.mapPorts, Certificate.Valid,
    cell, pullInput_get, List.forall_mem_map]

private theorem checkTail_map (rename : PortMap args target)
    (consistent : (facts.mapPorts rename).consistent = true)
    {past : List (List ValueSort)} {live : Nat} (body : Memory.Body args past live)
    (accepted : checkTail facts body = true) :
    checkTail (facts.mapPorts rename) (mapBody rename body) = true := by
  have cover (port : Port args .address)
      (covered : facts.disjoint.covers (past := []) (.arg port) = true) :
      (facts.mapPorts rename).disjoint.covers (past := []) (.arg (rename port)) = true :=
    (covers_iff _ _).mpr (List.mem_map_of_mem (f := fun p => rename p) ((covers_iff _ _).mp covered))
  induction body with
  | ret => contradiction
  | load _ address rest ih =>
    cases address with
    | output => contradiction
    | arg reader =>
      obtain ⟨covered, next⟩ := Bool.and_eq_true_iff.mp accepted
      exact Bool.and_eq_true_iff.mpr ⟨cover reader covered, ih next⟩
  | store _ address _ rest ih =>
    cases address with
    | output => contradiction
    | arg writer =>
      by_cases same : facts.same writer = true
      · have mappedSame : (facts.mapPorts rename).same (rename writer) = true := by
          apply (same_iff _ _).mpr
          rcases (same_iff _ _).mp same with h | h
          · exact Or.inl (congrArg (fun p => rename p) h)
          · exact Or.inr (List.mem_map_of_mem (f := fun p => rename p) h)
        simp [mapBody, mapOrigin, checkTail, mappedSame]
      · simp only [checkTail, ite_eq_right same] at accepted
        obtain ⟨covered, next⟩ := Bool.and_eq_true_iff.mp accepted
        have mappedCovered := cover writer covered
        have distinct := List.all_eq_true.mp consistent (rename writer) ((covers_iff _ _).mp mappedCovered)
        have mappedDifferent : ¬ (facts.mapPorts rename).same (rename writer) = true := by
          intro equal
          simp [equal] at distinct
        simp [mapBody, mapOrigin, checkTail, mappedDifferent, mappedCovered, ih next]

private theorem mapBody_reindexMemory (rename : PortMap args target)
    {past : List (List ValueSort)} {live : Nat} (body : Memory.Body args past live) (version : Nat) :
    mapBody rename (Memory.DeadStore.reindexMemory body version) =
      Memory.DeadStore.reindexMemory (mapBody rename body) version := by
  induction body generalizing version <;> simp [mapBody, Memory.DeadStore.reindexMemory, *]

private theorem cutWith_map (rename : PortMap args target)
    (consistent : (facts.mapPorts rename).consistent = true)
    {past : List (List ValueSort)} {live version : Nat} {body retained : Memory.Body args past live}
    {selected : PrefixStore args}
    (accepted : Load.cutWith (fun store {_ _} tail =>
      facts.disjoint.matches (past := []) (.arg store.address) && checkTail facts tail) version body =
      some (selected, retained)) :
    Load.cutWith (fun store {_ _} tail =>
      (facts.mapPorts rename).disjoint.matches (past := []) (.arg store.address) &&
      checkTail (facts.mapPorts rename) tail) version (mapBody rename body) =
      some (mapStore rename selected, mapBody rename retained) := by
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
          next checked =>
            obtain ⟨matched, safe⟩ := Bool.and_eq_true_iff.mp checked
            have mappedMatch : (facts.mapPorts rename).disjoint.matches (past := []) (.arg (rename address)) =
                true := (matches_iff _ _).mpr (congrArg (fun p => rename p) ((matches_iff _ _).mp matched))
            cases Option.some.inj accepted
            simp [mapBody, mapOrigin, Load.cutWith, chosen, mappedMatch, checkTail_map rename consistent rest safe,
              mapStore, mapBody_reindexMemory]
          next => contradiction
        · simp only [Load.cutWith, ite_eq_right chosen] at accepted
          obtain ⟨⟨_, _⟩, checked, rebuilt⟩ := Option.map_eq_some_iff.mp accepted
          cases rebuilt
          simp only [mapBody, mapOrigin, Load.cutWith, ite_eq_right chosen, ih checked, Option.map_some]

theorem cut_transport (rename : PortMap args target) (transported : facts.transport rename = some mapped)
    {entry retained : Memory.Graph args} {selected : PrefixStore args} {version : Nat}
    (accepted : cut facts version entry = some (selected, retained)) :
    cut mapped version (mapBody rename entry) = some (mapStore rename selected, mapBody rename retained) := by
  obtain ⟨consistent, rfl⟩ := transport_checked rename transported
  unfold cut at accepted
  split at accepted
  · simpa only [cut, ite_eq_left consistent] using cutWith_map rename consistent accepted
  · contradiction

theorem lower_observations {P Q : EntrySignature} (h : P ⟶ Q) (graph : Graph P.args) (entry : Memory.Graph P.args)
    {facts : AddressContract P.args} {mapped : AddressContract Q.args} (version : Nat)
    (transported : facts.transport (EntrySignature.Hom.port h) = some mapped)
    (input : Tuple (Val cells) Q.args) (valid : mapped.Valid input)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let pulled := pullInput (EntrySignature.Hom.port h) input
    let source := lower cells graph entry version facts
    let target := lower cells (mapGraph h graph) (mapBody (EntrySignature.Hom.port h) entry) version mapped
    entryTransition target.optimized input guard initial = entryTransition source.optimized pulled guard initial ∧
      run target.optimized input guard fuel initial = run source.optimized pulled guard fuel initial := by
  let rename : PortMap P.args Q.args := EntrySignature.Hom.port h
  let pulled := pullInput rename input
  have sourceValid : facts.Valid pulled := (valid_transport rename transported input).mp valid
  have entered : Memory.Graph.denote (mapBody (EntrySignature.Hom.port h) entry) input initial.cell =
      entry.denote pulled initial.cell :=
    denote_mapBody rename entry input PUnit.unit initial.cell
  have returned : (mapGraph h graph).denote guard input (entry.denote pulled initial.cell).2 =
      graph.denote guard pulled (entry.denote pulled initial.cell).2 :=
    observe_mapGraph h (⟨cells, input⟩ : EntryModel Q) graph guard _
  dsimp only
  constructor
  · rw [lower_entryTransition_eq _ _ _ none valid guard initial,
      lower_entryTransition_eq _ _ _ none sourceValid guard initial]
    simp only [lower, lowerDiamond_entryTransition]
    rw [entered]
    rfl
  · rw [(lower_runs _ _ _ none valid guard fuel initial).2,
      (lower_runs _ _ _ none sourceValid guard fuel initial).2, entered, returned]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Proofs
