module

public import Silmaril.Formats.Dasl.Prolly.Operations.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Thms
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms
public import Silmaril.Semantics.Prolly.Operations.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyOperations

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload Error : Type}

private theorem mapM_exact {Item Result FaultType : Type} {items : List Item} {fetch : Item → Except FaultType Result}
    {truth : Item → Result} (reads : ∀ item ∈ items, fetch item = .ok (truth item)) :
    items.mapM fetch = .ok (items.map truth) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    simp [List.mapM_cons, reads first (by simp), ih (fun item hit => reads item (List.mem_cons_of_mem _ hit)),
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem scan_complete [DecidableEq Key] (read : Name → Except (Fault Name) (Block Name Key Payload))
    (address : Block Name Key Payload → Name) (width level : Nat) (node : Node Key Payload level)
    (separators : Node.Separators level node) (bounded : Node.Bounded width level node)
    (reads : ∀ block ∈ blockOccurrences address level node, read (address block) = .ok block)
    {expected : Option Nat} (expect : expected = none ∨ expected = some level) {fuel : Nat} (enough : level < fuel) :
    scan read width fuel expected (address (nodeBlock address level node)) = .ok (flatten level node) := by
  induction level generalizing fuel expected with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have root := reads (nodeBlock address 0 node) (by simp [blockOccurrences])
      simp only [nodeBlock] at root
      change node.length ≤ width at bounded
      simp [scan, nodeBlock, root, expect, bounded, flatten, Bind.bind, Except.bind]
  | succ level ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have root := reads (nodeBlock address (level + 1) node) (by simp [blockOccurrences])
      have nonempty : 0 < node.length := List.length_pos_iff.mpr separators.1
      have next : level < fuel := by omega
      let fetch : Key × Node Key Payload level → Except (Fault Name) (List (Key × Payload)) := fun child => do
          let entries ← scan read width fuel (some level) (address (nodeBlock address level child.2))
          finishChild (address (nodeBlock address (level + 1) node)) child.1 entries
      have groups : node.mapM fetch = .ok (node.map fun child => flatten level child.2) := by
        apply mapM_exact
        intro child hit
        have childRead := ih child.2 (separators.2 child hit).2 (bounded.2 child hit)
          (fun block seen => reads block (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, hit, seen⟩)))
          (Or.inr rfl) next
        simp [fetch, childRead, finishChild, (separators.2 child hit).1, Bind.bind, Except.bind]
      have fits : node.length ≤ width := bounded.1
      simp only [nodeBlock] at root
      simp only [scan, root, Bind.bind, Except.bind, nodeBlock, Nat.zero_lt_succ, List.length_map,
        expect, nonempty, fits, and_self, ite_true, List.mapM_map, Nat.add_sub_cancel]
      change (node.mapM fetch >>= fun groups => pure groups.flatten) = .ok (flatten (level + 1) node)
      rw [groups]
      simp [flatten, List.flatMap_def, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem acquire_sound [LinearOrder Key] {width fuel : Nat} {tree : TypedMap Key Payload width}
    {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)} {address : Block Name Key Payload → Name}
    {store : Store Name} (stored : Stored codec address tree.val store) (bound : store.Binding)
    {read : Read Name} (sound : Read.Sound read store) {map : OrderedMap Key Payload}
    (ok : acquire codec read width fuel (tree.val.rootName address) = .ok map) :
    map = TypedMap.view tree := by
  unfold acquire at ok
  cases found : scan (readBlock codec read) width fuel none (tree.val.rootName address) with
  | error fault => simp [found, Bind.bind, Except.bind] at ok
  | ok entries =>
    have exactEntries := Silmaril.Formats.Dasl.Prolly.scan_sound address width fuel tree.val.level tree.val.root
      (fun _ hit _ checked => readBlock_sound stored bound sound hit checked) found
    change entries = (TypedMap.view tree).entries at exactEntries
    simpa [found, exactEntries, Bind.bind, Except.bind] using ok.symm

theorem acquire_complete [LinearOrder Key] {width fuel : Nat} (tree : TypedMap Key Payload width)
    (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)) (read : Read Name)
    (address : Block Name Key Payload → Name) (enough : tree.val.level < fuel)
    (reads : WholeReads (readBlock codec read) address tree.val) :
    acquire codec read width fuel (tree.val.rootName address) = .ok (TypedMap.view tree) := by
  have ok := scan_complete (readBlock codec read) address width tree.val.level tree.val.root
    tree.property.1.2 tree.property.2 reads (Or.inl rfl) enough
  change scan (readBlock codec read) width fuel none (tree.val.rootName address) = .ok (TypedMap.view tree).entries at ok
  simp [acquire, ok, Bind.bind, Except.bind]

theorem published_validRoot [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (map : OrderedMap Key Payload) (read : Name → Option ByteArray)
    {root : Name} {staged : Name → Option ByteArray} (named : profile.rootName? map = some root)
    (published : profile.publishMap reader map read = .ok (root, staged)) :
    profile.ValidRoots (reader.objectView staged) root map.lookup? := by
  let tree := build profile.policy map
  let address := replayAddress profile.nameBlock? root
  obtain ⟨admitted, rootEq⟩ := tree.replayAddress_spec profile.nameBlock? root named
  have spec := profile.publishMap_spec reader map read named
  rw [published] at spec
  have exactUnion := spec.2.1
  refine ⟨map, address, fun _ => rfl, admitted, rootEq, ?_⟩
  intro block hit
  obtain ⟨value, bytes, encode, render, _⟩ := (profile.admits_iff_serializes tree address).mp admitted block hit
  have node : profile.byteObservations tree address (address block) bytes :=
    ⟨value, ⟨block, ⟨rfl, hit⟩, by simpa only [blockCodec_encode] using encode⟩, render⟩
  have raw : Naming.graph staged (address block) bytes := by
    rw [exactUnion]
    exact Or.inr node
  exact ⟨value, encode, by
    change reader.shallowRead staged (address block) = .found value
    change staged (address block) = some bytes at raw
    simp [RootProfile.Readback.shallowRead, raw, reader.recovers render]⟩

theorem combineAndPublish_sound [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) {read : Name → Option ByteArray} {fuel : Nat} {reference : Store Name}
    {left right : TypedMap Key Payload profile.policy.width} {leftAddress rightAddress : Block Name Key Payload → Name}
    (leftStored : Stored (blockCodec profile.key profile.payload) leftAddress left.val reference)
    (rightStored : Stored (blockCodec profile.key profile.payload) rightAddress right.val reference)
    (bound : reference.Binding) (sound : Read.Sound (reader.shallowRead read) reference)
    (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Payload Error)
    {root : Name} {staged : Name → Option ByteArray}
    (ok : profile.combineAndPublish reader kind overlap read fuel (left.val.rootName leftAddress)
      (right.val.rootName rightAddress) = .ok (root, staged)) :
    ∃ result : OrderedMap Key Payload,
      (TypedMap.view left).combine kind overlap (TypedMap.view right) = .ok result ∧
      profile.rootName? result = some root ∧
      Naming.graph staged = Naming.union (Naming.graph read)
        (profile.byteObservations (build profile.policy result) (replayAddress profile.nameBlock? root)) ∧
      WholeReads (readBlock (blockCodec profile.key profile.payload) (reader.shallowRead staged))
        (replayAddress profile.nameBlock? root) (build profile.policy result) := by
  unfold RootProfile.combineAndPublish at ok
  dsimp only at ok
  cases leftOk : acquire (blockCodec profile.key profile.payload) (reader.shallowRead read)
      profile.policy.width fuel (left.val.rootName leftAddress) with
  | error fault => simp [leftOk, Except.mapError, Bind.bind, Except.bind] at ok
  | ok leftMap =>
    cases rightOk : acquire (blockCodec profile.key profile.payload) (reader.shallowRead read)
        profile.policy.width fuel (right.val.rootName rightAddress) with
    | error fault => simp [leftOk, rightOk, Except.mapError, Bind.bind, Except.bind] at ok
    | ok rightMap =>
      have leftEq := acquire_sound leftStored bound sound leftOk
      have rightEq := acquire_sound rightStored bound sound rightOk
      cases combined : leftMap.combine kind overlap rightMap with
      | error error => simp [leftOk, rightOk, combined, Except.mapError, Bind.bind, Except.bind] at ok
      | ok result =>
        have published : profile.publishMap reader result read = .ok (root, staged) := by
          cases stage : profile.publishMap reader result read with
          | error failure => simp [leftOk, rightOk, combined, stage, Except.mapError, Bind.bind, Except.bind] at ok
          | ok publication =>
            simpa [leftOk, rightOk, combined, stage, Except.mapError, Bind.bind, Except.bind] using ok
        cases named : profile.rootName? result with
        | none =>
          change (build profile.policy result).rootName? profile.nameBlock? = none at named
          simp [RootProfile.publishMap, RootProfile.publishTree, named] at published
        | some expected =>
          have spec := profile.publishMap_spec reader result read named
          rw [published] at spec
          obtain ⟨same, exactUnion, blockReads⟩ := spec
          subst expected
          refine ⟨result, leftEq ▸ rightEq ▸ combined, named, exactUnion, ?_⟩
          intro block hit
          have decoded := blockReads block hit
          unfold RootProfile.Readback.readBlock? at decoded
          obtain ⟨value, valueHit, blockHit⟩ := Option.bind_eq_some_iff.mp decoded
          obtain ⟨bytes, bytesHit, shallowHit⟩ := Option.bind_eq_some_iff.mp valueHit
          simp [readBlock, RootProfile.Readback.shallowRead, bytesHit, shallowHit, blockHit]

end Silmaril.Proofs.Formats.Dasl.ProllyOperations
