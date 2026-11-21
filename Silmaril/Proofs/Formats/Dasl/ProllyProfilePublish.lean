module

public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Thms
public import Silmaril.Formats.Dasl.Prolly.Publish.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyProfilePublish

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics.Naming Silmaril.Semantics.Prolly

variable {Name Key Payload Input Output Error : Type} [DecidableEq Name]

private theorem plan {prepare : Input → Except Error Output} (inputs : List Input)
    (ready : ∀ input ∈ inputs, ∃ output, prepare input = .ok output) :
    ∃ outputs, inputs.mapM prepare = .ok outputs ∧
      ∀ output, output ∈ outputs ↔ ∃ input ∈ inputs, prepare input = .ok output := by
  induction inputs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons first rest ih =>
    obtain ⟨head, headOk⟩ := ready first (List.mem_cons_self ..)
    obtain ⟨tail, tailOk, tailIff⟩ := ih (fun input hit => ready input (List.mem_cons_of_mem _ hit))
    refine ⟨head :: tail, by simp [List.mapM_cons, headOk, tailOk, Bind.bind, Except.bind]; rfl, ?_⟩
    intro output
    rw [List.mem_cons, tailIff]
    constructor
    · rintro (rfl | ⟨input, hit, emitted⟩)
      · exact ⟨first, List.mem_cons_self .., headOk⟩
      · exact ⟨input, List.mem_cons_of_mem _ hit, emitted⟩
    · rintro ⟨input, hit, emitted⟩
      rcases List.mem_cons.mp hit with rfl | tailHit
      · exact .inl (Except.ok.inj (emitted.symm.trans headOk))
      · exact .inr ⟨input, tailHit, emitted⟩

private theorem prepared_iff (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (tree : Semantics.Prolly.Tree Key Payload) (address : Block Name Key Payload → Name) (root : Name)
    (admitted : tree.Admits profile.nameBlock? address) {block : Block Name Key Payload}
    (occurs : block ∈ blockOccurrences address tree.level tree.root) (name : Name) (bytes : ByteArray) :
    prepareBlock (blockCodec profile.key profile.payload) reader.codec address
      (fun octets => (profile.hash? octets).getD root) block = .ok (name, bytes) ↔
    name = address block ∧ ∃ value, encodeBlock profile.key profile.payload block = some value ∧
      profile.render? value = some bytes := by
  obtain ⟨value, octets, encoded, rendered, named⟩ := (profile.admits_iff_serializes tree address).mp admitted block occurs
  simp [prepareBlock, encoded, RootProfile.Readback.codec, rendered, named, ← blockCodec_encode, eq_comm]

private theorem plan_exact (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (tree : Semantics.Prolly.Tree Key Payload) (address : Block Name Key Payload → Name) (root : Name)
    (admitted : tree.Admits profile.nameBlock? address) :
    ∃ writes, (blockOccurrences address tree.level tree.root).mapM
        (prepareBlock (blockCodec profile.key profile.payload) reader.codec address
          (fun bytes => (profile.hash? bytes).getD root)) = .ok writes ∧
      listed writes = profile.byteObservations tree address := by
  have ready := fun block hit => (profile.admits_iff_serializes tree address).mp admitted block hit
  obtain ⟨writes, staged, hits⟩ := plan (blockOccurrences address tree.level tree.root) (fun block hit => by
    obtain ⟨value, bytes, encoded, rendered, _⟩ := ready block hit
    exact ⟨(address block, bytes), (prepared_iff profile reader tree address root admitted hit _ _).mpr
      ⟨rfl, value, blockCodec_encode .. ▸ encoded, rendered⟩⟩)
  refine ⟨writes, staged, ?_⟩
  funext name bytes
  apply propext
  change (name, bytes) ∈ writes ↔ _
  rw [hits]
  constructor
  · rintro ⟨block, occurs, emitted⟩
    obtain ⟨named, value, encoded, rendered⟩ := (prepared_iff profile reader tree address root admitted occurs name bytes).mp emitted
    exact ⟨value, ⟨block, ⟨named, occurs⟩, encoded⟩, rendered⟩
  · rintro ⟨value, ⟨block, ⟨named, occurs⟩, encoded⟩, rendered⟩
    exact ⟨block, occurs, (prepared_iff profile reader tree address root admitted occurs name bytes).mpr
      ⟨named, value, encoded, rendered⟩⟩

theorem publishTree_spec (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray) {root : Name}
    (named : tree.rootName? profile.nameBlock? = some root) :
    profile.PublicationSpec reader tree read root (profile.publishTree reader tree read) := by
  let address := replayAddress profile.nameBlock? root
  let hash := fun bytes => (profile.hash? bytes).getD root
  obtain ⟨admitted, rootEq⟩ := tree.replayAddress_spec profile.nameBlock? root named
  obtain ⟨writes, planned, exactWrites⟩ := plan_exact profile reader tree address root admitted
  have commitEq : Prolly.publish (blockCodec profile.key profile.payload) reader.codec address hash tree read =
      match admit read writes with
      | .ok staged => .ok (tree.rootName address, staged)
      | .error name => .error (.collision name) := by
    simp [Prolly.publish, hash, planned, Bind.bind, Except.bind]; rfl
  cases committed : admit read writes with
  | error name =>
    have collision := admit_spec read writes
    simpa [RootProfile.PublicationSpec, RootProfile.publishTree, named, ← exactWrites, commitEq, address, hash,
      committed, Except.mapError] using (show name ∈ collisions (union (graph read) (listed writes)) from by
      simpa [committed] using collision)
  | ok staged =>
    have accepted : Prolly.publish (blockCodec profile.key profile.payload) reader.codec address hash tree read =
        .ok (tree.rootName address, staged) := commitEq.trans (by rw [committed])
    have stored := (publish_sound (fun _ _ => False) accepted).2.2.1
    have exactRaw := (admit_eq_union committed).trans (congrArg (union (graph read)) exactWrites)
    have recovered (block) (occurs : block ∈ blockOccurrences address tree.level tree.root) :
        reader.readBlock? staged (address block) = some block := by
      obtain ⟨value, encoded, decoded⟩ := stored block occurs
      change (staged (address block)).bind reader.decode? = some value at decoded
      simp [RootProfile.Readback.readBlock?, decoded, (blockCodec profile.key profile.payload).recovers encoded]
    have facts : tree.rootName address = root ∧
        graph staged = union (graph read) (profile.byteObservations tree address) ∧ _ :=
      ⟨rootEq, exactRaw, recovered⟩
    simpa [RootProfile.PublicationSpec, RootProfile.publishTree, named, commitEq, address, hash, committed,
      Except.mapError] using facts

omit [DecidableEq Name] in
theorem accepts_iff_of_spec (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray) (root : Name)
    (result : Except (RootProfile.PublishFailure Name) (Name × (Name → Option ByteArray)))
    (specified : profile.PublicationSpec reader tree read root result) :
    (∃ staged, result = .ok (root, staged)) ↔
      Binding (union (graph read) (profile.byteObservations tree (replayAddress profile.nameBlock? root))) := by
  cases result with
  | ok output =>
    obtain ⟨published, staged⟩ := output
    obtain ⟨rfl, rawEq, _⟩ := specified
    exact ⟨fun _ => rawEq ▸ graph_binding staged, fun _ => ⟨staged, rfl⟩⟩
  | error fault =>
    constructor
    · rintro ⟨_, accepted⟩
      cases accepted
    · intro bound
      exfalso
      cases fault with
      | naming => exact specified
      | publishing reason =>
        cases reason with
        | blockEncoding _ | wireEncoding _ | invalidAddress _ => exact specified
        | collision _ =>
          obtain ⟨_, _, left, right, different⟩ := specified
          exact different (bound left right)

end Silmaril.Proofs.Formats.Dasl.ProllyProfilePublish
