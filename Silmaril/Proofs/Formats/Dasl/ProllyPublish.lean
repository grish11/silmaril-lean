module

public import Silmaril.Formats.Dasl.Prolly.Publish.Defs
public import Silmaril.Semantics.Naming.Admission.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyPublish

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly
open Silmaril.Semantics.Naming
open Silmaril.Semantics.Prolly (Block blockOccurrences)

variable {Name Key Payload : Type} [DecidableEq Name]

private theorem prepare_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {wire : Encode.PartialCodec (Shallow Name) ByteArray} {address : Block Name Key Payload → Name}
    {hash : ByteArray → Name} {block : Block Name Key Payload} {write : Name × ByteArray}
    (accepted : prepareBlock codec wire address hash block = .ok write) :
    write.1 = address block ∧ hash write.2 = write.1 ∧
      ∃ value, codec.encode? block = some value ∧ wire.encode? value = some write.2 := by
  cases enc : codec.encode? block with
  | none => simp [prepareBlock, enc] at accepted
  | some value =>
    cases ser : wire.encode? value with
    | none => simp [prepareBlock, enc, ser] at accepted
    | some bytes =>
      by_cases eq : hash bytes = address block
      · have same : write = (address block, bytes) := by simpa [prepareBlock, enc, ser, eq] using accepted.symm
        exact same.symm ▸ ⟨rfl, eq, value, rfl, ser⟩
      · simp [prepareBlock, enc, ser, eq] at accepted

private theorem mapM_hits {Input Output Error : Type} {prepare : Input → Except Error Output}
    {inputs : List Input} {outputs : List Output} (accepted : inputs.mapM prepare = .ok outputs) :
    (∀ input ∈ inputs, ∃ output ∈ outputs, prepare input = .ok output) ∧
      (∀ output ∈ outputs, ∃ input ∈ inputs, prepare input = .ok output) := by
  induction inputs generalizing outputs with
  | nil => have eq : outputs = [] := (Except.ok.inj accepted).symm; simp [eq]
  | cons input rest ih =>
    cases step : prepare input with
    | error fault => simp [List.mapM_cons, step, Bind.bind, Except.bind] at accepted
    | ok output =>
      cases tail : rest.mapM prepare with
      | error fault => simp [List.mapM_cons, step, tail, Bind.bind, Except.bind] at accepted
      | ok writes =>
        have eq : outputs = output :: writes := by
          simpa [List.mapM_cons, step, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using accepted.symm
        subst outputs
        obtain ⟨forward, backward⟩ := ih tail
        constructor
        · intro item hit
          rcases List.mem_cons.mp hit with same | later
          · exact ⟨output, by simp, same.symm ▸ step⟩
          · obtain ⟨found, present, agrees⟩ := forward item later
            exact ⟨found, List.mem_cons_of_mem _ present, agrees⟩
        · intro item hit
          rcases List.mem_cons.mp hit with same | later
          · exact ⟨input, by simp, same.symm ▸ step⟩
          · obtain ⟨found, present, agrees⟩ := backward item later
            exact ⟨found, List.mem_cons_of_mem _ present, agrees⟩

theorem publish_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {wire : Encode.PartialCodec (Shallow Name) ByteArray} {address : Block Name Key Payload → Name}
    {hash : ByteArray → Name} {tree : Semantics.Prolly.Tree Key Payload} {read staged : Name → Option ByteArray}
    {root : Name} (blobs : Relation Name ByteArray)
    (accepted : publish codec wire address hash tree read = .ok (root, staged)) :
    root = tree.rootName address ∧ Subset (graph read) (graph staged) ∧
      Stored codec address tree (objectByteView wire staged blobs) ∧
      (HashCompatible hash (graph read) → HashCompatible hash (graph staged)) := by
  unfold publish at accepted
  cases planned : (blockOccurrences address tree.level tree.root).mapM (prepareBlock codec wire address hash) with
  | error fault => simp [planned, Bind.bind, Except.bind] at accepted
  | ok writes =>
    simp only [planned, Bind.bind, Except.bind] at accepted
    cases admitted : admit read writes with
    | error name => simp [admitted] at accepted
    | ok checked =>
      have same : (root, staged) = (tree.rootName address, checked) :=
        (Except.ok.inj (by simpa only [admitted] using accepted)).symm
      cases same
      obtain ⟨forward, backward⟩ := mapM_hits planned
      refine ⟨rfl, admit_preserves admitted, ?_, ?_⟩
      · intro block hit
        obtain ⟨⟨name, bytes⟩, present, prepared⟩ := forward block hit
        obtain ⟨eq, _, value, encoded, serialized⟩ := prepare_sound prepared
        change name = address block at eq
        subst name
        refine ⟨value, encoded, Option.bind_eq_some_iff.mpr ⟨bytes, ?_, wire.recovers serialized⟩⟩
        show graph staged (address block) bytes
        rw [admit_eq_union admitted]
        exact Or.inr present
      · intro old name bytes present
        rw [admit_eq_union admitted] at present
        rcases present with previous | new
        · exact old previous
        · obtain ⟨_, _, prepared⟩ := backward (name, bytes) new
          exact (prepare_sound prepared).2.1

end Silmaril.Proofs.Formats.Dasl.ProllyPublish
