module

public import Silmaril.Formats.Dasl.Mst.Publish.Defs
public import Silmaril.Semantics.Naming.Admission.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.MstPublish

open Silmaril.Formats.Dasl.Mst Silmaril.Semantics.Naming

variable {Name : Type}

theorem graph_compatible {profile : PublishProfile Name} {layerOf : Key → Nat} {records : List (Record Name)}
    {built : Built Name} (hit : build layerOf profile.nameNode? records = some built) :
    Subset (profile.byteObservations built) (fun name bytes => profile.name? bytes = some name) := by
  rintro name bytes ⟨node, observed, encoded⟩
  have named := build_names hit observed
  change profile.nodeBytes.encode? node = some bytes at encoded
  simpa [PublishProfile.nameNode?, encoded] using named

private theorem replay_list {profile : PublishProfile Name} (blocks : List (Name × Node Name))
    (total : ∀ pair ∈ blocks, ∃ bytes, profile.nodeBytes.encode? pair.2 = some bytes) :
    ∃ writes, blocks.mapM profile.renderBlock? = some writes ∧
      listed writes = push (listed blocks) (graph profile.nodeBytes.encode?) := by
  induction blocks with
  | nil =>
    refine ⟨[], rfl, ?_⟩
    funext name bytes
    simp [listed, push]
  | cons block rest ih =>
    obtain ⟨bytes, encoded⟩ := total block (.head _)
    obtain ⟨writes, replayed, exactWrites⟩ := ih (fun pair mem => total pair (.tail _ mem))
    refine ⟨(block.1, bytes) :: writes, ?_, ?_⟩
    · simp [List.mapM_cons, PublishProfile.renderBlock?, encoded, replayed]
    · funext name data
      apply propext
      simp only [listed, List.mem_cons]
      change ((name, data) = (block.1, bytes) ∨ listed writes name data) ↔ _
      rw [exactWrites]
      constructor
      · rintro (same | ⟨node, mem, encode⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          exact ⟨block.2, by cases block; exact List.Mem.head _, encoded⟩
        · exact ⟨node, List.Mem.tail _ mem, encode⟩
      · rintro ⟨node, mem, encode⟩
        rcases List.mem_cons.mp mem with same | known
        · obtain ⟨rfl, eq⟩ := Prod.mk.inj same
          exact Or.inl (Prod.ext rfl (Option.some.inj (encode.symm.trans (eq ▸ encoded))))
        · exact Or.inr ⟨_, known, encode⟩

private theorem replay {profile : PublishProfile Name} {layerOf : Key → Nat} {records : List (Record Name)}
    {built : Built Name} (hit : build layerOf profile.nameNode? records = some built) :
    ∃ writes, built.blocks.mapM profile.renderBlock? = some writes ∧ listed writes = profile.byteObservations built := by
  apply replay_list
  intro pair mem
  exact (Option.bind_eq_some_iff.mp (build_names hit mem)).imp (fun _ found => found.1)

theorem publish_spec [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf profile.nameNode? records = some built)
    (read : Name → Option ByteArray) : profile.Spec layerOf records read built (profile.publish layerOf records read) := by
  obtain ⟨writes, rendered, exactWrites⟩ := replay hit
  have admitted := admit_spec read writes
  rw [exactWrites] at admitted
  cases call : admit read writes with
  | error name => simpa [PublishProfile.Spec, PublishProfile.publish, hit, rendered, call] using admitted
  | ok staged =>
    have exactUnion : graph staged = union (graph read) (profile.byteObservations built) := by simpa [call] using admitted
    have decoded : Subset built.observed (profile.reference staged) := by
      intro name node known
      obtain ⟨bytes, encoded, _⟩ := Option.bind_eq_some_iff.mp (build_names hit known)
      have saved : graph staged name bytes := exactUnion ▸ Or.inr ⟨node, known, encoded⟩
      exact ⟨bytes, saved, profile.nodeBytes.recovers encoded⟩
    simpa [PublishProfile.Spec, PublishProfile.publish, hit, rendered, call] using
      And.intro exactUnion (And.intro decoded (build_realizes hit decoded))

theorem publish_accepts_iff [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf profile.nameNode? records = some built)
    (read : Name → Option ByteArray) :
    (∃ root staged, profile.publish layerOf records read = .ok (root, staged)) ↔
      Binding (union (graph read) (profile.byteObservations built)) := by
  obtain ⟨writes, rendered, exactWrites⟩ := replay hit
  rw [← exactWrites, ← admit_exists_iff]
  cases call : admit read writes <;> simp [PublishProfile.publish, hit, rendered, call]

theorem publish_sound [DecidableEq Name] {profile : PublishProfile Name} {layerOf : Key → Nat}
    {records : List (Record Name)} {read staged : Name → Option ByteArray} {root : Name}
    (published : profile.publish layerOf records read = .ok (root, staged)) :
    ∃ built, build layerOf profile.nameNode? records = some built ∧ root = built.root ∧
      graph staged = union (graph read) (profile.byteObservations built) ∧
      Subset built.observed (profile.reference staged) ∧ Realizes layerOf (profile.reference staged) none root records := by
  cases hit : build layerOf profile.nameNode? records with
  | none => simp [PublishProfile.publish, hit] at published
  | some built =>
    have spec := publish_spec hit read
    rw [published] at spec
    exact ⟨built, rfl, spec⟩

theorem read_sound (profile : PublishProfile Name) {read authoritative : Name → Option ByteArray}
    (included : Subset (graph read) (graph authoritative)) :
    ReadSound (profile.readShallow read) (profile.reference authoritative) := by
  intro name value node found decoded
  cases raw : read name with
  | none => simp [PublishProfile.readShallow, raw] at found
  | some bytes =>
    cases parsed : profile.wire.decode? bytes <;> simp [PublishProfile.readShallow, raw, parsed] at found
    subst value
    refine ⟨bytes, included raw, ?_⟩
    change (profile.wire.decode? bytes).bind decodeNode? = some node
    simpa [parsed] using decoded

end Silmaril.Proofs.Formats.Dasl.MstPublish
