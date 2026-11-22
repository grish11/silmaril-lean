module

public import Silmaril.Formats.Git.Filesystem.Writer.Defs
public import Silmaril.Formats.Git.Filesystem.Thms
public import Silmaril.Formats.Dasl.Wire.Canonical.Thms
public import Silmaril.Semantics.Prolly.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Filesystem

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Filesystem
open Silmaril.Semantics.Prolly
open Silmaril.Formats.Dasl.Wire (bdasl_roundtrip)

theorem blockBounds_encode {block : DirBlock} (bounds : BlockBounds block) :
    ∃ value, dirCodec.encode? block = some value ∧ Silmaril.Formats.Dasl.Wire.BdaslEncodable value := by
  have encoded : ∃ value, dirCodec.encode? block = some value := by
    cases block with
    | leaf entries =>
      simp [dirCodec, Formats.Dasl.Prolly.blockCodec_encode, Formats.Dasl.Prolly.encodeBlock]
    | branch level children =>
      have fit : 0 < level ∧ level < 2 ^ 63 := bounds.1
      simp only [dirCodec, Formats.Dasl.Prolly.blockCodec_encode, Formats.Dasl.Prolly.encodeBlock, fit]
      exact ⟨_, rfl⟩
  obtain ⟨value, hit⟩ := encoded
  exact ⟨value, hit, bounds.2 value hit⟩

private theorem namedBlock {hash : Hash} {block : DirBlock} {name : Cid} :
    (dirProfile hash).nameBlock? block = some name ↔
      ∃ bytes, blockBytes? block = some bytes ∧ address hash .object bytes = name := by
  simp only [Formats.Dasl.Prolly.RootProfile.nameBlock?, dirProfile, Formats.Dasl.Prolly.RootProfile.ofTotalHash,
    blockBytes?, dirCodec, Formats.Dasl.Prolly.blockCodec_encode, Option.bind_eq_some_iff, Function.comp_apply,
    Option.some.injEq]

private theorem occurrences_head {Name Key Payload : Type} (name : Block Name Key Payload → Name)
    (tree : Tree Key Payload) : blockOccurrences name tree.level tree.root =
      nodeBlock name tree.level tree.root :: (blockOccurrences name tree.level tree.root).drop 1 := by
  rcases tree with ⟨level, node⟩
  cases level <;> rfl

private theorem collectWrites {Block Write Error : Type} {emit : Block → Except Error Write} {spec : Block → Write → Prop}
    (blocks : List Block) (valid : ∀ block ∈ blocks, ∃ value, emit block = .ok value ∧ spec block value) :
    ∃ writes, blocks.mapM emit = .ok writes ∧ ∀ block ∈ blocks, ∃ value ∈ writes, spec block value := by
  induction blocks with
  | nil => exact ⟨[], rfl, fun _ hit => (List.not_mem_nil hit).elim⟩
  | cons head rest ih =>
    obtain ⟨value, computed, exactValue⟩ := valid head List.mem_cons_self
    obtain ⟨tail, ran, all⟩ := ih (fun block member => valid block (List.mem_cons_of_mem _ member))
    refine ⟨value :: tail, ?_, ?_⟩
    · simp [computed, ran, pure, Except.pure, Bind.bind, Except.bind]
    · intro block member
      rcases List.mem_cons.mp member with same | deeper
      · exact ⟨value, List.mem_cons_self, same.symm ▸ exactValue⟩
      · obtain ⟨write, inside, sound⟩ := all block deeper
        exact ⟨write, List.mem_cons_of_mem _ inside, sound⟩

theorem stageDirectory_of_root {hash : Hash} {directory : ByteDirectory} {root : Cid}
    (named : (build policy directory.ordered).rootName? (dirProfile hash).nameBlock? = some root) :
    ∃ image, stageDirectory hash directory = .ok image ∧ image.OfDirectory directory := by
  let tree := build policy directory.ordered
  let name := replayAddress (dirProfile hash).nameBlock? root
  let head := nodeBlock name tree.level tree.root
  let blocks := blockOccurrences name tree.level tree.root
  have occurrences : blocks = head :: blocks.drop 1 := occurrences_head name tree
  obtain ⟨admitted, sameRoot⟩ := tree.replayAddress_spec (dirProfile hash).nameBlock? root named
  have covers : ∀ block ∈ blocks, ∃ bytes, blockBytes? block = some bytes ∧ name block = address hash .object bytes := by
    intro block member
    obtain ⟨bytes, enc, same⟩ := namedBlock.mp (admitted block member)
    exact ⟨bytes, enc, same.symm⟩
  have headMember : head ∈ blocks := by rw [occurrences]; exact List.mem_cons_self
  obtain ⟨rootBytes, rootEnc, rootAddress⟩ := covers head headMember
  have rootExact : address hash .object rootBytes = root := rootAddress.symm.trans sameRoot
  let emit : DirBlock → Except ImportFault (Cid × ByteArray) := fun block => do
    let some wire := blockBytes? block | .error .encoding
    pure (address hash .object wire, wire)
  let spec : DirBlock → Cid × ByteArray → Prop := fun block write =>
    blockBytes? block = some write.2 ∧ name block = write.1
  obtain ⟨writes, ran, receipts⟩ := collectWrites (emit := emit) (spec := spec) (blocks.drop 1) (by
    intro block member
    obtain ⟨bytes, enc, same⟩ := covers block (List.mem_of_mem_drop member)
    exact ⟨(address hash .object bytes, bytes), by simp [emit, enc, pure, Except.pure], enc, same⟩)
  let image : Image hash .tree := ⟨rootBytes, writes⟩
  refine ⟨image, ?_, ?_⟩
  · simp only [stageDirectory, named]
    rw [show blockBytes? (nodeBlock (replayAddress (dirProfile hash).nameBlock? root)
      (build policy directory.ordered).level (build policy directory.ordered).root) = some rootBytes from rootEnc]
    simp only [rootExact, ne_eq, not_true_eq_false, ite_false]
    change (blocks.drop 1).mapM emit >>= _ = _
    rw [ran]
    rfl
  · have imageName : image.name = root := rootExact
    change tree.rootName (replayAddress (dirProfile hash).nameBlock? image.name) = image.name ∧ _
    rw [show replayAddress (dirProfile hash).nameBlock? image.name = name from congrArg _ imageName]
    refine ⟨rootAddress, ?_⟩
    intro block member
    change block ∈ blocks at member
    rw [occurrences] at member
    rcases List.mem_cons.mp member with same | tail
    · subst block
      refine ⟨rootBytes, rootEnc, rootAddress, ?_⟩
      change (name head, rootBytes) ∈ (image.name, rootBytes) :: writes
      rw [rootAddress]
      exact List.mem_cons_self
    · obtain ⟨⟨cid, bytes⟩, inside, enc, same⟩ := receipts block tail
      obtain ⟨known, encoded, sameAddress⟩ := covers block (List.mem_of_mem_drop tail)
      have bytesEq : bytes = known := Option.some.inj (enc.symm.trans encoded)
      have nameEq : name block = cid := same
      exact ⟨bytes, enc, bytesEq.symm ▸ sameAddress, List.mem_cons_of_mem _ (nameEq.symm ▸ inside)⟩

theorem stageDirectory_of_bounds {hash : Hash} {directory : ByteDirectory} (bounds : DirectoryBounds hash directory) :
    ∃ image, stageDirectory hash directory = .ok image ∧ image.OfDirectory directory := by
  let tree := build policy directory.ordered
  let name := replayAddress (dirProfile hash).nameBlock? (address hash .object ByteArray.empty)
  have admitted : tree.Admits (dirProfile hash).nameBlock? name := by
    intro block member
    obtain ⟨value, enc, valid⟩ := blockBounds_encode
      (bounds _ (laneMatches_address hash .object ByteArray.empty) block member)
    obtain ⟨wire, _⟩ := bdasl_roundtrip value valid
    have encoded : blockBytes? block = some (Silmaril.Formats.Dasl.Wire.canonicalBdaslModel value).encode.toByteArray := by
      simp only [blockBytes?, enc, Option.bind_some, wire]
    have hit := (namedBlock (hash := hash)).mpr ⟨_, encoded, rfl⟩
    unfold name replayAddress
    simp only [hit, Option.getD_some]
  exact stageDirectory_of_root ((tree.rootName?_eq_some_iff _ _).mpr ⟨name, admitted, rfl⟩)

theorem stageDirectory_of_ok {hash : Hash} {directory : ByteDirectory} {image : Image hash .tree}
    (staged : stageDirectory hash directory = .ok image) : image.OfDirectory directory := by
  cases root : (build policy directory.ordered).rootName? (dirProfile hash).nameBlock? with
  | none => simp [stageDirectory, root] at staged
  | some cid =>
    obtain ⟨actual, success, certified⟩ := stageDirectory_of_root root
    exact (Except.ok.inj (success.symm.trans staged)) ▸ certified

end Silmaril.Proofs.Formats.Git.Filesystem
