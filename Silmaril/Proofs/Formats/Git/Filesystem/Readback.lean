module

public import Silmaril.Formats.Git.Filesystem.Writer.Thms
public import Silmaril.Formats.Git.Filesystem.Thms
public import Silmaril.Formats.Dasl.Wire.Canonical.Thms
public import Silmaril.Formats.Dasl.Prolly.Route.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Filesystem

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey Stored routedLookup routedLookup_build_complete)
open Silmaril.Formats.Dasl.Wire (Profile bdasl_roundtrip)
open Silmaril.Formats.Git.Arena (Read)
open Silmaril.Semantics.Prolly (build replayAddress blockOccurrences)

private theorem scan_exact {Index Error : Type} [DecidableEq Index] {Value : Index → Type} :
    ∀ (items : List Index) (visit : (index : Index) → index ∈ items → Except Error (Value index))
      (target : (index : Index) → index ∈ items → Value index),
      Translate.Graph.scan items visit = .ok target ↔
        ∀ index hit, visit index hit = .ok (target index hit) := by
  intro items
  induction items with
  | nil =>
    intro visit target
    have unique (other : (index : Index) → index ∈ [] → Value index) : other = target :=
      funext fun _ => funext fun hit => (List.not_mem_nil hit).elim
    exact ⟨fun _ _ hit => (List.not_mem_nil hit).elim, fun _ => congrArg Except.ok (unique _)⟩
  | cons first rest ih =>
    intro visit target
    let tailVisit := fun index hit => visit index (List.mem_cons_of_mem first hit)
    let tailTarget := fun index hit => target index (List.mem_cons_of_mem first hit)
    let combine (value : Value first) (tail : (index : Index) → index ∈ rest → Value index)
        (index : Index) (hit : index ∈ first :: rest) : Value index :=
      if same : index = first then same.symm ▸ value else tail index ((List.mem_cons.mp hit).resolve_left same)
    have step : Translate.Graph.scan (first :: rest) visit = (do
        let value ← visit first List.mem_cons_self
        let tail ← Translate.Graph.scan rest tailVisit
        pure (combine value tail)) := rfl
    constructor
    · intro done
      cases front : visit first List.mem_cons_self with
      | error fault => simp [step, front, Bind.bind, Except.bind] at done
      | ok value =>
        cases back : Translate.Graph.scan rest tailVisit with
        | error fault => simp [step, front, back, Bind.bind, Except.bind] at done
        | ok tail =>
          have combined : combine value tail = target := Except.ok.inj (by
            simpa only [step, front, back, Bind.bind, Except.bind, pure, Except.pure] using done)
          intro index hit
          by_cases same : index = first
          · subst index
            rw [← combined]
            simpa [combine] using front
          · rw [← combined]
            simpa [combine, same] using (ih tailVisit tail).mp back index ((List.mem_cons.mp hit).resolve_left same)
    · intro ok
      have back := (ih tailVisit tailTarget).mpr (fun index hit => ok index (List.mem_cons_of_mem first hit))
      simp only [step, ok first List.mem_cons_self, back, Bind.bind, Except.bind, pure, Except.pure]
      apply congrArg Except.ok
      funext index hit
      by_cases same : index = first
      · subst index; simp [combine]
      · simp [combine, same, tailTarget]

private def treeImage {hash : Hash} {keys : Finset ByteKey} {modes : ↥keys → EntryMode}
    (root : Image hash .tree) (images : (child : ↥keys) → Image hash (modes child).kind) : Image hash .tree :=
  let order := keys.attach.sort (· ≤ ·)
  let descendants := order.attach.flatMap fun child => (images child.val).writes
  { root with descendants := root.descendants ++ descendants }

private theorem stage_tree_iff {hash : Hash} {Ref Meta : Type} {keys : Finset ByteKey} {modes : ↥keys → EntryMode}
    {children : (child : ↥keys) → Object ByteKey Ref Meta (modes child).kind} {image : Image hash .tree} :
    stage hash (.tree keys modes children) = .ok image ↔
      ∃ (images : (child : ↥keys) → Image hash (modes child).kind) (root : Image hash .tree),
        (∀ child, Dasl.validByteComponent child.val = true ∧ modes child ≠ .gitlink ∧
          stage hash (children child) = .ok (images child)) ∧
        stageDirectory hash (namedDirectory modes fun child => (images child).name) = .ok root ∧
        treeImage root images = image := by
  let order := keys.attach.sort (· ≤ ·)
  have member (child : ↥keys) : child ∈ order := (Finset.mem_sort _).mpr (Finset.mem_attach _ _)
  let visit : (child : ↥keys) → child ∈ order → Except ImportFault (Image hash (modes child).kind) := fun child _ => do
    if !Dasl.validByteComponent child.val then throw (.component child.val)
    if modes child = .gitlink then throw (.gitlink child.val)
    stage hash (children child)
  have runTree : stage hash (.tree keys modes children) = (do
      let read ← Translate.Graph.scan order visit
      let images := fun child => read child (member child)
      let root ← stageDirectory hash (namedDirectory modes fun child => (images child).name)
      pure (treeImage root images)) := by rw [stage]; rfl
  rw [runTree]
  constructor
  · intro staged
    cases scanned : Translate.Graph.scan order visit with
    | error fault => simp [scanned, Bind.bind, Except.bind] at staged
    | ok read =>
      let images := fun child => read child (member child)
      rw [scanned] at staged
      change (stageDirectory hash (namedDirectory modes fun child => (images child).name) >>= fun root =>
        Except.ok (treeImage root images)) = .ok image at staged
      cases made : stageDirectory hash (namedDirectory modes fun child => (images child).name) with
      | error fault => simp [made, Bind.bind, Except.bind] at staged
      | ok root =>
        refine ⟨images, root, ?_, made, ?_⟩
        · intro child
          have got := (scan_exact order visit read).mp scanned child (member child)
          by_cases valid : Dasl.validByteComponent child.val = true <;> by_cases localMode : modes child = .gitlink <;>
            simp [visit, valid, localMode, throw, throwThe, Bind.bind, Except.bind] at got
          exact ⟨valid, localMode, got⟩
        · simpa [made, Bind.bind, Except.bind] using staged
  · rintro ⟨images, root, each, made, rfl⟩
    have scan : Translate.Graph.scan order visit = .ok (fun child _ => images child) :=
      (scan_exact order visit _).mpr fun child _ => by
        obtain ⟨valid, localMode, hit⟩ := each child
        simp [visit, valid, localMode, hit]
    simp [scan, made, Bind.bind, Except.bind, pure, Except.pure]

theorem stage_of_bounds {hash : Hash} {Ref Meta : Type} {kind : Kind} {tree : Object ByteKey Ref Meta kind}
    (bounds : StageBounds hash tree) : ∃ image, stage hash tree = .ok image := by
  induction tree with
  | blob bytes => exact ⟨⟨bytes, []⟩, rfl⟩
  | ref kind name => exact False.elim bounds
  | commit tree count parents metadata ihTree ihParent => exact False.elim bounds
  | tree keys modes children ih =>
    obtain ⟨each, buildBound⟩ := bounds
    choose images staged using fun child => ih child (each child).2.2
    obtain ⟨root, made, _⟩ := stageDirectory_of_bounds (buildBound images staged)
    exact ⟨treeImage root images, stage_tree_iff.mpr ⟨images, root,
      fun child => ⟨(each child).1, (each child).2.1, staged child⟩, made, rfl⟩⟩

theorem directory_readback {hash : Hash} {directory : ByteDirectory} {image : Image hash .tree}
    {fetch : Cid → Option ByteArray} (stageOK : image.OfDirectory directory) (bounds : DirectoryBounds hash directory)
    (covered : image.Covered fetch) {key : ByteKey} {fuel : Nat} (enough : (build policy directory.ordered).level < fuel) :
    routedLookup dirCodec (dirRead hash (.ofPublished fetch)) policy.width fuel image.name key =
      .ok (directory.ordered.lookup? key) := by
  let reader := dirRead hash (.ofPublished fetch)
  let built := build policy directory.ordered
  let name := replayAddress (dirProfile hash).nameBlock? image.name
  let reference : Silmaril.Formats.Dasl.Store Cid := ⟨fun name value => reader name = .found value, fun _ _ => False⟩
  have stored : Stored dirCodec name built reference := by
    intro block member
    obtain ⟨wire, rendered, addressed, included⟩ := stageOK.2 block member
    have tag := laneMatches_address hash .object image.bytes
    obtain ⟨value, encoded, encodable⟩ := (bounds image.name tag block member).encode
    obtain ⟨serialize, parse⟩ := bdasl_roundtrip value encodable
    have exactWire : wire = (Silmaril.Formats.Dasl.Wire.canonicalBdaslModel value).encode.toByteArray := by
      apply Option.some.inj
      simpa only [blockBytes?, encoded, Option.bind_some, serialize] using rendered.symm
    have fetches : fetch (name block) = some wire := covered _ included
    refine ⟨value, encoded, ?_⟩
    change reader (name block) = .found value
    change name block = address hash .object wire at addressed
    rw [addressed] at fetches ⊢
    have verified : readVerified hash (Store.ofPublished fetch) .object (address hash .object wire) = .found wire := by
      simp [readVerified, Store.ofPublished, Read.andThen, fetches]
    have decoded : Profile.bdasl.parse? wire = some value := by rw [exactWire]; exact parse
    simp [reader, dirRead, verified, decoded]
  have exactName : built.rootName name = image.name := stageOK.1
  rw [← exactName]
  exact routedLookup_build_complete policy directory.ordered (stored.pathReads (read := reader) (fun {_ _} hit => hit) key) enough

private theorem covered_tree_root {hash : Hash} {keys : Finset ByteKey} {modes : ↥keys → EntryMode}
    {root : Image hash .tree} {images : (child : ↥keys) → Image hash (modes child).kind} {fetch : Cid → Option ByteArray}
    (covered : (treeImage root images).Covered fetch) : root.Covered fetch := by
  intro pair hit
  apply covered
  rcases List.mem_cons.mp hit with same | tail
  · exact List.mem_cons.mpr (.inl same)
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ tail)

private theorem covered_tree_child {hash : Hash} {keys : Finset ByteKey} {modes : ↥keys → EntryMode}
    {root : Image hash .tree} {images : (child : ↥keys) → Image hash (modes child).kind} {fetch : Cid → Option ByteArray}
    (covered : (treeImage root images).Covered fetch) (child : ↥keys) : (images child).Covered fetch := by
  intro pair hit
  apply covered
  let order := keys.attach.sort (· ≤ ·)
  have member : child ∈ order := (Finset.mem_sort _).mpr (Finset.mem_attach _ _)
  change pair ∈ (root.name, root.bytes) :: (root.descendants ++ order.attach.flatMap fun index => (images index.val).writes)
  exact List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨⟨child, member⟩, List.mem_attach _ _, hit⟩))

theorem readback_of_stage {hash : Hash} {Ref Meta : Type} {kind : Kind} {tree : Object ByteKey Ref Meta kind}
    {image : Image hash kind} {fetch : Cid → Option ByteArray} (bounds : StageBounds hash tree)
    (staged : stage hash tree = .ok image) (covered : image.Covered fetch) :
    Readback hash (.ofPublished fetch) tree image.name := by
  induction tree with
  | ref kind name => exact False.elim bounds
  | commit tree count parents metadata ihTree ihParent => exact False.elim bounds
  | blob bytes =>
    have same : (⟨bytes, []⟩ : Image hash .blob) = image := Except.ok.inj staged
    subst image
    have present : fetch (address hash .raw bytes) = some bytes := covered _ List.mem_cons_self
    simp [Readback, Image.name, kindLane, readVerified, Store.ofPublished, Read.andThen, present]
  | tree keys modes children ih =>
    obtain ⟨images, root, each, made, rfl⟩ := stage_tree_iff.mp staged
    obtain ⟨every, directoryBounds⟩ := bounds
    refine ⟨fun child => (images child).name, ?_, ?_⟩
    · intro key fuel enough
      exact directory_readback (stageDirectory_of_ok made) (directoryBounds images (fun child => (each child).2.2))
        (covered_tree_root covered) enough
    · intro child
      obtain ⟨component, mode, done⟩ := each child
      have childBounds := every child
      exact ⟨component, mode, laneMatches_address _ _ _, ih child childBounds.2.2 done (covered_tree_child covered child)⟩

end Silmaril.Proofs.Formats.Git.Filesystem
