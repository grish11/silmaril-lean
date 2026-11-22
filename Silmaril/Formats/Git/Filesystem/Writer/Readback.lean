module

public import Silmaril.Formats.Git.Filesystem.Writer.Thms
public import Silmaril.Formats.Git.Filesystem.Thms
import Silmaril.Proofs.Formats.Git.Filesystem.Readback

public section

namespace Silmaril.Formats.Git.Filesystem

open Formats.Dasl.Prolly (ByteKey routedLookup)
open Silmaril.Semantics.Prolly (build)

variable {hash : Hash} {Ref Meta : Type} {kind : Kind} {tree : Object ByteKey Ref Meta kind}

/-- Every finite tree in the bounded profile stages. Admission is independent:
even a successfully staged tree can conflict with another binding. -/
theorem stage_of_bounds (bounds : StageBounds hash tree) : ∃ image, stage hash tree = .ok image :=
  Proofs.Formats.Git.Filesystem.stage_of_bounds bounds

theorem Image.directory_readback {directory : ByteDirectory} {image : Image hash .tree} {fetch : Cid → Option ByteArray}
    (staged : image.OfDirectory directory) (bounds : DirectoryBounds hash directory) (covered : image.Covered fetch)
    {key : ByteKey} {fuel : Nat} (enough : (build policy directory.ordered).level < fuel) :
    routedLookup dirCodec (dirRead hash (.ofPublished fetch)) policy.width fuel image.name key =
      .ok (directory.ordered.lookup? key) :=
  Proofs.Formats.Git.Filesystem.directory_readback staged bounds covered enough

theorem readback_of_stage {image : Image hash kind} {fetch : Cid → Option ByteArray}
    (bounds : StageBounds hash tree) (staged : stage hash tree = .ok image) (covered : image.Covered fetch) :
    Readback hash (.ofPublished fetch) tree image.name :=
  Proofs.Formats.Git.Filesystem.readback_of_stage bounds staged covered

/-- After guarded publication, the byte bindings needed by the entire finite
readback come from admission itself. No hash injectivity is needed. -/
theorem Image.readbackPublished {image : Image hash kind} {before after : Cid → Option ByteArray}
    (bounds : StageBounds hash tree) (staged : stage hash tree = .ok image) (published : image.publish before = .ok after) :
    Readback hash (.ofPublished after) tree image.name := by
  refine readback_of_stage bounds staged (fun pair member => ?_)
  change Silmaril.Semantics.Naming.graph after pair.1 pair.2
  rw [Image.publish_bindings published]; exact Or.inr (by cases pair; exact member)

end Silmaril.Formats.Git.Filesystem
