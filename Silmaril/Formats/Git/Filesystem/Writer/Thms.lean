module

public import Silmaril.Formats.Git.Filesystem.Writer.Defs
public import Silmaril.Semantics.Prolly.Thms
import Silmaril.Proofs.Formats.Git.Filesystem.Writer

public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Semantics.Prolly (build)

variable {hash : Hash} {directory : ByteDirectory}

theorem BlockBounds.encode {block : DirBlock} (bounds : BlockBounds block) :
    ∃ value, dirCodec.encode? block = some value ∧ Formats.Dasl.Wire.BdaslEncodable value :=
  Proofs.Formats.Git.Filesystem.blockBounds_encode bounds

/-- Successful bottom-up naming is sufficient for the actual directory writer;
no separate enumeration or publication hypothesis is needed. -/
theorem stageDirectory_of_root {root : Cid}
    (named : (build policy directory.ordered).rootName? (dirProfile hash).nameBlock? = some root) :
    ∃ image, stageDirectory hash directory = .ok image ∧ image.OfDirectory directory :=
  Proofs.Formats.Git.Filesystem.stageDirectory_of_root named

theorem stageDirectory_of_bounds (bounds : DirectoryBounds hash directory) :
    ∃ image, stageDirectory hash directory = .ok image ∧ image.OfDirectory directory :=
  Proofs.Formats.Git.Filesystem.stageDirectory_of_bounds bounds

theorem stageDirectory_of_ok {image : Image hash .tree}
    (staged : stageDirectory hash directory = .ok image) : image.OfDirectory directory :=
  Proofs.Formats.Git.Filesystem.stageDirectory_of_ok staged

end Silmaril.Formats.Git.Filesystem
