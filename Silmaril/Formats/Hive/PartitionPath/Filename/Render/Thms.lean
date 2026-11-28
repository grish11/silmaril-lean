module

public import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Defs
import Silmaril.Proofs.Formats.Hive.PartitionPath.Filename.Render

public section

namespace Silmaril.Formats.Hive.PartitionPath.Filename

/-- The bounded parser recovers exactly the original ordered entries from a
successful rendering, independently of the lexical parent. -/
theorem parse_render_of_ok {maxFilenameBytes : Nat} {keys : List String} {encoding : Positional.Encoding}
    {options : Options} {entries : Partition} {suffix leaf : String}
    (rendered : render maxFilenameBytes keys encoding options entries suffix = .ok leaf) (directory : String) :
    parse maxFilenameBytes keys encoding options directory leaf = .ok entries :=
  Proofs.Formats.Hive.PartitionPath.Filename.parse_render_of_ok rendered directory

end Silmaril.Formats.Hive.PartitionPath.Filename
