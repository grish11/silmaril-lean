module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Defs
import Silmaril.Proofs.Formats.Hive.PartitionPath.Positional.Render

public section

namespace Silmaril.Formats.Hive.PartitionPath.Positional

/-- Successful rendering preserves the ordered values, yields exactly the
declared segment count, and respects both output byte caps. -/
theorem render_spec {limits : RenderLimits} {keys : List String} {encoding : Encoding}
    {options : Options} {entries : Partition} {directory : String}
    (rendered : render limits keys encoding options entries = .ok directory) :
    parse limits.maxDirectoryBytes keys encoding options directory = .ok entries ∧
      directory.utf8ByteSize ≤ limits.maxDirectoryBytes ∧ (segments directory).length = keys.length ∧
      ∀ segment ∈ segments directory, segment.utf8ByteSize ≤ limits.maxSegmentBytes :=
  Proofs.Formats.Hive.PartitionPath.Positional.render_spec rendered

theorem parse_render_of_ok {limits : RenderLimits} {keys : List String} {encoding : Encoding}
    {options : Options} {entries : Partition} {directory : String}
    (rendered : render limits keys encoding options entries = .ok directory) :
    parse limits.maxDirectoryBytes keys encoding options directory = .ok entries :=
  (render_spec rendered).1

end Silmaril.Formats.Hive.PartitionPath.Positional
