module

import Silmaril.Formats.Hive.Manifest.Literal.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
meta import Silmaril.Formats.Hive.Manifest.Literal.Defs

namespace Silmaril.Formats.Hive.Manifest.Literal

open TypedPartitions (PartitionSchema Convert)

#guard (parse {} "label=%5f_HIVE_DEFAULT_PARTITION__").toOption ==
  some [("label", some "%5f_HIVE_DEFAULT_PARTITION__")]
#guard (PartitionPath.parse {} "label=%5f_HIVE_DEFAULT_PARTITION__").toOption ==
  some [("label", none)]
#guard (parse {} "label=__HIVE_DEFAULT_PARTITION__").toOption == some [("label", none)]
#guard (parse {} "label=").toOption == some [("label", some "")]
#guard (parse {} "k%2F=v%FF+%2f=a").toOption == some [("k%2F", some "v%FF+%2f=a")]
#guard (parse {} "label=café").toOption == some [("label", some "café")]
#guard (parse {nullMarker := "%2F"} "label=%2F").toOption == some [("label", none)]
#guard (parse {} "k=1/%6B=2").toOption == some [("k", some "1"), ("%6B", some "2")]

private def schema : PartitionSchema Unit := ⟨#[⟨"label", (), .reject⟩]⟩
private def convert : Convert (fun (_ : Unit) => String) Unit := fun _ text => .ok text
private def declared := "label=%5f_HIVE_DEFAULT_PARTITION__/f%2eparquet"

#guard match prepareFile schema declared.utf8ByteSize {} convert declared with
  | .ok file =>
    file.path.declared == declared && file.path.filename == "f%2eparquet" &&
    file.path.canonicalDirectory == "label=%255f_HIVE_DEFAULT_PARTITION__" &&
    file.cells ⟨0, by decide⟩ == some "%5f_HIVE_DEFAULT_PARTITION__"
  | .error _ => false

#guard match prepareFile schema 7 {} convert "é/file" with
  | .error reason => reason == .prepare (.partitionPath "é/file" (.missingEquals "é"))
  | .ok _ => false
#guard match prepareFile schema 6 {} convert "é/file" with
  | .error reason => reason == .pathByteLimit 6 7
  | .ok _ => false
#guard match prepareFile schema 100 {} convert "../label=123/f.parquet" with
  | .error reason => reason == .prepare (.relativePath "../label=123/f.parquet" .invalidSegment)
  | .ok _ => false
#guard match prepareFile schema 100 {} convert "label=1/label=2/f.parquet" with
  | .error reason => reason == .prepare (.partitionPath "label=1/label=2/f.parquet" (.duplicateKey "label"))
  | .ok _ => false

#print axioms value_eq_none_iff
#print axioms value_of_uri_marker_alias
#print axioms prepareFile_path

end Silmaril.Formats.Hive.Manifest.Literal
