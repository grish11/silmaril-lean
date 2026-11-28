module

import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Thms
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.PartitionPath.Positional.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
meta import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Defs
meta import Silmaril.Formats.Hive.Manifest.Inventory.Defs

namespace Silmaril.Formats.Hive.PartitionPath.Filename

open Manifest
open Silmaril.Relational
open TypedPartitions (PartitionSchema Convert)

private def keys := ["region", "year"]
private def entries : Partition := [("region", some "a_b"), ("year", some "7")]
private def expected := "a%5Fb_7_part-0.parquet"

#guard (render 128 keys .uri {} entries "part-0.parquet").toOption == some expected
#guard (render 128 keys .uri {} [("region", some "café/x%5F"), ("year", some "8")]
  "part-1.parquet").toOption == some "caf%C3%A9%2Fx%255F_8_part-1.parquet"
#guard (render 128 keys .literal {} [("region", some "café%5f"), ("year", some "7")]
  "part-2.parquet").toOption == some "café%5f_7_part-2.parquet"
#guard (render 128 [] .uri {} [] "part-3.parquet").toOption == some "part-3.parquet"
#guard (render expected.utf8ByteSize keys .uri {} entries "part-0.parquet").toOption == some expected

private def fails (encoding : Positional.Encoding) (entries : Partition) (suffix : String)
    (expected : Error) : Bool :=
  match render 128 keys encoding {} entries suffix with
  | .ok _ => false
  | .error reason => reason == expected

#guard fails .literal entries "part-0.parquet" (.unsafeLiteralFilenameValue "region")
#guard fails .literal [("region", some "a/b"), ("year", some "7")]
  "part-0.parquet" (.unsafeLiteralFilenameValue "region")
#guard fails .uri [("region", none), ("year", some "7")] "part-0.parquet" (.filenameNull "region")
#guard fails .uri [("region", some ""), ("year", some "7")] "part-0.parquet" .emptySegment
#guard fails .uri [("region", some "__HIVE_DEFAULT_PARTITION__"), ("year", some "7")]
  "part-0.parquet" (.nullMarkerCollision "region")
#guard fails .uri entries.reverse "part-0.parquet" .filenameKeyOrder
#guard fails .uri entries "ambiguous_suffix.parquet" .unsafeFilenameSuffix
#guard fails .uri entries "../bad.parquet" .unsafeFilenameSuffix
#guard fails .uri entries ".." .unsafeFilenameSuffix
#guard fails .uri entries "" .unsafeFilenameSuffix
#guard match render (expected.utf8ByteSize - 1) keys .uri {} entries "part-0.parquet" with
  | .ok _ => false
  | .error reason => reason == .filenameByteLimit (expected.utf8ByteSize - 1) expected.utf8ByteSize

private def schema : PartitionSchema Unit := ⟨#[⟨"region", (), .reject⟩, ⟨"year", (), .reject⟩]⟩
private def convert : Convert (fun (_ : Unit) => String) Unit := fun _ text => .ok text
private def physical : Scan.Schema String Unit := ⟨0, Fin.elim0⟩

#guard match render 128 keys .uri {} entries "part-0.parquet" with
  | .error _ => false
  | .ok leaf =>
    let path := "raw=parent/" ++ leaf
    match prepareInventoryWithFileParser physical schema ⟨1, 128⟩ (parse 128 keys .uri) {} convert [path] with
    | .ok [file] =>
      file.path.declared == "raw=parent/a%5Fb_7_part-0.parquet" && file.path.filename == leaf &&
        (file.cells ⟨0, by decide⟩ : Option String) == some "a_b" &&
        (file.cells ⟨1, by decide⟩ : Option String) == some "7"
    | _ => false

#print axioms parse_render_of_ok
#print axioms Percent.decode_encodeWith
#print axioms Percent.encodeWith_avoids_underscore
#print axioms Positional.parseSegments_ok_iff

end Silmaril.Formats.Hive.PartitionPath.Filename
