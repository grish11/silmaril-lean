module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Page.Checksum.Scan.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Defs

/-! Exercise the opt-in verifier through both physical column paths. -/

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary

open Silmaril.Relational Silmaril.Formats.Arrow

private def v1 : Bytes := ⟨include_bytes "../../../../../data/parquet-crc-scan/crc-mixed-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/crc-plain-v2.parquet"⟩
private def leadingDictionary : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/crc-dictionary-v2.parquet"⟩
private def absent : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/mixed-v2.parquet"⟩
private def snappy : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/snappy-dictionary-v2.parquet"⟩

private def schema : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private def observe (stream : Events.EventStream String FlatInt32.Cell (Snapshot.Error Error)) :
    Except (Snapshot.Error Error) (List Nat × List (List (Option Int32)) × Events.Termination (Snapshot.Error Error)) :=
  stream.map fun ⟨_, trace⟩ => (trace.batches.map (·.rowCount), trace.rows.map List.ofFn, trace.termination)

private def read (bytes : Bytes) := observe (readAllWithCRC 1024 {} schema bytes)

private def expectedRows (n : Nat) : List (List (Option Int32)) := (List.range n).map fun (i : Nat) =>
  [some (Int32.ofInt (100 + Int.ofNat i)),
    if i % 4 = 0 then none else some (Int32.ofInt (40 * Int.ofNat (i / 8) - 9 + 3 * Int.ofNat (i % 3)))]

#guard read v1 = .ok ([8, 8], expectedRows 16, .eos)
#guard read v2 = .ok ([8, 8], expectedRows 16, .eos)
#guard read leadingDictionary = .ok ([8, 8], expectedRows 16, .eos)
#guard read absent = .ok ([8, 8], expectedRows 16, .eos)
#guard observe (readAll {} schema v2) =
  .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.plain .crcUnsupported))))
#guard observe (readAll {} schema leadingDictionary) =
  .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.dictionary .crcUnsupported))))
#guard read snappy = .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.codec 1))))

structure Mutation where
  name : String
  byte : Nat
  column : Nat
  page : Nat
  offset : Nat
  declared : UInt32
  computed : UInt32

private def mutations : List Mutation :=
  [⟨"plainSecond", 275, 0, 1, 245, 466463816, 3047505369⟩,
    ⟨"dictionary", 311, 1, 0, 291, 702975685, 2990785194⟩,
    ⟨"definitions", 353, 1, 1, 323, 3519150616, 446507453⟩,
    ⟨"indices", 355, 1, 1, 323, 3519150616, 1769839997⟩]

private def Mutation.line (m : Mutation) : String :=
  String.intercalate "\t" [m.name, toString m.byte, toString m.column, toString m.page,
    toString m.offset, toString m.declared, toString m.computed] ++ "\n"

#guard String.join (mutations.map Mutation.line) =
  include_str "../../../../../data/parquet-crc-scan/mutations.tsv"

private def flip (offset : Nat) : Bytes := ⟨v2.data.set! offset (v2.data[offset]! ^^^ 1)⟩

private def over (m : Mutation) : Bool :=
  let typed := Page.Checksum.FrameFailure.mk m.page m.offset (.mismatch m.declared m.computed)
  let failure := if m.column == 0 then Error.column 0 "required_i32" (.plain (.checksum typed))
    else Error.column 1 "optional_i32" (.dictionary (.checksum typed))
  decide (read (flip m.byte) = .ok ([8], expectedRows 8, .readError (.decode 1 failure)))

#guard mutations.all over

#guard observe (readAllWithCRC 0 {} schema v2) =
  .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.plain (.checksum ⟨0, 4, .byteLimit⟩)))))

private def outside : Page.Frame :=
  ⟨⟨1, 1, some 0, .dataV1 ⟨1, 0, 3, 3⟩⟩, ⟨0, 1⟩, ⟨1, 2⟩⟩

#guard Page.Checksum.verifyFrames (fun _ => 1) .empty [outside] = .error ⟨0, 0, .invalidExtent⟩

-- A decoder that always fails would mask a later CRC error if called before
-- the complete column prepass. Its branch should never win this test.
private def prematureDecode : Except (FlatScan.Error Unit) Unit := do
  let (footer, metadata) ← (Footer.readFooter {} v2).mapError .footer
  let some column := metadata.rowGroups[1]?.bind (fun group => group.columns.head?) |
    throw .groupIndex
  let fail : FlatScan.DecodePage Unit := fun _ _ _ => .error ()
  (FlatScan.scanColumnWithCRC 1024 {} fail (flip 275) footer.start ⟨"required_i32", .required⟩ 8 column).map
    (fun _ => ())

#guard prematureDecode = .error (.checksum ⟨1, 245, .mismatch 466463816 3047505369⟩)

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary
