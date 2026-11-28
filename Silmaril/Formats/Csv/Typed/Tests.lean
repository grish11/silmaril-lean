module

import Silmaril.Formats.Csv.Typed.Thms
meta import Silmaril.Formats.Csv.Typed.Defs

/-! Executable regressions for heterogeneous nullable rows and the zero-column policy. -/

open Silmaril.Formats.Csv (Field Rows)
open Silmaril.Formats.Csv.Typed

private meta def bytes (s : String) : Field := s.toUTF8.data.toList

private inductive Kind where
  | text
  | digit

private meta def Value : Kind → Type
  | .text => Field
  | .digit => Nat

private meta def schema : Schema Kind :=
  ⟨2, Fin.cases (bytes "label", .text) (fun _ => (bytes "digit", .digit))⟩

private meta def codecs : (k : Kind) → CellCodec (Value k)
  | .text => ⟨some, some⟩
  | .digit =>
    { print := fun (n : Nat) => if n < 10 then some [UInt8.ofNat (48 + n)] else none
      parse := fun field => match field with
        | [b] => if 48 ≤ b.toNat ∧ b.toNat < 58 then some (b.toNat - 48) else none
        | _ => none }

private meta def row (label : Option Field) (digit : Option Nat) :
    Silmaril.Relational.Scan.Row schema Value := Fin.cases label (fun _ => digit)

private meta def data : Table schema Value :=
  [row none (some 7), row (some []) none, row (some (bytes "N")) (some 0)]

private meta def lexical : Rows :=
  [[bytes "label", bytes "digit"], [bytes "N", bytes "T7"], [bytes "T", bytes "N"],
    [bytes "TN", bytes "T0"]]

private meta def observe (table : Table schema Value) : List (Option Field × Option Nat) :=
  table.map fun item =>
    (cast (by rfl) (item (0 : Fin 2)), cast (by rfl) (item (1 : Fin 2)))

#guard exportRows schema codecs data = .ok lexical
#guard (importRows schema codecs lexical).map observe = .ok [(none, some 7), (some [], none),
  (some (bytes "N"), some 0)]
#guard encode schema codecs data = .ok (bytes "\"label\",\"digit\"\r\n\"N\",\"T7\"\r\n\"T\",\"N\"\r\n\"TN\",\"T0\"\r\n")
#guard (decode schema codecs (bytes "label,digit\r\nN,T7\r\nT,N\r\nTN,T0")).map observe =
  .ok (observe data)

#guard (importRows schema codecs []).map List.length = .error .missingHeader
#guard (importRows schema codecs [[bytes "digit", bytes "label"]]).map List.length = .error .headerMismatch
#guard (importRows schema codecs [header schema, [bytes "N"]]).map List.length = .error (.width 2 1)
#guard (importRows schema codecs [header schema, [bytes "N", bytes "N", bytes "T"]]).map List.length =
  .error (.width 2 3)
#guard (importRows schema codecs [header schema, [[], bytes "N"]]).map List.length = .error (.invalidTag 0)
#guard (importRows schema codecs [header schema, [bytes "N0", bytes "N"]]).map List.length = .error (.invalidTag 0)
#guard (importRows schema codecs [header schema, [bytes "N", bytes "Tx"]]).map List.length = .error (.parseCell 1)
#guard exportRows schema codecs [row none (some 10)] = .error (.printCell 1)
#guard encode schema codecs [row (some (bytes "é")) none] = .error .unrepresentableWire
#guard (decode schema codecs (bytes "label,digit\nN,N")).map List.length = .error .malformedWire

private meta def zero : Schema Kind := ⟨0, fun i => i.elim0⟩

private meta def zeroRows : Table zero Value := [fun i => i.elim0, fun i => i.elim0]

#guard exportRows zero codecs zeroRows = .ok [[[]], [[]], [[]]]
#guard encode zero codecs zeroRows = .ok (bytes "\"\"\r\n\"\"\r\n\"\"\r\n")
#guard (decode zero codecs (bytes "\"\"\r\n\"\"\r\n\"\"\r\n")).map List.length = .ok 2
#guard (importRows zero codecs [[[]]]).map List.length = .ok 0
#guard (importRows zero codecs [[[]], [bytes "N"]]).map List.length = .error .zeroColumnMarker
