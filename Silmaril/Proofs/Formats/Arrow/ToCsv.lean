module

public import Silmaril.Formats.Arrow.ToCsv.Defs
import Silmaril.Formats.Csv.Typed.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
import Mathlib.Data.List.Basic

public section

namespace Silmaril.Proofs.Formats.Arrow.ToCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Arrow.ToCsv
open Silmaril.Formats.Relational.NamedTable (Packed importCollected schemaMatches_eq_true_iff)

theorem labelOf_injective : Function.Injective labelOf := by
  intro left right equal
  have name : left.name = right.name :=
    String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (congrArg Prod.fst equal)))
  have kind : left.type = right.type := congrArg (fun label => label.2.1) equal
  have nullable : left.nullable = right.nullable := congrArg (fun label => label.2.2) equal
  cases left
  cases right
  simp_all

theorem schemaOf_injective : Function.Injective schemaOf := by
  intro fields other equal
  have labels (fields : List Field) : List.ofFn (schemaOf fields).kind = fields.map labelOf := by
    change List.ofFn (labelOf ∘ fields.get) = _
    rw [← List.map_ofFn]
    exact congrArg (List.map labelOf) (List.ofFn_getElem (xs := fields))
  have mapped := congrArg (fun schema : Csv.Typed.Schema Kind => List.ofFn schema.kind) equal
  simp only [labels] at mapped
  exact List.map_injective_iff.mpr labelOf_injective mapped

private theorem typedCell_preserves {kind : Kind} {raw : Option Value} {value : Option (Cell kind)}
    (checked : typedCell kind raw = .ok value) : eraseCell kind value = raw := by
  rcases kind with ⟨kind, nullable⟩
  cases kind <;> cases nullable <;> cases raw <;> (try cases ‹Value›)
  all_goals simp [typedCell] at checked
  all_goals
    subst value
    rfl

theorem typedRow_preserves {fields : List Field} {raw : Row} {row : Scan.Row (schemaOf fields) Cell}
    (checked : typedRow fields raw = .ok row) : eraseRow fields row = raw := by
  induction fields generalizing raw with
  | nil =>
    cases raw with
    | nil => rfl
    | cons value rest =>
      change Except.error InputError.rowWidth = .ok row at checked
      cases checked
  | cons field fields ih =>
    cases raw with
    | nil => simp only [typedRow, reduceCtorEq] at checked
    | cons value rest =>
      cases head : typedCell (field.type, field.nullable) value with
      | error error => simp only [typedRow, Bind.bind, Except.bind, head, reduceCtorEq] at checked
      | ok cell =>
        cases tail : typedRow fields rest with
        | error error => simp only [typedRow, Bind.bind, Except.bind, head, tail, reduceCtorEq] at checked
        | ok values =>
          simp only [typedRow, Bind.bind, Except.bind, head, tail, Pure.pure, Except.pure] at checked
          have translated := Except.ok.inj checked
          subst row
          calc
            _ = eraseCell (field.type, field.nullable) cell :: eraseRow fields values :=
              List.ofFn_succ
            _ = value :: rest := by rw [typedCell_preserves head, ih tail]

theorem typedRows_preserve {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell}
    (checked : typedRows observed = .ok rows) :
    rows.map (eraseRow observed.fields) = observed.batches.flatten := by
  have preserve (input : List Row) (output : Scan.Table (schemaOf observed.fields) Cell)
      (ok : input.mapM (typedRow observed.fields) = .ok output) :
      output.map (eraseRow observed.fields) = input := by
    induction input generalizing output with
    | nil =>
      simp [Pure.pure, Except.pure] at ok
      subst output
      rfl
    | cons raw rest ih =>
      cases head : typedRow observed.fields raw with
      | error error => simp [List.mapM_cons, Bind.bind, Except.bind, head] at ok
      | ok row =>
        cases tail : rest.mapM (typedRow observed.fields) with
        | error error => simp [List.mapM_cons, Bind.bind, Except.bind, head, tail] at ok
        | ok values =>
          simp [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure, head, tail] at ok
          subst output
          rw [List.map_cons, typedRow_preserves head, ih _ tail]
  exact preserve observed.batches.flatten rows checked

theorem codecs_parsePrint (kind : Kind) : (codecs kind).ParsePrint := by
  rcases kind with ⟨type, nullable⟩
  cases type
  · exact Csv.Typed.Codecs.int32_parsePrint
  · exact Csv.Typed.Codecs.utf8_parsePrint

theorem importIpc_of_read {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows) :
    importIpc db name (schemaOf observed.fields) limits input =
      .ok (Function.update db name (some ⟨schemaOf observed.fields, rows⟩)) := by
  simp [importIpc, observeIpc, importCollected, vacant, read, checked, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem convert_roundTrip {Name : Type} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (limits : ObservationLimits) (input : KBytes) {observed : ObservedStream}
    {rows : Scan.Table (schemaOf observed.fields) Cell} {wire : Csv.Bytes} (vacant : db name = none)
    (read : readRows limits input = .ok observed) (checked : typedRows observed = .ok rows)
    (representable : Csv.Typed.encode (schemaOf observed.fields) codecs rows = .ok wire) :
    convert db name (schemaOf observed.fields) limits input = .ok (schemaOf observed.fields, wire) ∧
      (Csv.Typed.decode (schemaOf observed.fields) codecs wire).map
        (List.map (eraseRow observed.fields)) = .ok observed.batches.flatten := by
  constructor
  · simp [convert, importIpc_of_read db name limits input vacant read checked, Csv.NamedTable.exportCsv,
      Scan.observePacked, Database.Packed.erase, Database.Partial.map, representable, Except.mapError,
      Bind.bind, Except.bind]
  · rw [Csv.Typed.decode_encode codecs_parsePrint representable]
    exact congrArg (Except.ok (ε := Csv.Typed.Error)) (typedRows_preserve checked)

end Silmaril.Proofs.Formats.Arrow.ToCsv
