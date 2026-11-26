module

import Silmaril.Formats.Parquet.Reader.Thms

/-! Kernel-checked examples of group order, row counts, and terminal outcomes. -/

namespace Silmaril.Formats.Parquet.Reader

open Silmaril.Relational Silmaril.Formats.Arrow

private abbrev Value (_ : Unit) := Nat

private def schema : Scan.Schema Nat Unit := ⟨2, fun i => (i.val, ())⟩

private def row (key payload : Option Nat) : Scan.Row schema Value :=
  fun i => if i.val = 0 then key else payload

private def duplicate : Scan.Row schema Value := row (some 7) none
private def unknown : Scan.Row schema Value := row none (some 9)
private def last : Scan.Row schema Value := row (some 7) (some 20)

private def decodeGroup : Nat → Except Nat (RowGroup schema Value)
  | 0 => .ok [duplicate, unknown]
  | 1 => .ok []
  | 2 => .ok [last, duplicate]
  | 4 => .ok [unknown]
  | _ => .error 17

private def source (groups : List Nat) : Source Nat schema Value Nat :=
  ⟨groups, decodeGroup, fun rest => if rest.isEmpty then .error 23 else .ok ()⟩

private def opened (groups : List Nat) : OpenResult Nat Nat Value Nat :=
  .ok ⟨schema, source groups⟩

private def reader : Events.BatchReader (OpenResult Nat Nat Value Nat) Nat Value Nat
    (fun s => Source Nat s Value Nat) :=
  batchReader id

example : (readAll (opened [0, 1, 2])).collect =
    .ok ⟨⟨schema, [duplicate, unknown, last, duplicate]⟩, .eos⟩ := rfl

example : (readAll (opened [0, 1, 2])).map
    (fun opened => opened.snd.batches.map AlignedColumns.rowCount) = .ok [2, 0, 2] := rfl

example : (reader.read 3 (opened [0, 1, 2])).collect =
    .ok ⟨⟨schema, [duplicate, unknown, last, duplicate]⟩, .closeError 23⟩ := rfl

example : (reader.read 4 (opened [0, 1, 2])).collect =
    .ok ⟨⟨schema, [duplicate, unknown, last, duplicate]⟩, .eos⟩ := rfl

example : (reader.read 2 (opened [0, 1, 2])).collect =
    .ok ⟨⟨schema, [duplicate, unknown]⟩, .closed⟩ := rfl

example : (reader.read 0 (opened [])).collect = .ok ⟨⟨schema, []⟩, .closeError 23⟩ := rfl

example : (readAll (opened [])).collect = .ok ⟨⟨schema, []⟩, .eos⟩ := rfl

example : (readAll (opened [0, 1, 3, 2])).collect =
    .ok ⟨⟨schema, [duplicate, unknown]⟩, .readError 17⟩ := rfl

example : (readAll (.error 17 : OpenResult Nat Nat Value Nat)).collect = .error 17 := rfl

private def keep (s : Scan.Schema Nat Unit) : Scan.Predicate s Value := fun row =>
  if h : 0 < s.width then (row ⟨0, h⟩).map (fun n => n == 7) else none

private def zero (s : Scan.Schema Nat Unit) : Scan.Projection s := Scan.Projection.ofArray #[]

private def payloadOnly (s : Scan.Schema Nat Unit) : Scan.Projection s :=
  if h : 1 < s.width then Scan.Projection.ofArray #[⟨1, h⟩] else zero s

example : ((readAll (opened [0, 1, 2])).scan payloadOnly keep).collect.map
    (fun o => (o.table.rows.map List.ofFn, o.termination)) =
      .ok ([[none], [some 20], [none]], .eos) := rfl

private def zeroScan (groups : List Nat) := (readAll (opened groups)).scan zero keep

example : (zeroScan [0, 1, 2]).collect.map
    (fun o => (o.table.schema.width, o.table.rowCount, o.termination)) = .ok (0, 3, .eos) := rfl

example : (zeroScan [0, 1, 3, 2]).collect.map
    (fun o => (o.table.schema.width, o.table.rowCount, o.termination)) = .ok (0, 1, .readError 17) := rfl

example : Events.EventStream.Equivalent (zeroScan [0, 4, 1, 3, 2]) (zeroScan [0, 1, 3, 2]) := by
  refine scan_readAll_skipGroup (source [0, 4, 1, 3, 2]) [0] [1, 3, 2] 4 zero keep rfl
    (rows := [unknown]) rfl ?_
  intro row mem
  have same : row = unknown := List.mem_singleton.mp mem
  subst row
  rfl

end Silmaril.Formats.Parquet.Reader
