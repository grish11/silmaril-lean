module

public import Silmaril.Semantics.Relational.Scan.Defs

/-!
# Abstract Arrow batch events

A successful open fixes the schema for all batches. An adapter supplies validated
schema labels and typed nullable columns, and translates its own error type. An IPC
adapter also interprets framing and resolves dictionaries before yielding a batch.
-/

@[expose] public section

namespace Silmaril.Formats.Arrow.Events

open Silmaril.Relational

/-- The common column length represents the number of rows even at schema width zero. -/
abbrev Batch {Id Kind : Type*} (schema : Scan.Schema Id Kind) (Value : Kind → Type*) :=
  Scan.Columns schema Value

/-- Terminal outcomes after a schema was opened. The reader's error payload is observed. -/
inductive Termination (Error : Type*) where
  | eos
  | closed
  | readError (error : Error)
  | closeError (error : Error)
  deriving DecidableEq

/-- Ordered batches followed by exactly one terminal outcome. A failed read or
close retains all preceding batches. -/
structure Trace {Id Kind : Type*} (schema : Scan.Schema Id Kind) (Value : Kind → Type*)
    (Error : Type*) where
  batches : List (Batch schema Value)
  termination : Termination Error

/-- An open error has no schema or batches. A successful open emits one schema
followed by its trace. -/
abbrev EventStream (Id : Type*) {Kind : Type*} (Value : Kind → Type*) (Error : Type*) :=
  Except Error (Σ schema : Scan.Schema Id Kind, Trace schema Value Error)

/-- A pure pull interface for adapters. `next` yields a batch with its successor
cursor, returns `none` at EOS, or reports a read error. Both terminal replies
consume the cursor. `close` consumes a live cursor and reports cleanup failure. -/
structure BatchReader (Input Id : Type*) {Kind : Type*} (Value : Kind → Type*)
    (Error : Type*) (Cursor : Scan.Schema Id Kind → Type*) where
  openInput : Input → Except Error (Σ schema, Cursor schema)
  next : {schema : Scan.Schema Id Kind} → Cursor schema →
    Except Error (Option (Batch schema Value × Cursor schema))
  close : {schema : Scan.Schema Id Kind} → Cursor schema → Except Error Unit

variable {Input Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}
variable {Cursor : Scan.Schema Id Kind → Type*}

/-- Open and call `next` at most `fuel` times. At the limit, close the live
cursor without another read. A final batch at the limit therefore yields a
close outcome even if another call would have returned EOS. A zero-row batch
still takes one call. -/
def BatchReader.read (reader : BatchReader Input Id Value Error Cursor)
    (fuel : Nat) (input : Input) : EventStream Id Value Error :=
  (reader.openInput input).map fun ⟨schema, cursor⟩ => ⟨schema, pull schema fuel cursor []⟩
where
  pull (schema : Scan.Schema Id Kind) :
      Nat → Cursor schema → List (Batch schema Value) → Trace schema Value Error
    | 0, cursor, batches =>
      let termination := match reader.close cursor with
        | .ok () => .closed
        | .error error => .closeError error
      ⟨batches.reverse, termination⟩
    | fuel + 1, cursor, batches =>
      match reader.next cursor with
      | .ok (some (batch, next)) => pull schema fuel next (batch :: batches)
      | .ok none => ⟨batches.reverse, .eos⟩
      | .error error => ⟨batches.reverse, .readError error⟩

/-- A materialized observation includes the ordered table even after an error. -/
structure Observation (Id : Type*) {Kind : Type*} (Value : Kind → Type*) (Error : Type*) where
  table : Scan.Observation Id Value
  termination : Termination Error

def Trace.rows (trace : Trace schema Value Error) : Scan.Table schema Value :=
  trace.batches.flatMap AlignedColumns.toRows

def Trace.collect (trace : Trace schema Value Error) : Observation Id Value Error :=
  ⟨⟨schema, trace.rows⟩, trace.termination⟩

def EventStream.collect (stream : EventStream Id Value Error) :
    Except Error (Observation Id Value Error) :=
  stream.map fun ⟨_, trace⟩ => trace.collect

/-- Equality of schema labels, ordered typed nullable rows, and outcomes.
Batch boundaries are unobserved, including zero-row batches. This compares
completed traces. Readers using the same call budget can stop at different rows. -/
def EventStream.Equivalent (left right : EventStream Id Value Error) : Prop :=
  left.collect = right.collect

/-- Apply a logical filter and projection to decoded batches. Each predicate
sees the full input row and keeps only true. Termination is carried through.
An adapter that skips physical reads must independently preserve observed errors. -/
def Trace.scan (trace : Trace schema Value Error) (projection : Scan.Projection schema)
    (predicate : Scan.Predicate schema Value) : Trace projection.schema Value Error :=
  ⟨trace.batches.map (fun batch => AlignedColumns.ofRows (projection.scan predicate batch.toRows)),
    trace.termination⟩

/-- Choose the logical scan at the schema emitted on successful open. -/
def EventStream.scan (stream : EventStream Id Value Error)
    (projection : (schema : Scan.Schema Id Kind) → Scan.Projection schema)
    (predicate : (schema : Scan.Schema Id Kind) → Scan.Predicate schema Value) :
    EventStream Id Value Error :=
  stream.map fun ⟨schema, trace⟩ =>
    ⟨(projection schema).schema, trace.scan (projection schema) (predicate schema)⟩

end Silmaril.Formats.Arrow.Events
