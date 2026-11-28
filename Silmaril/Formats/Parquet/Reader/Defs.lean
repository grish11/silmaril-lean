module

public import Silmaril.Formats.Arrow.Events.Defs

/-!
# Typed Parquet row-group reader

An adapter fixes the schema and the order of group descriptors on open. It
supplies a decoder for one descriptor and a close outcome for the unread tail.
Here those are pure functions over a fixed source. Wire adapters must establish
their own metadata, page decoding, and error contracts at this boundary.
-/

@[expose] public section

namespace Silmaril.Formats.Parquet.Reader

open Silmaril.Relational Silmaril.Formats.Arrow

/-- One row group denotes a list of typed nullable rows at the opened schema. -/
abbrev RowGroup {Id Kind : Type*} (schema : Scan.Schema Id Kind) (Value : Kind → Type*) :=
  Scan.Table schema Value

/-- The cursor is the unread suffix of a source. Decoding is invoked only for
the group at the head of that suffix. Descriptors may name encoded data.
`close` supplies the outcome when Arrow closes a live cursor. At EOS or on a
read error the `next` reply already consumes the cursor. -/
structure Source (Group : Type*) {Id Kind : Type*} (schema : Scan.Schema Id Kind)
    (Value : Kind → Type*) (Error : Type*) where
  groups : List Group
  readGroup : Group → Except Error (RowGroup schema Value)
  close : List Group → Except Error Unit

/-- Open failure precedes schema emission. The successful schema fixes the cell
types for every group in the source. -/
abbrev OpenResult (Group Id : Type*) {Kind : Type*} (Value : Kind → Type*) (Error : Type*) :=
  Except Error (Σ schema : Scan.Schema Id Kind, Source Group schema Value Error)

variable {Input Group Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- Each successful group emits one aligned Arrow batch, including empty groups.
The first group error terminates the read. Closing delegates to the source. -/
def batchReader (openSource : Input → OpenResult Group Id Value Error) :
    Events.BatchReader Input Id Value Error (fun s => Source Group s Value Error) where
  openInput := openSource
  next source :=
    match source.groups with
    | [] => .ok none
    | group :: rest => (source.readGroup group).map fun rows =>
      some (AlignedColumns.ofRows rows, { source with groups := rest })
  close source := source.close source.groups

/-- After a successful open, allow one pull per declared group and one extra
pull to observe EOS. The first read error still stops collection immediately. -/
def readAll (opened : OpenResult Group Id Value Error) : Events.EventStream Id Value Error :=
  match opened with
  | .error error => .error error
  | .ok source => (batchReader id).read (source.snd.groups.length + 1) (.ok source)

/-- The ordered denotation stops at the first failed group and retains every
successful preceding group. An exhausted source denotes EOS. -/
def denoteGroups (readGroup : Group → Except Error (RowGroup schema Value)) :
    List Group → List (RowGroup schema Value) × Events.Termination Error
  | [] => ([], .eos)
  | group :: rest =>
    match readGroup group with
    | .error error => ([], .readError error)
    | .ok rows =>
      let tail := denoteGroups readGroup rest
      (rows :: tail.1, tail.2)

/-- Full consumption observes the ordered row table, schema and outcome. -/
def denote (opened : OpenResult Group Id Value Error) :
    Except Error (Events.Observation Id Value Error) :=
  opened.map fun ⟨schema, source⟩ =>
    let groups := denoteGroups source.readGroup source.groups
    ⟨⟨schema, groups.1.flatten⟩, groups.2⟩

end Silmaril.Formats.Parquet.Reader
