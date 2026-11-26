module

public import Silmaril.Formats.Compression.Zstd.SequenceTables.Defs

/-! # Zstandard Repeat sequence tables

RFC 8878 §3.1.1.3.2.1. The three mode fields independently select
the previous table of their own alphabet.
-/

public section

namespace Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat

open FseTable (Alphabet)

structure State where
  private mk ::
  previous : Option Tables
  deriving DecidableEq, Repr

def State.empty : State := ⟨none⟩

theorem State.empty_previous : State.empty.previous = none := by
  unfold State.empty
  rfl

theorem State.eq_of_previous {left right : State} (same : left.previous = right.previous) :
    left = right := by
  cases left
  cases right
  cases same; rfl

@[expose] def tableFor (tables : Tables) : Alphabet → Table
  | .literalLength => tables.literalLength
  | .offset => tables.offset
  | .matchLength => tables.matchLength

@[expose] def State.table (state : State) (alphabet : Alphabet) : Option Table :=
  state.previous.map (tableFor · alphabet)

/-- A retained table has validated wire provenance in its own alphabet.
    This witness need not be retained in the executable state. -/
@[expose] def TableAccepted (alphabet : Alphabet) (table : Table) : Prop :=
  ∃ mode used rest, TableWire alphabet mode used rest table

@[expose] def State.Valid (state : State) : Prop :=
  ∀ alphabet table, state.table alphabet = some table → TableAccepted alphabet table

inductive Error where
  | prefix (reason : SequenceTables.Error)
  | missingTable (alphabet : Alphabet)
  deriving DecidableEq, Repr

inductive SelectionWire (prior : State) (alphabet : Alphabet) :
    Nat → List UInt8 → List UInt8 → Table → Prop where
  | fresh {mode : Nat} {used rest : List UInt8} {table : Table} :
      TableWire alphabet mode used rest table → SelectionWire prior alphabet mode used rest table
  | reuse {rest : List UInt8} {table : Table} :
      prior.table alphabet = some table → SelectionWire prior alphabet 3 [] rest table

abbrev SectionWire (prior : State) := SectionLayout (SelectionWire prior)

@[expose] def StateUpdate (prior : State) (result : Section) (next : State) : Prop :=
  match result with
  | .empty => next = prior
  | .coded _ tables _ => next.previous = some tables

@[expose] def resolveTable (prior : State) (alphabet : Alphabet) (mode : Nat) (input : List UInt8) :
    Except Error (Table × List UInt8) :=
  if mode = 3 then
    match prior.table alphabet with
    | none => .error (.missingTable alphabet)
    | some table => .ok (table, input)
  else (SequenceTables.resolveTable alphabet mode input).mapError Error.prefix

/-- Resolve one exact section and propose the next state. Thread it into the
    next block only after accepting this block's payload. A zero count
    preserves the prior state. -/
def resolve (limits : Limits) (prior : State) (input : List UInt8) :
    Except Error (Section × State) := do
  let result ← resolveUsing Error.prefix (resolveTable prior) limits input
  let next := match result with
    | .empty => prior
    | .coded _ tables _ => ⟨some tables⟩
  return (result, next)

/-- Observe the proposed state through its public table slots. -/
theorem resolve_observation (limits : Limits) (prior : State) (input : List UInt8) :
    (resolve limits prior input).map (fun (result, next) => (result, next.previous)) =
      (resolveUsing Error.prefix (resolveTable prior) limits input).map (fun result =>
        (result, match result with | .empty => prior.previous | .coded _ tables _ => some tables)) := by
  cases h : resolveUsing Error.prefix (resolveTable prior) limits input with
  | error _ => simp [resolve, h, bind, Except.bind, Except.map]
  | ok result => cases result <;> simp [resolve, h, bind, Except.bind, pure, Except.pure, Except.map]

end Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat
