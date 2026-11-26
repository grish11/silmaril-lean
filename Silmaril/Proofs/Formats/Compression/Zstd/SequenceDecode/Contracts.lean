module

public import Silmaril.Formats.Compression.Zstd.SequenceDecode.Defs
import Silmaril.Formats.Compression.Zstd.ReverseBits.Thms
import Silmaril.Formats.Compression.Zstd.SequenceTables.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.SequenceDecode

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.SequenceDecode
open Silmaril.Formats.Compression.Zstd.SequenceDecode.Internal
open ReverseBits (Cursor)

private theorem readField_sound {width value : Nat} {cursor rest : Cursor}
    (success : ReverseBits.read width cursor = some (value, rest)) :
    Field width value cursor.bits rest.bits ∧ value < 2 ^ width := by
  obtain ⟨bits, shape, size, valueEq, within, _⟩ := ReverseBits.read_sound success
  exact ⟨⟨bits, shape, size, valueEq⟩, within⟩

private theorem readThree_sound {first second third a b c : Nat} {cursor rest : Cursor}
    (success : readThree first second third cursor = some ((a, b, c), rest)) :
    ThreeFields (first, second, third) (a, b, c) cursor.bits rest.bits ∧
      a < 2 ^ first ∧ b < 2 ^ second ∧ c < 2 ^ third := by
  cases hfirst : ReverseBits.read first cursor with
  | none => simp [readThree, hfirst, bind, Option.bind] at success
  | some pair =>
    obtain ⟨vfirst, middle⟩ := pair
    cases hsecond : ReverseBits.read second middle with
    | none => simp [readThree, hfirst, hsecond, bind, Option.bind] at success
    | some pair =>
      obtain ⟨vsecond, next⟩ := pair
      cases hthird : ReverseBits.read third next with
      | none => simp [readThree, hfirst, hsecond, hthird, bind, Option.bind] at success
      | some pair =>
        obtain ⟨vthird, tail⟩ := pair
        simp only [readThree, hfirst, hsecond, hthird, bind, Option.bind] at success
        cases success
        obtain ⟨wireFirst, boundFirst⟩ := readField_sound hfirst
        obtain ⟨wireSecond, boundSecond⟩ := readField_sound hsecond
        obtain ⟨wireThird, boundThird⟩ := readField_sound hthird
        exact ⟨⟨middle.bits, next.bits, wireFirst, wireSecond, wireThird⟩,
          boundFirst, boundSecond, boundThird⟩

private theorem initialize_sound {tables : SequenceTables.Tables} {cursor rest : Cursor} {states : States}
    (success : readInitial tables cursor = some (states, rest)) :
    InitWire tables cursor.bits states rest.bits := by
  cases reading : readThree
      (stateWidth tables.literalLength) (stateWidth tables.offset) (stateWidth tables.matchLength) cursor with
  | none => simp [readInitial, reading, bind, Option.bind] at success
  | some pair =>
    obtain ⟨⟨ll, ofc, ml⟩, tail⟩ := pair
    simp only [readInitial, reading, bind, Option.bind] at success
    cases success
    exact readThree_sound reading

private def HasWire (alphabet : FseTable.Alphabet) (table : SequenceTables.Table) : Prop :=
  ∃ mode used rest, SequenceTables.TableWire alphabet mode used rest table

private def CheckedTables (tables : SequenceTables.Tables) : Prop :=
  HasWire .literalLength tables.literalLength ∧ HasWire .offset tables.offset ∧
    HasWire .matchLength tables.matchLength

private theorem lookup_sound {alphabet : FseTable.Alphabet} {table : SequenceTables.Table}
    {state : Nat} {row : FseTable.Row} (hasWire : HasWire alphabet table)
    (selected : lookup table state = some row) : RowWire alphabet table state row := by
  obtain ⟨mode, used, rest, wire⟩ := hasWire
  cases table with
  | rle symbol =>
    cases wire with
    | rle within =>
      cases state with
      | zero =>
        cases selected
        exact ⟨rfl, Nat.zero_le _, Nat.two_pow_pos _, within, Nat.le_refl _, Nat.le_refl _⟩
      | succ state => cases selected
  | fse table =>
    have countPositive : 0 < 2 ^ row.bits := Nat.two_pow_pos _
    obtain ⟨accuracy, stateBound, symbolBound, bitsBound, nextBound⟩ :=
      SequenceTables.fse_state_bounds wire selected
        (extra := 2 ^ row.bits - 1) (by omega)
    exact ⟨selected, accuracy, stateBound, symbolBound, bitsBound, by
      change row.baseline + 2 ^ row.bits ≤ 2 ^ table.log
      omega⟩

private theorem selectRows_sound {tables : SequenceTables.Tables} {states : States} {rows : Rows}
    (checked : CheckedTables tables) (success : selectRows tables states = some rows) :
    RowsWire tables states rows := by
  cases ll : lookup tables.literalLength states.literalLength with
  | none => simp [selectRows, ll, bind, Option.bind] at success
  | some literal =>
    cases ofc : lookup tables.offset states.offset with
    | none => simp [selectRows, ll, ofc, bind, Option.bind] at success
    | some offset =>
      cases ml : lookup tables.matchLength states.matchLength with
      | none => simp [selectRows, ll, ofc, ml, bind, Option.bind] at success
      | some matched =>
        simp only [selectRows, ll, ofc, ml, bind, Option.bind] at success
        cases success
        exact ⟨lookup_sound checked.1 ll, lookup_sound checked.2.1 ofc, lookup_sound checked.2.2 ml⟩

private theorem readExtra_sound {rows : Rows} {cursor rest : Cursor} {command : Sequence.Command}
    (success : readExtra rows cursor = .ok (command, rest)) :
    ExtraWire rows cursor.bits rest.bits command := by
  cases ll : RleSequences.literalCode rows.literalLength.symbol with
  | none => simp [readExtra, ll, throw] at success
  | some literal =>
    cases ofc : offsetCode rows.offset.symbol with
    | none => simp [readExtra, ll, ofc, throw] at success
    | some offset =>
      cases ml : RleSequences.matchCode rows.matchLength.symbol with
      | none => simp [readExtra, ll, ofc, ml, throw] at success
      | some matched =>
        cases reading : readThree offset.width matched.width literal.width cursor with
        | none => simp [readExtra, ll, ofc, ml, reading, throw] at success
        | some pair =>
          obtain ⟨⟨offsetExtra, matchExtra, literalExtra⟩, tail⟩ := pair
          simp only [readExtra, ll, ofc, ml, reading, pure, Except.pure] at success
          cases success
          exact ⟨literal, offset, matched, ll, ofc, ml, literalExtra, offsetExtra, matchExtra,
            (readThree_sound reading).1, rfl⟩

private theorem advance_sound {tables : SequenceTables.Tables} {old states : States}
    {rows : Rows} {cursor rest : Cursor}
    (wire : RowsWire tables old rows) (success : advance rows cursor = some (states, rest)) :
    NextWire tables rows cursor.bits states rest.bits := by
  cases reading : readThree rows.literalLength.bits rows.matchLength.bits rows.offset.bits cursor with
  | none => simp [advance, reading, bind, Option.bind] at success
  | some pair =>
    obtain ⟨⟨ll, ml, ofc⟩, tail⟩ := pair
    simp only [advance, reading, bind, Option.bind] at success
    cases success
    obtain ⟨fields, llFits, mlFits, ofFits⟩ := readThree_sound reading
    exact ⟨ll, ofc, ml, fields, rfl,
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left llFits _) wire.literalLength.nextBound,
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left ofFits _) wire.offset.nextBound,
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left mlFits _) wire.matchLength.nextBound⟩

private theorem readCommands_sound {tables : SequenceTables.Tables} {count : Nat} {states : States}
    {cursor : Cursor} {acc out : List Sequence.Command} (checked : CheckedTables tables)
    (success : readCommands tables count states cursor acc = .ok out) :
    ∃ commands, out = acc.reverse ++ commands ∧ commands.length = count ∧
      CommandsWire tables states cursor.bits commands := by
  induction count generalizing states cursor acc with
  | zero =>
    simp only [readCommands] at success
    split at success
    · rename_i exhausted
      cases success
      rw [(ReverseBits.isEmpty_iff cursor).mp exhausted]
      exact ⟨[], by simp, rfl, .done states⟩
    · cases success
  | succ count ih =>
    cases selecting : selectRows tables states with
    | none => simp [readCommands, selecting, throw] at success
    | some rows =>
      cases reading : readExtra rows cursor with
      | error reason => simp [readCommands, selecting, reading, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨command, rest⟩ := pair
        have selected := selectRows_sound checked selecting
        have extra := readExtra_sound reading
        simp only [readCommands, selecting, reading, bind, Except.bind] at success
        split at success
        · rename_i last
          subst count
          simp only [readCommands] at success
          split at success
          · rename_i exhausted
            cases success
            rw [(ReverseBits.isEmpty_iff rest).mp exhausted] at extra
            exact ⟨[command], List.reverse_cons, rfl, .last selected extra⟩
          · cases success
        · rename_i more
          cases moving : advance rows rest with
          | none => simp [moving, throw] at success
          | some pair =>
            obtain ⟨next, tail⟩ := pair
            simp only [moving] at success
            obtain ⟨commands, shape, size, wire⟩ := ih success
            cases commands with
            | nil => exact (more size.symm).elim
            | cons nextCommand remaining =>
              refine ⟨command :: nextCommand :: remaining, ?_, by simp [size], ?_⟩
              · simpa [List.reverse_cons, List.append_assoc] using shape
              · exact .more selected extra (advance_sound selected moving) wire

private theorem tables_checked {input stream : List UInt8} {count : Nat} {tables : SequenceTables.Tables}
    (wire : SequenceTables.SectionWire input (.coded count tables stream)) : CheckedTables tables := by
  cases wire with
  | coded _ _ _ ll ofc ml _ => exact ⟨⟨_, _, _, ll⟩, ⟨_, _, _, ofc⟩, ⟨_, _, _, ml⟩⟩

theorem readResolved_sound {input : List UInt8} {resolvedSection : SequenceTables.Section} {commands : List Sequence.Command}
    (wire : SequenceTables.SectionWire input resolvedSection) (success : readResolved resolvedSection = .ok commands) :
    PayloadWire resolvedSection commands := by
  cases resolvedSection with
  | empty =>
    cases success
    exact .empty
  | coded count tables stream =>
    cases started : ReverseBits.start stream with
    | none => simp [readResolved, started, throw] at success
    | some cursor =>
      cases initialized : readInitial tables cursor with
      | none => simp [readResolved, started, initialized, throw] at success
      | some pair =>
        obtain ⟨states, rest⟩ := pair
        simp only [readResolved, started, initialized] at success
        obtain ⟨out, shape, size, body⟩ := readCommands_sound (tables_checked wire) success
        have same : commands = out := by simpa using shape
        subst commands
        exact .coded size (ReverseBits.start_sound started) (initialize_sound initialized) body

theorem decode_sound {limits : SequenceTables.Limits} {input : List UInt8} {commands : List Sequence.Command}
    (success : decode limits input = .ok commands) :
    input.length ≤ limits.inputBytes ∧ commands.length ≤ limits.sequences ∧
      ∃ resolvedSection, SequenceTables.SectionWire input resolvedSection ∧ PayloadWire resolvedSection commands ∧
        commands.length = resolvedSection.count := by
  cases resolved : SequenceTables.resolve limits input with
  | error reason => simp [SequenceDecode.decode, resolved, Except.mapError, bind, Except.bind] at success
  | ok resolvedSection =>
    simp only [SequenceDecode.decode, resolved, Except.mapError, bind, Except.bind] at success
    obtain ⟨bytesFit, countFits, wire⟩ := SequenceTables.resolve_sound resolved
    have payload := readResolved_sound wire success
    have size : commands.length = resolvedSection.count := by
      cases payload with
      | empty => rfl
      | coded size _ _ _ => exact size
    exact ⟨bytesFit, size ▸ countFits, resolvedSection, wire, payload, size⟩

end Silmaril.Proofs.Formats.Compression.Zstd.SequenceDecode
