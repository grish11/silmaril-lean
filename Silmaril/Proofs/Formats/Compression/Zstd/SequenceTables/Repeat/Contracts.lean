module

public import Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Defs
import Silmaril.Formats.Compression.Zstd.SequenceTables.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.SequenceTables.Repeat

open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.SequenceTables (Limits Section Table TableWire resolveUsing)
open Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat

theorem resolveTable_sound {prior : State} {alphabet : FseTable.Alphabet} {mode : Nat}
    {input rest : List UInt8} {table : Table}
    (success : SequenceTables.Repeat.resolveTable prior alphabet mode input = .ok (table, rest)) :
    ∃ used, input = used ++ rest ∧ SelectionWire prior alphabet mode used rest table := by
  unfold SequenceTables.Repeat.resolveTable at success
  split at success
  · rename_i repeated
    subst mode
    cases previous : prior.table alphabet with
    | none => simp [previous] at success
    | some chosen =>
      simp only [previous] at success
      cases success
      exact ⟨[], rfl, .reuse previous⟩
  · cases h : SequenceTables.resolveTable alphabet mode input with
    | error err => simp [h, Except.mapError] at success
    | ok pair =>
      obtain ⟨chosen, tail⟩ := pair
      simp only [h, Except.mapError] at success
      cases success
      obtain ⟨used, splitBytes, wire⟩ := SequenceTables.resolveTable_sound h
      exact ⟨used, splitBytes, .fresh wire⟩

theorem resolve_sound {limits : Limits} {prior next : State} {input : List UInt8} {result : Section}
    (success : SequenceTables.Repeat.resolve limits prior input = .ok (result, next)) :
    input.length ≤ limits.inputBytes ∧ result.count ≤ limits.sequences ∧
      SectionWire prior input result ∧ StateUpdate prior result next := by
  have observed := resolve_observation limits prior input
  rw [success] at observed
  cases h : resolveUsing Error.prefix (SequenceTables.Repeat.resolveTable prior) limits input with
  | error err => simp [h, Except.map] at observed
  | ok resolved =>
    have checks := SequenceTables.resolveUsing_sound
      (translate := Error.prefix) (readTable := SequenceTables.Repeat.resolveTable prior)
      (relation := SelectionWire prior) (fun got => resolveTable_sound got) h
    cases resolved with
    | empty =>
      simp only [h, Except.map, Except.ok.injEq, Prod.mk.injEq] at observed
      obtain ⟨rfl, same⟩ := observed
      exact ⟨checks.1, checks.2.1, checks.2.2, State.eq_of_previous same⟩
    | coded count tables stream =>
      simp only [h, Except.map, Except.ok.injEq, Prod.mk.injEq] at observed
      obtain ⟨rfl, same⟩ := observed
      exact ⟨checks.1, checks.2.1, checks.2.2, same⟩

private theorem selected_accepted {prior : State} {alphabet : FseTable.Alphabet}
    {mode : Nat} {used rest : List UInt8} {table : Table}
    (valid : prior.Valid) (selection : SelectionWire prior alphabet mode used rest table) :
    TableAccepted alphabet table := by
  cases selection with
  | fresh wire => exact ⟨_, _, _, wire⟩
  | reuse previous => exact valid _ _ previous

theorem resolve_preserves_valid {limits : Limits} {prior next : State} {input : List UInt8}
    {result : Section} (valid : prior.Valid)
    (success : SequenceTables.Repeat.resolve limits prior input = .ok (result, next)) : next.Valid := by
  obtain ⟨_, _, wire, update⟩ := resolve_sound success
  cases wire with
  | empty _ => exact (show next = prior from update).symm ▸ valid
  | coded _ _ _ ll ofc ml _ =>
    intro alphabet table previous
    have newTables := update
    unfold StateUpdate at newTables
    simp only [State.table, newTables, Option.map_some, Option.some.injEq] at previous
    subst table
    cases alphabet with
    | literalLength => exact selected_accepted valid ll
    | offset => exact selected_accepted valid ofc
    | matchLength => exact selected_accepted valid ml

theorem selected_tables_accepted {prior next : State} {result : Section}
    (update : StateUpdate prior result next) (valid : next.Valid) : result.TablesAccepted := by
  cases result with
  | empty => exact True.intro
  | coded count tables stream =>
    have stored : next.previous = some tables := update
    refine ⟨valid .literalLength _ ?_, valid .offset _ ?_, valid .matchLength _ ?_⟩ <;>
      simp [State.table, stored, tableFor]

theorem suffix_exact {prior : State} {input : List UInt8} {result : Section}
    (wire : SectionWire prior input result) :
    input.drop (input.length - result.bitstream.length) = result.bitstream := by
  cases wire with
  | empty _ => simp [Section.bitstream]
  | @coded encoded ll ofc ml stream mode count tables _ _ _ _ _ _ _ =>
    let header := encoded ++ [mode] ++ ll ++ ofc ++ ml
    change (header ++ stream).drop ((header ++ stream).length - stream.length) = stream
    simp only [List.length_append, Nat.add_sub_cancel, List.drop_left]

end Silmaril.Proofs.Formats.Compression.Zstd.SequenceTables.Repeat
