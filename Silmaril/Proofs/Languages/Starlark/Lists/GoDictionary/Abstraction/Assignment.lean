module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction.Defs
import Silmaril.Languages.Starlark.Lists.Comparison.Thms
import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Thms
import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Thms
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction.Lookup

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap Entry findEntry putEntry)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Row)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Abstraction
open Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion (Table Address)

theorem empty_related (heap : Heap) (profile : KeyProfile) :
    Related heap profile Table.empty [] := by
  exact ⟨Lists.GoDictionary.Deletion.empty_wellFormed _, Lists.GoDictionary.Growth.empty_replayable heap,
    rfl, List.Pairwise.nil⟩

private theorem put_miss (new : Entry) (entries : List Entry) (absent : findEntry new.keyCode entries = none) :
    putEntry new entries = entries ++ [new] := by
  induction entries with
  | nil => rfl
  | cons old rest ih =>
    by_cases same : old.keyCode = new.keyCode
    · simp [findEntry, same] at absent
    · have tail : findEntry new.keyCode rest = none := by simpa [findEntry, same] using absent
      simp [putEntry, same, ih tail]

private theorem put_selected (before after : Address → Option Entry) (target : Address) (old new : Entry)
    (order : List Address) (entries : List Entry) (linked : target ∈ order)
    (addresses : order.Nodup) (unique : Lists.Comparison.UniqueKeyCodes entries)
    (encoded : order.map before = entries.map some)
    (selected : before target = some old) (code : old.keyCode = new.keyCode)
    (write : ∀ address, after address =
      if address = target then some {old with value := new.value} else before address) :
    order.map after = (putEntry new entries).map some := by
  induction order generalizing entries with
  | nil => simp at linked
  | cons head tail ih =>
    cases entries with
    | nil => simp at encoded
    | cons first rest =>
      obtain ⟨atHead, atTail⟩ := List.cons.inj encoded
      obtain ⟨notTail, tailDistinct⟩ := List.nodup_cons.mp addresses
      obtain ⟨different, tailUnique⟩ := List.pairwise_cons.mp unique
      by_cases same : head = target
      · subst head
        have equal : first = old := Option.some.inj (atHead.symm.trans selected)
        subst first
        have unchanged : tail.map after = tail.map before :=
          List.map_congr_left (fun address mem => by
            rw [write, ite_eq_right (show address ≠ target from fun eq => notTail (eq ▸ mem))])
        simp [putEntry, code, write target, unchanged, atTail]
      · have later : target ∈ tail := (List.mem_cons.mp linked).resolve_left (Ne.symm same)
        have enc := List.mem_map_of_mem (f := before) later
        rw [selected, atTail] at enc
        have member : old ∈ rest := by simpa using enc
        have differentCode : first.keyCode ≠ new.keyCode := code ▸ different old member
        simp [write head, same, atHead, putEntry, differentCode,
          ih rest later tailDistinct tailUnique atTail]

theorem set_agrees (heap : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (key value : Lists.Value) (query : KeyObservation) (laws : Coherent heap profile)
    (related : Related heap profile table entries) (admitted : profile key = some query) :
    ∃ next, Lists.GoDictionary.Deletion.set heap table key value = .ok next ∧
      Related heap profile next (putEntry ⟨key, query.code, value⟩ entries) := by
  obtain ⟨picked, looked, observation⟩ := select_entry heap profile table entries key query laws related admitted
  let row : Row := ⟨query.hash, key, value⟩
  let new : Entry := ⟨key, query.code, value⟩
  have valid (next : Table) (ran : Lists.GoDictionary.Deletion.set heap table key value = .ok next) :=
    Lists.GoDictionary.Deletion.set_valid heap table next key value related.layout related.replay ran
  have unique : Lists.Comparison.UniqueKeyCodes (putEntry new entries) :=
    Lists.Comparison.uniqueKeyCodes_putEntry new entries related.unique
  cases picked with
  | none =>
    have result : ∃ next, Lists.GoDictionary.Deletion.set heap table key value = .ok next ∧
        next.entries = table.entries ++ [row] := by
      by_cases room : table.order.length < table.width.limit
      · refine ⟨table.append row, ?_, Lists.GoDictionary.Deletion.append_entries table row related.layout⟩
        simp [Lists.GoDictionary.Deletion.set, looked, bind, Except.bind, room, pure, Except.pure, row]
      · have ⟨_, rows, layout⟩ := Lists.GoDictionary.Deletion.grow_wellFormed table related.layout
        refine ⟨table.grow.append row, Lists.GoDictionary.Deletion.set_grows heap table key value query.hash
          related.layout (Nat.not_lt.mp room) looked, ?_⟩
        rw [Lists.GoDictionary.Deletion.append_entries _ row layout, rows]
    obtain ⟨next, ran, rows⟩ := result
    have ⟨layout, replay⟩ := valid next ran
    refine ⟨next, ran, ⟨layout, replay, ?_, unique⟩⟩
    change next.order.map (observeCell profile next) = (putEntry new entries).map some
    rw [ordered_rows profile next layout, rows, List.map_append, ← ordered_rows profile table related.layout,
      related.ordered, put_miss new entries observation, List.map_append]
    simp [observeRow, row, new, admitted]
  | some hit =>
    rcases hit with ⟨address, oldRow⟩
    obtain ⟨old, found, read, encoded⟩ := observation
    let next := table.replace (address, oldRow) value
    have ran : Lists.GoDictionary.Deletion.set heap table key value = .ok next := by
      simp [Lists.GoDictionary.Deletion.set, looked, bind, Except.bind, pure, Except.pure, next]
    have ⟨layout, replay⟩ := valid next ran
    refine ⟨next, ran, ⟨layout, replay, ?_, unique⟩⟩
    change table.order.map (observeCell profile next) = (putEntry new entries).map some
    have original : observeCell profile table address = some old := by simp [observeCell, read, encoded]
    have linked := (related.layout.linked address).mpr (by simp [read])
    have code := ((Lists.Comparison.findEntry_some_iff_of_unique query.code entries old related.unique).mp found).2
    refine put_selected _ _ address old new table.order entries linked related.layout.unique
      related.unique related.ordered original code ?_
    intro other
    by_cases same : other = address
    · subst other
      obtain ⟨info, obsOf, hash, rfl⟩ := observe_row encoded
      simp [observeCell, Lists.GoDictionary.Deletion.Table.replace, Lists.GoDictionary.Deletion.Table.write,
        next, observeRow, obsOf, hash, new]
    · simp [observeCell, Lists.GoDictionary.Deletion.Table.replace,
        Lists.GoDictionary.Deletion.Table.write, next, same]

/-- A new heap with the same admitted observations preserves the table relation. -/
theorem related_heap (heap after : Heap) (profile : KeyProfile) (table : Table) (entries : List Entry)
    (beforeLaws : Coherent heap profile) (afterLaws : Coherent after profile)
    (related : Related heap profile table entries) : Related after profile table entries := by
  refine ⟨related.layout, ?_, related.ordered, related.unique⟩
  let keys := table.entries.map fun row => (row.hash, row.key)
  have admitted (item : UInt32 × Lists.Value) (mem : item ∈ keys) :
      ∃ info, profile item.2 = some info ∧ item.1 = info.hash := by
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp mem
    have encoded := List.mem_map_of_mem (f := observeRow profile) present
    rw [← ordered_rows profile table related.layout, related.ordered] at encoded
    obtain ⟨entry, _, obs⟩ := List.mem_map.mp encoded
    obtain ⟨info, obsOf, hashed, _⟩ := observe_row obs.symm
    exact ⟨info, obsOf, hashed⟩
  refine ⟨?_, ?_⟩
  · intro item mem
    obtain ⟨info, obsOf, hashed⟩ := admitted item mem
    obtain ⟨word, raw, normalized⟩ := afterLaws.hashes item.2 info obsOf
    exact ⟨word, raw, normalized.trans hashed.symm⟩
  · exact related.replay.2.imp_of_mem (fun earlier later previous same => by
      obtain ⟨a, first, firstHash⟩ := admitted _ earlier
      obtain ⟨b, second, secondHash⟩ := admitted _ later
      have equal : b.hash = a.hash := secondHash.symm.trans (same.symm.trans firstHash)
      rw [afterLaws.compares _ _ b a second first equal, ← beforeLaws.compares _ _ b a second first equal]
      exact previous same)

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Abstraction
