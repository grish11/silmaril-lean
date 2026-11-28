module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Operational.Defs
import Silmaril.Languages.Starlark.Lists.GoDictionary.Thms
import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Thms
import Silmaril.Languages.Starlark.Lists.Comparison.Thms
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Slots
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion.Layout

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Error Row hashKey storedHash hashesAt_iff)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion

private theorem probes_exec (heap : Heap) (table : Table) (key : Lists.Value) (hash : UInt32)
    (out : Except Lists.Error (Option (Address × Row))) :
    Probes heap table key hash out ↔
      Lists.Comparison.probe (fun item => Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key item.2.key)
        (table.candidates hash) = out :=
  Lists.Comparison.probes_iff_probe (α := Address × Row) (fun item =>
    Lists.Comparison.equalAt_iff heap Lists.Comparison.defaultDepth key item.2.key) (table.candidates hash) out

theorem deletes_iff (heap : Heap) (table : Table) (key : Lists.Value)
    (out : Except Error (Option Lists.Value × Table)) :
    Deletes heap table key out ↔ delete heap table key = out := by
  constructor
  · intro rule
    cases rule with
    | hashError failed => simp [delete, lookupWithHash, failed, bind, Except.bind]
    | probeError hashed tested | miss hashed tested | hit hashed tested =>
      exact (by simp [delete, lookupWithHash, hashKey, (hashesAt_iff ..).mp hashed, probeTable,
        (probes_exec ..).mp tested, bind, Except.bind, Except.mapError, pure, Except.pure])
  · rintro rfl
    cases hashed : hashKey heap key with
    | error error =>
      simpa [delete, lookupWithHash, hashed, bind, Except.bind] using
        Deletes.hashError (table := table) hashed
    | ok word =>
      have stable := (hashesAt_iff heap (heap.size + 1) key word).mpr hashed
      cases ran : Lists.Comparison.probe
          (fun item : Address × Row => Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key item.2.key)
            (table.candidates (storedHash word)) with
      | error error =>
        simpa [delete, lookupWithHash, hashed, probeTable, ran, bind, Except.bind, Except.mapError] using
          Deletes.probeError stable ((probes_exec ..).mpr ran)
      | ok result =>
        cases result with
        | none =>
          simpa [delete, lookupWithHash, hashed, probeTable, ran, bind, Except.bind, Except.mapError,
            pure, Except.pure] using Deletes.miss stable ((probes_exec ..).mpr ran)
        | some item =>
          obtain ⟨address, row⟩ := item
          simpa [delete, lookupWithHash, hashed, probeTable, ran, bind, Except.bind, Except.mapError,
            pure, Except.pure] using Deletes.hit stable ((probes_exec ..).mpr ran)

theorem lookup_hit_cell (heap : Heap) (table : Table) (key : Lists.Value) (hash : UInt32)
    (address : Address) (row : Row)
    (found : lookupWithHash heap table key = .ok (hash, some (address, row))) :
    table.cells address = some row := by
  cases hashed : hashKey heap key with
  | error error => simp [lookupWithHash, hashed, bind, Except.bind] at found
  | ok word =>
    let test := fun (item : Address × Row) =>
      Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key item.2.key
    cases ran : Lists.Comparison.probe test (table.candidates (storedHash word)) with
    | error error =>
      dsimp [test] at ran
      simp [lookupWithHash, hashed, probeTable, ran, bind, Except.bind, Except.mapError] at found
    | ok result =>
      have data : (storedHash word, result) = (hash, some (address, row)) := by
        have checked := ran
        dsimp [test] at checked
        simpa [lookupWithHash, hashed, probeTable, checked, bind, Except.bind, Except.mapError,
          pure, Except.pure] using found
      rw [(Prod.mk.inj data).2] at ran
      have mem := GoDictionary.probe_hit_mem test _ (address, row) ran
      exact (candidate_mem table _ address row |>.mp mem).2.2.1

theorem lookup_miss_parts (heap : Heap) (table : Table) (key : Lists.Value) (hash : UInt32)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    ∃ word, hashKey heap key = .ok word ∧ storedHash word = hash ∧ probeTable heap table key hash = .ok none := by
  cases hashed : hashKey heap key with
  | error error => simp [lookupWithHash, hashed, bind, Except.bind] at missing
  | ok word =>
    cases checked : probeTable heap table key (storedHash word) with
    | error error => simp [lookupWithHash, hashed, checked, bind, Except.bind] at missing
    | ok hit =>
      simp [lookupWithHash, hashed, checked, bind, Except.bind, pure, Except.pure] at missing
      exact ⟨word, rfl, missing.1, missing.1 ▸ missing.2 ▸ checked⟩

theorem probe_miss (heap : Heap) (table : Table) (key : Lists.Value) (hash : UInt32)
    (wf : WellFormed table) :
    probeTable heap table key hash = .ok none ↔
      ∀ row ∈ table.entries, row.hash = hash →
        Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key row.key = .ok false := by
  unfold probeTable
  rw [show ∀ result : Except Lists.Error (Option (Address × Row)),
    result.mapError Error.runtime = .ok none ↔ result = .ok none by
      intro result
      cases result <;> simp [Except.mapError]]
  rw [Languages.Starlark.Lists.GoDictionary.Growth.probe_miss_iff]
  constructor
  · intro miss row mem same
    obtain ⟨address, _, read⟩ := List.mem_filterMap.mp mem
    obtain ⟨fits, home⟩ := wf.placed address row read
    exact miss (address, row) ((candidate_mem ..).mpr ⟨same ▸ home, fits, read, same⟩)
  · rintro miss ⟨address, row⟩ mem
    obtain ⟨_, _, read, same⟩ := (candidate_mem ..).mp mem
    have linked := (wf.linked address).mpr (by simp [read])
    exact miss row (List.mem_filterMap.mpr ⟨address, linked, read⟩) same

theorem delete_survivors (heap : Heap) (table next : Table) (key : Lists.Value) (removed : Option Lists.Value)
    (wf : WellFormed table) (ran : delete heap table key = .ok (removed, next)) :
    WellFormed next ∧ List.Sublist next.entries table.entries := by
  have rule := (deletes_iff ..).mpr ran
  cases rule with
  | miss => exact ⟨wf, List.Sublist.refl _⟩
  | hit hashed probed =>
    exact ⟨unlink_wellFormed _ _ wf, unlink_survivors _ _ wf⟩

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Deletion
