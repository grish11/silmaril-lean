module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs
import Silmaril.Languages.Starlark.Lists.Comparison.Thms
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Layout

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (Heap)
open Silmaril.Languages.Starlark.Lists.GoDictionary (Error Row hashKey storedHash)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

theorem overloaded_iff (width : Width) (size : Nat) :
    width.limit ≤ size ↔ 8 ≤ size ∧ 13 * width.count ≤ 2 * size := by
  simp only [Width.limit, Nat.max_le]
  omega

theorem home_mask (width : Width) (hash : UInt32) :
    width.home hash = (hash &&& UInt32.ofNat (width.count - 1)).toNat := by
  have word : UInt32.ofNat (width.home hash) = hash &&& UInt32.ofNat (width.count - 1) := by
    rw [Width.home, Width.count, ← Nat.and_two_pow_sub_one_eq_mod, UInt32.ofNat_and, UInt32.ofNat_toNat]
  have small : width.home hash < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.mod_le ..) hash.toNat_lt
  have masked := congrArg UInt32.toNat word
  change (UInt32.ofNat (width.home hash)).toNat = _ at masked
  rwa [UInt32.toNat_ofNat_of_lt' small] at masked

theorem home_double (width : Width) (entries : List Row) (hash : UInt32) :
    homeRows width.double entries hash = (homeRows width entries hash).filter
      (fun item => width.double.home item.1.hash == width.double.home hash) := by
  have dvd : width.count ∣ width.double.count := by
    refine ⟨2, ?_⟩
    simp [Width.count, Width.double, Nat.pow_succ]
  simp only [homeRows, List.filter_filter]
  apply List.filter_congr
  intro item _
  by_cases together : width.double.home item.1.hash = width.double.home hash
  · have parent := congrArg (· % width.count) together
    simp only [Width.home, Nat.mod_mod_of_dvd _ dvd] at parent
    simp [together, show width.home item.1.hash = width.home hash from parent]
  · simp [together]

theorem candidates_double (width : Width) (entries : List Row) (hash : UInt32) :
    orderedCandidates width.double entries hash =
      (slotOrder ((homeRows width entries hash).filter
        (fun item => width.double.home item.1.hash == width.double.home hash))).filter
        (fun item => item.1.hash == hash) := by
  rw [orderedCandidates, home_double]

theorem probe_slots_iff (heap : Heap) (table : Table) (key : Lists.Value) (hash : UInt32)
    (out : Except Lists.Error (Option (Row × Nat))) :
    Lists.Comparison.Probes (fun item =>
      Lists.Comparison.EqualAt heap Lists.Comparison.defaultDepth key item.1.key)
      ((table.slots hash).filterMap (fun cell => cell.filter fun item => item.1.hash == hash)) out ↔
    probeTable heap table key hash = out.mapError Error.runtime := by
  rw [← candidates_slots]
  rw [Lists.Comparison.probes_iff_probe (α := Row × Nat) (fun item =>
    Lists.Comparison.equalAt_iff heap Lists.Comparison.defaultDepth key item.1.key)]
  unfold probeTable probeRows Table.candidates
  cases Lists.Comparison.probe
    (fun item : Row × Nat => Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key item.1.key)
    (orderedCandidates table.width table.entries hash) <;> cases out <;> simp [Except.mapError]

private theorem candidate_mem (width : Width) (entries : List Row) (hash : UInt32) (item : Row × Nat) :
    item ∈ orderedCandidates width entries hash ↔ item ∈ entries.zipIdx ∧ item.1.hash = hash := by
  rw [orderedCandidates, List.mem_filter, (slot_order_perm _).mem_iff, homeRows, List.mem_filter]
  by_cases same : item.1.hash = hash <;> simp [same]

theorem probe_miss_iff {α : Type} (test : α → Except Lists.Error Bool) (items : List α) :
    Lists.Comparison.probe test items = .ok none ↔ ∀ item ∈ items, test item = .ok false := by
  induction items with
  | nil => simp [Lists.Comparison.probe]
  | cons item later ih =>
    cases checked : test item with
    | error error => simp [Lists.Comparison.probe, checked]
    | ok flag => cases flag <;> simp [Lists.Comparison.probe, checked, ih]

theorem probe_miss (heap : Heap) (width : Width) (entries : List Row) (key : Lists.Value) (hash : UInt32) :
    probeRows heap width entries key hash = .ok none ↔
      ∀ row ∈ entries, row.hash = hash →
        Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key row.key = .ok false := by
  unfold probeRows
  rw [show ∀ result : Except Lists.Error (Option (Row × Nat)),
    result.mapError Error.runtime = .ok none ↔ result = .ok none by
      intro result
      cases result <;> simp [Except.mapError]]
  rw [probe_miss_iff]
  simp only [candidate_mem, and_imp]
  constructor
  · intro miss row mem same
    obtain ⟨index, hit⟩ := List.mem_iff_getElem?.mp mem
    exact miss (row, index) (List.mk_mem_zipIdx_iff_getElem?.mpr hit) same
  · intro miss item mem same
    exact miss item.1 (List.fst_mem_of_mem_zipIdx mem) same

theorem reinserts_double (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (original : Reinserts heap width prefixRows remaining) :
    Reinserts heap width.double prefixRows remaining := by
  induction original with
  | done rows => exact .done rows
  | next hashed stored missed room _ ih =>
    exact .next hashed stored ((probe_miss ..).mpr ((probe_miss ..).mp missed))
      (Nat.lt_trans room width.limit_lt_double) ih

theorem reinsert_run (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (steps : Reinserts heap width prefixRows remaining)
    (bound : (prefixRows ++ remaining).length ≤ width.limit) :
    remaining.foldlM (fun table row =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap table row.key row.value)
      (⟨width, prefixRows, by simp only [List.length_append] at bound; omega⟩ : Table) =
    .ok ⟨width, prefixRows ++ remaining, bound⟩ := by
  induction steps with
  | done rows => simp [pure, Except.pure]
  | @next earlier row later word hashed stored missed room _ ih =>
    let table : Table := ⟨width, earlier, Nat.le_of_lt room⟩
    have read : lookupWithHash heap table row.key = .ok (row.hash, none) := by
      simp [lookupWithHash, hashed, stored, bind, Except.bind, pure, Except.pure, probeTable, table, missed]
    have hasRoom : table.entries.length < table.width.limit := room
    have write : Languages.Starlark.Lists.GoDictionary.Growth.set heap table row.key row.value =
        .ok (table.insert row room) := by
      unfold Languages.Starlark.Lists.GoDictionary.Growth.set
      rw [read]
      cases row
      simp only [bind, Except.bind, dite_eq_left hasRoom, pure, Except.pure]
    change ((row :: later).foldlM (fun current item =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap current item.key item.value) table) = _
    rw [List.foldlM_cons, write]
    change (later.foldlM (fun current item =>
      Languages.Starlark.Lists.GoDictionary.Growth.set heap current item.key item.value) (table.insert row room)) = _
    simpa only [Table.insert, table, List.append_assoc, List.singleton_append] using
      ih (by simpa only [List.append_assoc, List.singleton_append] using bound)

theorem set_hit (heap : Heap) (table : Table) (key value : Lists.Value) (hash : UInt32) (hit : Row × Nat)
    (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    set heap table key value = .ok (table.replace hit value) := by
  unfold Languages.Starlark.Lists.GoDictionary.Growth.set
  rw [found]
  rfl

theorem set_error (heap : Heap) (table : Table) (key value : Lists.Value) (error : Error)
    (failed : lookupWithHash heap table key = .error error) :
    set heap table key value = .error error := by
  unfold Languages.Starlark.Lists.GoDictionary.Growth.set
  rw [failed]
  rfl

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

theorem set_grow (heap : Heap) (table : Table) (key value : Lists.Value) (hash : UInt32)
    (full : table.width.limit ≤ table.entries.length)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    set heap table key value = .ok (table.grow.insert ⟨hash, key, value⟩
      (Nat.lt_of_le_of_lt table.bounded table.width.limit_lt_double)) := by
  obtain ⟨_, _, _, probed⟩ := lookup_miss_parts heap table key hash missing
  have again : probeTable heap table.grow key hash = .ok none :=
    (probe_miss ..).mpr ((probe_miss ..).mp probed)
  unfold Languages.Starlark.Lists.GoDictionary.Growth.set
  rw [missing]
  simp only [bind, Except.bind, dite_eq_right (Nat.not_lt.mpr full), again, pure, Except.pure]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth
