module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Layout
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Rehash
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Growth.Replay

public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

/-- The count threshold is the pinned load predicate in integer arithmetic. -/
theorem overloaded_iff (width : Width) (size : Nat) :
    width.limit ≤ size ↔ 8 ≤ size ∧ 13 * width.count ≤ 2 * size :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.overloaded_iff width size

/-- The home index equals Go’s masked 32-bit hash. -/
theorem home_mask (width : Width) (hash : UInt32) :
    width.home hash = (hash &&& UInt32.ofNat (width.count - 1)).toNat :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.home_mask width hash

/-- Each indexed home row occupies one slot and the chain has exactly the needed blocks. -/
theorem slots_wellFormed (table : Table) (hash : UInt32) :
    ((table.slots hash).filterMap id).Perm (table.homeEntries hash) ∧
    (table.slots hash).length = 8 * max 1 (((table.homeEntries hash).length + 7) / 8) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.slots_wellFormed table hash

/-- Appending a row changes only its own home chain. -/
theorem home_append (table : Table) (row : Row) (room : table.entries.length < table.width.limit)
    (hash : UInt32) :
    (table.insert row room).homeEntries hash = table.homeEntries hash ++
      (if table.width.home row.hash = table.width.home hash then [(row, table.entries.length)] else []) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.home_append table row room hash

/-- The primary block fills from its last slot down. -/
theorem append_primary {α : Type} (entries : List α) (row : α) (room : entries.length < 8) :
    physicalChain (entries ++ [row]) =
      (physicalChain entries).set (7 - entries.length) (some row) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.append_primary entries row room

/-- A full chain links a new block at slot zero. Otherwise insertion takes the highest vacant slot. -/
theorem append_overflow {α : Type} (entries : List α) (row : α) (full : 8 ≤ entries.length) :
    physicalChain (entries ++ [row]) =
      if entries.length % 8 = 0 then physicalChain entries ++ (some row :: List.replicate 7 none)
      else (physicalChain entries).set (8 * (entries.length / 8) + (8 - entries.length % 8)) (some row) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.append_overflow entries row full

/-- Lookup visits only the matching full hashes, in ascending slot order through the chain. -/
theorem candidates_slots (table : Table) (hash : UInt32) :
    table.candidates hash = (table.slots hash).filterMap (fun cell =>
      cell.filter fun item => item.1.hash == hash) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.candidates_slots table hash

/-- At every chronological prefix, a new home is the stable subsequence of its old home. -/
theorem home_double (width : Width) (entries : List Row) (hash : UInt32) :
    homeRows width.double entries hash = (homeRows width entries hash).filter
      (fun item => width.double.home item.1.hash == width.double.home hash) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.home_double width entries hash

/-- After splitting, rebuild the slot order in that subsequence before selecting matching hashes. -/
theorem candidates_double (width : Width) (entries : List Row) (hash : UInt32) :
    orderedCandidates width.double entries hash =
      (slotOrder ((homeRows width entries hash).filter
        (fun item => width.double.home item.1.hash == width.double.home hash))).filter
        (fun item => item.1.hash == hash) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.candidates_double width entries hash

/-- Independent ordered probe rules give the raw hit, miss or first reached key error. -/
theorem probe_slots_iff (heap : Heap) (table : Table) (key : Value) (hash : UInt32)
    (out : Except Lists.Error (Option (Row × Nat))) :
    Lists.Comparison.Probes (fun item =>
      Lists.Comparison.EqualAt heap Lists.Comparison.defaultDepth key item.1.key)
      ((table.slots hash).filterMap (fun cell => cell.filter fun item => item.1.hash == hash)) out ↔
    probeTable heap table key hash = out.mapError Error.runtime :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.probe_slots_iff heap table key hash out

theorem probe_miss_iff {α : Type} (test : α → Except Lists.Error Bool) (items : List α) :
    Lists.Comparison.probe test items = .ok none ↔ ∀ item ∈ items, test item = .ok false :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.probe_miss_iff test items

theorem replayable_sublist (heap : Heap) {rows survivors : List Row}
    (valid : Replayable heap rows) (kept : List.Sublist survivors rows) : Replayable heap survivors :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.replayable_sublist heap valid kept

theorem replayable_append (heap : Heap) (rows : List Row) (row : Row) (word : UInt32)
    (valid : Replayable heap rows) (hashed : hashKey heap row.key = .ok word)
    (stored : storedHash word = row.hash)
    (miss : ∀ earlier ∈ rows, earlier.hash = row.hash →
      Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth row.key earlier.key = .ok false) :
    Replayable heap (rows ++ [row]) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.replayable_append heap rows row word valid hashed stored miss

/-- An exhausted miss tests every matching full hash with a successful false result, at any width. -/
theorem probe_miss (heap : Heap) (width : Width) (entries : List Row) (key : Value) (hash : UInt32) :
    probeRows heap width entries key hash = .ok none ↔
      ∀ row ∈ entries, row.hash = hash →
        Lists.Comparison.equalAt heap Lists.Comparison.defaultDepth key row.key = .ok false :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.probe_miss heap width entries key hash

/-- Successful chronological replay lifts from any width to its double. -/
theorem reinserts_double (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (original : Reinserts heap width prefixRows remaining) :
    Reinserts heap width.double prefixRows remaining :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.reinserts_double heap width prefixRows remaining original

/-- Stable hashes and pairwise misses justify each replay step at every permitted prefix. -/
theorem reinserts_of_replayable (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (valid : Replayable heap (prefixRows ++ remaining)) (bound : (prefixRows ++ remaining).length ≤ width.limit) :
    Reinserts heap width prefixRows remaining :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.reinserts_of_replayable heap width prefixRows remaining valid bound

/-- Executable replay produces the exact width and ordered rows certified by the replay steps. -/
theorem reinsert_run (heap : Heap) (width : Width) (prefixRows remaining : List Row)
    (steps : Reinserts heap width prefixRows remaining)
    (bound : (prefixRows ++ remaining).length ≤ width.limit) :
    remaining.foldlM (fun table row =>
      set heap table row.key row.value)
      (⟨width, prefixRows, by simp only [List.length_append] at bound; omega⟩ : Table) =
    .ok ⟨width, prefixRows ++ remaining, bound⟩ :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.reinsert_run heap width prefixRows remaining steps bound

/-- Rehashing from an empty wider table reproduces the exact chronological rows. -/
theorem rehash_run (heap : Heap) (table : Table) (valid : Replayable heap table.entries) :
    table.entries.foldlM (fun current row =>
      set heap current row.key row.value)
      (⟨table.width.double, [], by simp⟩ : Table) = .ok table.grow :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.rehash_run heap table valid

/-- A selected candidate refers to a live chronological row. -/
theorem lookup_hit_row (heap : Heap) (table : Table) (key : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    table.entries[hit.2]? = some hit.1 :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.lookup_hit_row heap table key hash hit found

/-- Replacement preserves the hash and original key at every chronological index. -/
theorem replace_keeps_keys (table : Table) (hit : Row × Nat) (value : Value)
    (present : table.entries[hit.2]? = some hit.1) :
    (table.replace hit value).entries.map (fun row => (row.hash, row.key)) =
      table.entries.map (fun row => (row.hash, row.key)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.replace_keeps_keys table hit value present

theorem empty_replayable (heap : Heap) : Replayable heap Table.empty.entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.empty_replayable heap

/-- Successful insertion and replacement preserve the replay invariant for a fixed key heap. -/
theorem set_replayable (heap : Heap) (table next : Table) (key value : Value)
    (valid : Replayable heap table.entries)
    (ran : set heap table key value = .ok next) :
    Replayable heap next.entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.set_replayable heap table next key value valid ran

/-- A hit replaces before the load test. -/
theorem set_hit (heap : Heap) (table : Table) (key value : Value) (hash : UInt32) (hit : Row × Nat)
    (found : lookupWithHash heap table key = .ok (hash, some hit)) :
    set heap table key value = .ok (table.replace hit value) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.set_hit heap table key value hash hit found

/-- A raw lookup error aborts before the load test. -/
theorem set_error (heap : Heap) (table : Table) (key value : Value) (error : Error)
    (failed : lookupWithHash heap table key = .error error) :
    set heap table key value = .error error :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.set_error heap table key value error failed

/-- An overloaded miss retries at twice the width and appends the new row. -/
theorem set_grow (heap : Heap) (table : Table) (key value : Value) (hash : UInt32)
    (full : table.width.limit ≤ table.entries.length)
    (missing : lookupWithHash heap table key = .ok (hash, none)) :
    set heap table key value = .ok (table.grow.insert ⟨hash, key, value⟩
      (Nat.lt_of_le_of_lt table.bounded table.width.limit_lt_double)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Growth.set_grow heap table key value hash full missing

/-- The split preserves the exact chronological rows before the new insertion. -/
theorem grow_keeps_entries (table : Table) : table.grow.entries = table.entries := rfl

end Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
