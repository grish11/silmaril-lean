module

public import Silmaril.Formats.Compression.Brotli.Command.Defs
import Silmaril.Formats.Compression.Bits.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Command

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Command
open Silmaril.Formats.Compression.Brotli.Command.Internal
open Huffman.Description (Table)

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {output : β} (read : (action >>= next) = .ok output) :
    ∃ result, action = .ok result ∧ next result = .ok output := by
  cases action with
  | error _ => cases read
  | ok result => exact ⟨result, rfl, read⟩

private theorem mapError_ok {ε α : Type} {action : Except ε α} {f : ε → Error} {out : α}
    (read : action.mapError f = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

private theorem insertBounds (index : Fin 24) :
    insertCodes[index.val].extraBits ≤ 24 ∧ insertCodes[index.val].last ≤ 16799809 := by
  have all : insertCodes.toList.all (fun row => decide (row.extraBits ≤ 24 ∧ row.last ≤ 16799809)) = true :=
    by decide
  exact of_decide_eq_true (List.all_eq_true.mp all _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem index.isLt)))

private theorem copyBounds (index : Fin 24) :
    copyCodes[index.val].extraBits ≤ 24 ∧ 2 ≤ copyCodes[index.val].base ∧
      copyCodes[index.val].last ≤ 16779333 := by
  have all : copyCodes.toList.all (fun row => decide (row.extraBits ≤ 24 ∧ 2 ≤ row.base ∧ row.last ≤ 16779333)) = true :=
    by decide
  exact of_decide_eq_true (List.all_eq_true.mp all _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem index.isLt)))

theorem spec_bounds (symbol : Fin 704) :
    (spec symbol).insert.extraBits ≤ 24 ∧ (spec symbol).copy.extraBits ≤ 24 ∧
    (spec symbol).insert.last ≤ 16799809 ∧ 2 ≤ (spec symbol).copy.base ∧
    (spec symbol).copy.last ≤ 16779333 := by
  unfold spec
  rcases lengthIndices symbol with ⟨insert, copy⟩
  exact ⟨(insertBounds insert).1, (copyBounds copy).1, (insertBounds insert).2, (copyBounds copy).2⟩

theorem spec_implicit_iff (symbol : Fin 704) :
    (spec symbol).distance = .implicitZero ↔ symbol.val < 128 := by
  unfold spec
  cases lengthIndices symbol
  by_cases h : symbol.val < 128 <;> simp [h]

theorem ExtrasWire.bounds {symbol : Fin 704} {bits : List Bool} {command : Value}
    (wire : ExtrasWire symbol bits command) :
    command.symbol = symbol ∧ command.distance = (spec symbol).distance ∧
    (spec symbol).insert.base ≤ command.insertLength ∧ command.insertLength ≤ (spec symbol).insert.last ∧
    (spec symbol).copy.base ≤ command.copyLength ∧ command.copyLength ≤ (spec symbol).copy.last ∧
    bits.length = (spec symbol).insert.extraBits + (spec symbol).copy.extraBits := by
  cases wire with
  | @fields insert copy hi hc =>
    refine ⟨rfl, rfl, Nat.le_add_right .., ?_, Nat.le_add_right .., ?_, ?_⟩
    · change (spec symbol).insert.base + insert ≤
        (spec symbol).insert.base + 2 ^ (spec symbol).insert.extraBits - 1
      omega
    · change (spec symbol).copy.base + copy ≤
        (spec symbol).copy.base + 2 ^ (spec symbol).copy.extraBits - 1
      omega
    · simp only [List.length_append, natBits_length]

theorem Wire.bounds {table : Table} {bits : List Bool} {command : Value} (wire : Wire table bits command) :
    bits.length ≤ 63 ∧ command.insertLength ≤ 16799809 ∧
    2 ≤ command.copyLength ∧ command.copyLength ≤ 16779333 ∧
    (command.distance = .implicitZero ↔ command.symbol.val < 128) := by
  cases wire with
  | command _ _ widthCap extras =>
    obtain ⟨_, distance, _, insert, copyMin, copyMax, size⟩ := ExtrasWire.bounds extras
    obtain ⟨insertWidth, copyWidth, insertCap, copyLo, copyHi⟩ := spec_bounds command.symbol
    simp only [List.length_append, msbBits_length, size]
    exact ⟨by omega, by omega, by omega, by omega, distance ▸ spec_implicit_iff command.symbol⟩

private theorem take_sound {field : Field} {limit width result : Nat}
    {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : take field limit width before = .ok (result, after)) :
    width ≤ limit ∧ result < 2 ^ width ∧ ∃ suffix, input = natBits result width ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + width := by
  unfold take at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i value cursor actual
  cases read
  obtain ⟨suffix, split, nextRep, fits, offset, nextCount⟩ := LSBReader.readBits_sound rep count actual
  exact ⟨by omega, fits, suffix, split, nextRep, nextCount ▸ Nat.mod_lt _ (by decide), offset⟩

theorem readExtras_sound {symbol : Fin 704} {bitLimit : Nat}
    {before after : LSBReader} {input : List Bool} {command : Value}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readExtras symbol bitLimit before = .ok (command, after)) :
    ∃ used suffix, ExtrasWire symbol used command ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold readExtras at read
  obtain ⟨⟨insert, cursor⟩, insertRead, read⟩ := bind_ok read
  obtain ⟨⟨copy, final⟩, copyRead, done⟩ := bind_ok read
  cases done
  obtain ⟨insertCap, insertFits, middle, split, rep', count', first⟩ := take_sound rep count insertRead
  obtain ⟨copyCap, copyFits, suffix, split', lastRep, lastCount, second⟩ := take_sound rep' count' copyRead
  refine ⟨_, suffix, .fields insertFits copyFits, ?_, lastRep, lastCount, ?_, ?_⟩
  · rw [split, split', List.append_assoc]
  · simp only [List.length_append, natBits_length, first, second]
    omega
  · simp only [List.length_append, natBits_length]
    omega

theorem readExtras_insert_truncated {symbol : Fin 704} {bitLimit : Nat} {before : LSBReader}
    (cap : (spec symbol).insert.extraBits ≤ bitLimit)
    (missing : before.readBits (spec symbol).insert.extraBits = none) :
    readExtras symbol bitLimit before = .error (.truncated .insertExtra) := by
  simp [readExtras, take, Nat.not_lt.mpr cap, missing, bind, Except.bind]

theorem readExtras_copy_truncated {symbol : Fin 704} {bitLimit insert : Nat} {before cursor : LSBReader}
    (insertCap : (spec symbol).insert.extraBits ≤ bitLimit)
    (copyCap : (spec symbol).copy.extraBits ≤ bitLimit - (spec symbol).insert.extraBits)
    (first : before.readBits (spec symbol).insert.extraBits = some (insert, cursor))
    (missing : cursor.readBits (spec symbol).copy.extraBits = none) :
    readExtras symbol bitLimit before = .error (.truncated .copyExtra) := by
  simp [readExtras, take, Nat.not_lt.mpr insertCap, Nat.not_lt.mpr copyCap, first, missing,
    bind, Except.bind]

theorem read_sound {table : Table} {bitLimit : Nat} {before after : LSBReader}
    {input : List Bool} {command : Value} (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.Command.read table bitLimit before = .ok (command, after)) :
    ∃ used suffix, Wire table used command ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold Silmaril.Formats.Compression.Brotli.Command.read at read
  split at read <;> try contradiction
  rename_i alphabet
  obtain ⟨⟨symbol, cursor⟩, symbolRead, next⟩ := bind_ok read
  simp only [] at next
  split at next <;> try contradiction
  rename_i symbolFits
  obtain ⟨code, width, middle, assigned, widthBound, widthCap, split, rep', count', first⟩ :=
    Table.readBounded_sound rep count (mapError_ok symbolRead)
  obtain ⟨extras, suffix, extraWire, split', lastRep, lastCount, second, extraCap⟩ :=
    readExtras_sound rep' count' next
  have sameSymbol := (ExtrasWire.bounds extraWire).1
  refine ⟨_, suffix, .command (by omega) (by simpa [sameSymbol] using assigned) widthBound
    (sameSymbol ▸ extraWire), ?_, lastRep, lastCount, ?_, ?_⟩
  · rw [split, split', List.append_assoc]
  · simp only [List.length_append, msbBits_length, first, second]
    omega
  · simp only [List.length_append, msbBits_length]
    omega

theorem readSingle_sound {header : CompressedHeader.Header} {bitLimit : Nat}
    {before after : LSBReader} {input : List Bool} {command : Value}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readSingle header bitLimit before = .ok (command, after)) :
    header.initial.controls.insertCopy = .single ∧
    ∃ table used suffix, header.insertCopyTrees = [table] ∧ Wire table used command ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold readSingle at read
  split at read <;> try contradiction
  rename_i control
  split at read <;> try contradiction
  rename_i table tree
  obtain ⟨used, suffix, wire, split, rep', count', offset, cap⟩ := read_sound rep count read
  exact ⟨control, table, used, suffix, tree, wire, split, rep', count', offset, cap⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Command
