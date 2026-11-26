module

public import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs
import Silmaril.Formats.Compression.Zstd.ReverseBits.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Huffman.SingleStream

open Silmaril.Formats.Compression (Bit)
open Silmaril.Formats.Compression.Zstd
open Silmaril.Formats.Compression.Zstd.Huffman.SingleStream
open Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Internal
open Huffman.DirectWeights (Tree mass slots)
open ReverseBits (Cursor)

private theorem validate_sound {limits : Huffman.DirectWeights.Limits} {tree : Tree}
    (success : validate limits tree = .ok ()) : tree.Valid limits := by
  unfold validate at success
  split at success
  · cases success
  rename_i depth
  split at success
  · cases success
  rename_i length
  split at success
  · cases success
  rename_i nonempty
  split at success
  · cases success
  rename_i weights
  split at success
  · cases success
  rename_i massFits
  split at success
  · cases success
  rename_i rank
  obtain ⟨positive, depthFits⟩ := not_or.mp depth
  obtain ⟨two, even⟩ := not_or.mp rank
  refine ⟨Nat.pos_of_ne_zero positive, Nat.le_of_not_gt depthFits, Nat.le_of_not_gt nonempty,
    List.drop_eq_nil_iff.mp (Classical.not_not.mp length), ?_, Classical.not_not.mp massFits,
    Nat.le_of_not_gt two, Classical.not_not.mp even⟩
  intro weight member
  have all : (tree.weights.all fun weight => decide (weight ≤ tree.depth)) = true := by
    simpa using weights
  exact of_decide_eq_true (List.all_eq_true.mp all weight member)

private theorem place_sound {depth start finish : Nat} {ranks : List (Nat × Nat)} {entries : List Entry}
    (success : place depth start ranks = .ok (entries, finish)) :
    LayoutWire depth start ranks entries finish := by
  induction ranks generalizing start entries finish with
  | nil =>
    cases success
    exact .done start
  | cons pair ranks ih =>
    obtain ⟨weight, symbol⟩ := pair
    simp only [place] at success
    split at success
    · cases success
    rename_i checks
    cases placed : place depth (start + slots weight) ranks with
    | error reason => simp [placed, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨tail, stop⟩ := pair
      simp only [placed, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨positive, bound, symbolFits, aligned, available⟩ := by
        simpa only [not_or] using checks
      exact .code (Nat.pos_of_ne_zero positive) (Nat.le_of_not_gt bound)
        (Nat.lt_of_not_ge symbolFits) (Classical.not_not.mp aligned) (Nat.le_of_not_gt available) (ih placed)

theorem build_sound {limits : Huffman.DirectWeights.Limits} {tree : Tree} {table : Table}
    (success : build limits tree = .ok table) : tree.Valid limits ∧ TableWire tree table := by
  cases valid : validate limits tree with
  | error reason => simp [build, valid, bind, Except.bind] at success
  | ok validated =>
    cases placed : place tree.depth 0 (ranked tree) with
    | error reason => simp [build, valid, placed, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨entries, finish⟩ := pair
      simp only [build, valid, placed, bind, Except.bind] at success
      split at success
      · cases success
      · rename_i exactEnd
        cases success
        exact ⟨validate_sound (by cases validated; exact valid), rfl,
          Classical.not_not.mp exactEnd ▸ place_sound placed⟩

private theorem layout_intervals {depth start finish : Nat} {ranks : List (Nat × Nat)}
    {entries : List Entry} (wire : LayoutWire depth start ranks entries finish) :
    (∀ entry ∈ entries, 0 < entry.width ∧ entry.width ≤ depth ∧
      start ≤ entry.start depth ∧ entry.finish depth ≤ 2 ^ depth) ∧
      entries.Pairwise (fun left right => left.finish depth ≤ right.start depth) := by
  induction wire with
  | done => simp
  | @code start finish weight symbol rank entries positive weightFits _ aligned fits _ ih =>
    let entry : Entry := ⟨symbol, depth + 1 - weight, start / slots weight⟩
    have span : entry.span depth = slots weight := by
      simp only [entry, Entry.span, slots, Nat.ne_of_gt positive, ite_false]
      congr 1
      omega
    have begins : entry.start depth = start := by
      simp only [Entry.start, span, entry]
      have exactDivision := Nat.mod_add_div start (slots weight)
      rw [aligned, Nat.zero_add, Nat.mul_comm] at exactDivision
      exact exactDivision
    have ends : entry.finish depth = start + slots weight := by simp [Entry.finish, begins, span]
    change (∀ code ∈ entry :: entries, _) ∧ (entry :: entries).Pairwise _
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, ih.2⟩⟩
    · intro code member
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨by dsimp [entry]; omega, by dsimp [entry]; omega, by simp [begins], ends ▸ fits⟩
      · obtain ⟨nonzero, width, atLeast, within⟩ := ih.1 code tail
        exact ⟨nonzero, width, Nat.le_trans (Nat.le_add_right _ _) atLeast, within⟩
    · intro code member
      rw [ends]
      exact (ih.1 code member).2.2.1

theorem table_intervals {tree : Tree} {table : Table} (wire : TableWire tree table) :
    (∀ entry ∈ table.entries, 0 < entry.width ∧ entry.width ≤ table.depth ∧
      entry.finish table.depth ≤ 2 ^ table.depth) ∧
    table.entries.Pairwise (fun left right => left.finish table.depth ≤ right.start table.depth) := by
  rw [wire.1]
  obtain ⟨bounds, disjoint⟩ := layout_intervals wire.2
  exact ⟨fun entry member => ⟨(bounds entry member).1, (bounds entry member).2.1,
    (bounds entry member).2.2.2⟩, disjoint⟩

private theorem readSymbol_sound {entries : List Entry} {cursor rest : Cursor} {byte : UInt8}
    (success : readSymbol cursor entries = some (byte, rest)) :
    ∃ entry ∈ entries, ∃ field, cursor.bits = field ++ rest.bits ∧ field.length = entry.width ∧
      Bit.bitsToNatMSB field = entry.code ∧ byte = entry.symbol.toUInt8 := by
  induction entries with
  | nil => cases success
  | cons entry entries ih =>
    have tail (ok : readSymbol cursor entries = some (byte, rest)) :
        ∃ chosen ∈ entry :: entries, ∃ field,
          cursor.bits = field ++ rest.bits ∧ field.length = chosen.width ∧
            Bit.bitsToNatMSB field = chosen.code ∧ byte = chosen.symbol.toUInt8 := by
      obtain ⟨chosen, member, read⟩ := ih ok
      exact ⟨chosen, List.mem_cons_of_mem _ member, read⟩
    cases read : ReverseBits.read entry.width cursor with
    | none => exact tail (by simpa [readSymbol, read] using success)
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp only [readSymbol, read] at success
      split at success
      · rename_i matched
        cases success
        obtain ⟨field, shape, width, valueEq, _, _⟩ := ReverseBits.read_sound read
        exact ⟨entry, List.mem_cons_self, field, shape, width, valueEq.symm.trans matched, rfl⟩
      · exact tail success

private theorem readSymbols_sound {entries : List Entry} {expected : Nat} {cursor : Cursor}
    {acc out : List UInt8} (success : readSymbols entries expected cursor acc = .ok out) :
    ∃ bytes, out = acc.reverse ++ bytes ∧ bytes.length = expected ∧ StreamWire entries cursor.bits bytes := by
  induction expected generalizing cursor acc with
  | zero =>
    simp only [readSymbols] at success
    split at success
    · rename_i finished
      cases success
      refine ⟨[], by simp, rfl, ?_⟩
      rw [(ReverseBits.isEmpty_iff cursor).mp finished]
      exact .done
    · cases success
  | succ count ih =>
    cases read : readSymbol cursor entries with
    | none => simp [readSymbols, read] at success
    | some pair =>
      obtain ⟨byte, rest⟩ := pair
      simp only [readSymbols, read] at success
      obtain ⟨entry, member, field, layout, width, code, rfl⟩ := readSymbol_sound read
      obtain ⟨bytes, shape, length, wire⟩ := ih success
      refine ⟨entry.symbol.toUInt8 :: bytes, ?_, by simp [length], ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using shape
      · rw [layout]
        exact .symbol member width code wire

theorem decode_sound {limits : Limits} {tree : Tree} {expected : Nat} {input out : List UInt8}
    (success : decode limits tree expected input = .ok out) :
    input.length ≤ limits.inputBytes ∧ out.length = expected ∧ expected ≤ limits.outputSymbols ∧
    tree.Valid limits.tree ∧
    ∃ table cursor, TableWire tree table ∧ ReverseBits.StartWire input cursor ∧
      StreamWire table.entries cursor.bits out := by
  unfold decode at success
  split at success
  · cases success
  rename_i bytesFit
  split at success
  · cases success
  rename_i symbolsFit
  cases built : build limits.tree tree with
  | error reason => simp [built, bind, Except.bind] at success
  | ok table =>
    cases started : ReverseBits.start input with
    | none => simp [built, started, throw, bind, Except.bind] at success
    | some cursor =>
      simp only [built, started, bind, Except.bind] at success
      obtain ⟨decoded, shape, length, wire⟩ := readSymbols_sound success
      have same : out = decoded := by simpa using shape
      subst out
      obtain ⟨valid, canonical⟩ := build_sound built
      exact ⟨List.drop_eq_nil_iff.mp (Classical.not_not.mp bytesFit), length, Nat.le_of_not_gt symbolsFit,
        valid, table, cursor, canonical, ReverseBits.start_sound started, wire⟩

end Silmaril.Proofs.Formats.Compression.Zstd.Huffman.SingleStream
