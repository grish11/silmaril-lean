module

public import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Defs
import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Huffman.MainLengths

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli.Huffman
open Silmaril.Formats.Compression.Brotli.Huffman.MainLengths
open Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Internal

private structure Advance (before after : Cursor) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.reader.Rep suffix
  count : after.reader.count < 8
  offset : after.reader.totalRead = before.reader.totalRead + used.length
  budget : before.remaining = after.remaining + used.length

private theorem Advance.refl {cursor : Cursor} {input : List Bool}
    (rep : cursor.reader.Rep input) (count : cursor.reader.count < 8) :
    Advance cursor cursor input [] input :=
  ⟨rfl, rep, count, by simp, by simp⟩

private theorem Advance.trans {before middle after : Cursor}
    {input first rest second suffix : List Bool}
    (a : Advance before middle input first rest) (b : Advance middle after rest second suffix) :
    Advance before after input (first ++ second) suffix := by
  refine ⟨by rw [a.split, b.split, List.append_assoc], b.rep, b.count, ?_, ?_⟩
  · simp only [List.length_append, b.offset, a.offset]
    omega
  · simp only [List.length_append, a.budget, b.budget]
    omega

private theorem bind_ok {α β : Type} {action : Except Error α} {next : α → Except Error β}
    {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok result => exact ⟨result, rfl, read⟩

private theorem symbol_ok {α : Type} {action : Except CodeLengthSymbol.Error α} {out : α}
    (read : action.mapError Error.symbol = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

private theorem readRepeat_sound {kind : RepeatKind} {before after : Cursor}
    {token : Token} {input : List Bool} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readRepeat kind before = .ok (token, after)) :
    ∃ extra suffix, token = .repeat kind extra ∧ extra < 2 ^ kind.width ∧
      Advance before after input (natBits extra kind.width) suffix := by
  unfold readRepeat at read
  split at read <;> try contradiction
  rename_i cap
  split at read <;> try contradiction
  rename_i extra next actual
  cases read
  obtain ⟨suffix, split, rep', valid, offset, count'⟩ := LSBReader.readBits_sound rep count actual
  refine ⟨extra, suffix, rfl, valid, split, rep', count' ▸ Nat.mod_lt _ (by decide), ?_, ?_⟩
  · simpa only [natBits_length] using offset
  · simp only [natBits_length]
    omega

private theorem readToken_sound {table : Brotli.Huffman.CodeLengths.Table} {before after : Cursor}
    {token : Token} {input : List Bool} (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : readToken table before = .ok (token, after)) :
    ∃ used suffix, TokenWire table token used ∧ Advance before after input used suffix := by
  unfold readToken at read
  obtain ⟨⟨symbol, reader⟩, symbolRead, next⟩ := bind_ok read
  obtain ⟨bits, tail, wire, split, rep', count', offset, cap, _⟩ :=
    CodeLengthSymbol.read_sound rep count (symbol_ok symbolRead)
  have first : Advance before ⟨reader, before.remaining - (reader.totalRead - before.reader.totalRead)⟩
      input bits tail := ⟨split, rep', count', offset, by dsimp; omega⟩
  simp only [] at next
  split at next
  · cases next
    exact ⟨bits, tail, .length wire, first⟩
  · rename_i special
    let kind : RepeatKind := if symbol = 16 then .previous else .zero
    have tag : kind.symbol = symbol := by
      have bound := wire.1
      by_cases is16 : symbol = 16
      · simp [kind, is16, RepeatKind.symbol]
      · simp [kind, is16, RepeatKind.symbol]
        omega
    obtain ⟨extra, suffix, rfl, extraBound, second⟩ := readRepeat_sound first.rep first.count next
    have symbolWire : CodeLengthSymbol.Wire table kind.symbol bits := by rwa [tag]
    exact ⟨_, suffix, .run symbolWire extraBound, first.trans second⟩

theorem Token.repeat_run (kind : RepeatKind) (extra : Nat) (history : History) (valid : history.Valid) :
    let old := history.continued kind
    let total := kind.total old extra
    let run := (Token.repeat kind extra).emit history
    0 < run.count ∧ old + run.count = total ∧ run.next.previousRun = some (kind, total) ∧
      run.value = (if kind = .previous then history.prior else 0) ∧ run.next.prior = history.prior ∧
      run.next.Valid := by
  have legal : history.continued kind = 0 ∨ 3 ≤ history.continued kind := by
    cases same : history.previousRun with
    | none => simp [History.continued, same]
    | some pair =>
      obtain ⟨last, old⟩ := pair
      have lower : 3 ≤ old := by simpa [History.Valid, same] using valid
      by_cases chained : last = kind
      · simp [History.continued, same, chained, lower]
      · simp [History.continued, same, chained]
  have grows : history.continued kind < kind.total (history.continued kind) extra := by
    cases kind <;> simp only [RepeatKind.total, RepeatKind.width] <;> split <;> omega
  have length : 3 ≤ kind.total (history.continued kind) extra := by
    simp only [RepeatKind.total]
    split <;> omega
  dsimp only [Token.emit, History.Valid]
  exact ⟨by omega, by omega, rfl, rfl, rfl, length⟩

private theorem emit_progress {token : Token} {history : History} (valid : history.Valid) :
    0 < (token.emit history).count ∧ (token.emit history).next.Valid := by
  cases token with
  | length value => exact ⟨Nat.zero_lt_succ 0, trivial⟩
  | «repeat» kind extra =>
    obtain ⟨positive, _, _, _, _, nextValid⟩ := Token.repeat_run kind extra history valid
    exact ⟨positive, nextValid⟩

private theorem expand_sound {table : Brotli.Huffman.CodeLengths.Table} {fuel slots space : Nat}
    {history : History} {before after : Cursor} {lengths : List Nat} {input : List Bool}
    (valid : history.Valid) (rep : before.reader.Rep input) (count : before.reader.count < 8)
    (read : expand table fuel slots space history before = .ok (lengths, after)) :
    ∃ used suffix, RunsWire table history slots space used lengths ∧ Advance before after input used suffix := by
  induction fuel generalizing slots space history before after lengths input with
  | zero =>
    simp only [expand] at read
    split at read <;> try contradiction
    rename_i done
    subst space
    cases read
    exact ⟨[], input, .done .., .refl rep count⟩
  | succ fuel ih =>
    simp only [expand] at read
    split at read
    · rename_i done
      subst space
      cases read
      exact ⟨[], input, .done .., .refl rep count⟩
    · rename_i spacePositive
      split at read <;> try contradiction
      obtain ⟨⟨token, cursor⟩, decoded, next⟩ := bind_ok read
      simp only [] at next
      split at next
      · contradiction
      · rename_i runFits
        split at next
        · contradiction
        · rename_i massFits
          obtain ⟨⟨tail, last⟩, expanded, done⟩ := bind_ok next
          cases done
          obtain ⟨tokenBits, middle, tokenWire, first⟩ := readToken_sound rep count decoded
          obtain ⟨positive, nextValid⟩ := emit_progress (token := token) valid
          obtain ⟨tailBits, suffix, restWire, second⟩ := ih nextValid first.rep first.count expanded
          exact ⟨_, suffix, .step rfl valid (by omega) positive (by omega) (by omega) tokenWire restWire,
            first.trans second⟩

theorem read_sound {limits : Limits} {alphabet : Nat} {table : Brotli.Huffman.CodeLengths.Table}
    {before after : LSBReader} {lengths : List Nat} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read limits alphabet table before = .ok (lengths, after)) :
    0 < alphabet ∧ alphabet ≤ 704 ∧ alphabet ≤ limits.alphabet ∧
    ∃ used suffix, RunsWire table History.start alphabet 32768 used lengths ∧ input = used ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧
      used.length ≤ limits.bits := by
  unfold Formats.Compression.Brotli.Huffman.MainLengths.read at read
  split at read <;> try contradiction
  rename_i standard
  split at read <;> try contradiction
  rename_i fits
  obtain ⟨⟨values, cursor⟩, expanded, done⟩ := bind_ok read
  cases done
  obtain ⟨used, suffix, wire, advance⟩ := expand_sound (by trivial) rep count expanded
  have budget := advance.budget
  dsimp at budget
  exact ⟨by omega, by omega, by omega, used, suffix, wire, advance.split, advance.rep,
    advance.count, advance.offset, by omega⟩

private theorem TokenWire.bit_width {table : Brotli.Huffman.CodeLengths.Table} {token : Token} {bits : List Bool}
    (wire : TokenWire table token bits) : bits.length ≤ 8 := by
  have code_width : ∀ {symbol used}, CodeLengthSymbol.Wire table symbol used → used.length ≤ 5 := by
    intro symbol used symbolWire
    obtain ⟨_, code, width, _, bound, rfl⟩ := symbolWire
    have size : ∀ n, (msbBits code n).length = n := by
      intro n
      induction n <;> simp_all [msbBits]
    rwa [size]
  cases wire with
  | length symbolWire => exact Nat.le_trans (code_width symbolWire) (by decide)
  | @run kind extra used symbolWire _ =>
    have shape := code_width symbolWire
    have extraWidth : kind.width ≤ 3 := by cases kind <;> decide
    simp only [List.length_append, natBits_length]
    omega

theorem RunsWire.bounds {table : Brotli.Huffman.CodeLengths.Table} {history : History} {slots space : Nat}
    {bits : List Bool} {lengths : List Nat} (wire : RunsWire table history slots space bits lengths) :
    lengths.length = slots ∧ kraft lengths = space ∧ (∀ depth ∈ lengths, depth ≤ 15) ∧
      bits.length ≤ 8 * slots := by
  induction wire with
  | done history slots => simp [kraft, mass, List.sum_replicate_nat]
  | @step history slots space token tokenBits tailBits tail run _ _ positive runPositive slotsFit massFit tokenWire _ ih =>
    let debit := run.count * mass run.value.val
    obtain ⟨tailSize, tailMass, tailDepth, tailBudget⟩ := ih
    have headBudget := TokenWire.bit_width tokenWire
    have depthBound := run.value.isLt
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, tailSize]
      omega
    · change kraft (List.replicate run.count run.value.val ++ tail) = space
      have sumHead : kraft (List.replicate run.count run.value.val) = debit := by
        simp [kraft, debit, List.sum_replicate_nat]
      have total : kraft (List.replicate run.count run.value.val ++ tail) = debit + kraft tail := by
        simpa [kraft, List.map_append, List.sum_append] using congrArg (fun v => v + kraft tail) sumHead
      rw [total, tailMass]
      omega
    · intro len mem
      rcases List.mem_append.mp mem with mem | mem
      · have same := (List.mem_replicate.mp mem).2
        omega
      · exact tailDepth _ mem
    · simp only [List.length_append]
      omega


end Silmaril.Proofs.Formats.Compression.Brotli.Huffman.MainLengths
