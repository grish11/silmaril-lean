module

public import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Huffman.MainLengths.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.MainLengths

theorem History.continued_same {history : History} {kind : RepeatKind} {count : Nat}
    (prior : history.previousRun = some (kind, count)) : history.continued kind = count := by
  simp [History.continued, prior]

theorem History.continued_change {history : History} {kind last : RepeatKind} {count : Nat}
    (prior : history.previousRun = some (last, count)) (change : last ≠ kind) :
    history.continued kind = 0 := by
  simp [History.continued, prior, change]

theorem Token.length_resets (history : History) (value : Fin 16) :
    ((Token.length value).emit history).next.previousRun = none := rfl

theorem Token.default_previous (extra : Nat) :
    let run := (Token.repeat .previous extra).emit History.start
    run.value = 8 ∧ run.count = 3 + extra := ⟨rfl, rfl⟩

/-- A repeat contributes just the increment from the old run total and
    records its new total. Zero runs preserve the previous nonzero length. -/
theorem Token.repeat_run (kind : RepeatKind) (extra : Nat) (history : History) (valid : history.Valid) :
    let old := history.continued kind
    let total := kind.total old extra
    let run := (Token.repeat kind extra).emit history
    0 < run.count ∧ old + run.count = total ∧ run.next.previousRun = some (kind, total) ∧
      run.value = (if kind = .previous then history.prior else 0) ∧ run.next.prior = history.prior ∧
      run.next.Valid :=
  Proofs.Formats.Compression.Brotli.Huffman.MainLengths.Token.repeat_run kind extra history valid

/-- The expansion exactly fills the alphabet and debits the initial Kraft
    space. Each accepted token emits at least one length of depth at most 15. -/
theorem RunsWire.bounds {table : CodeLengths.Table} {history : History} {slots space : Nat}
    {bits : List Bool} {lengths : List Nat} (wire : RunsWire table history slots space bits lengths) :
    lengths.length = slots ∧ kraft lengths = space ∧ (∀ depth ∈ lengths, depth ≤ 15) ∧
      bits.length ≤ 8 * slots :=
  Proofs.Formats.Compression.Brotli.Huffman.MainLengths.RunsWire.bounds wire

/-- Successful expansion consumes the exact code-length descriptions in
    order, with unchanged suffix, under the standard and caller bounds. -/
theorem read_sound {limits : Limits} {alphabet : Nat} {table : CodeLengths.Table}
    {before after : LSBReader} {lengths : List Nat} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read limits alphabet table before = .ok (lengths, after)) :
    0 < alphabet ∧ alphabet ≤ 704 ∧ alphabet ≤ limits.alphabet ∧
    ∃ used suffix, RunsWire table History.start alphabet 32768 used lengths ∧ input = used ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧
      used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Huffman.MainLengths.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.Huffman.MainLengths
