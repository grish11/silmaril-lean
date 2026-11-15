module

public import Silmaril.Semantics.Acceptors.Thms
public import Mathlib.Algebra.Group.Nat.Even
import Silmaril.Proofs.Semantics.Acceptors.Examples

/-!
# Incremental acceptors: a byte example

The language `evenZeros` of byte strings with an even number of `0x00` bytes, a
one-bit symbol acceptor `zeroParity` for it, and its chunk lift `evenZeroBytes`
over `ByteArray` chunks, proved `CorrectInterleaved`. Concrete traces are checked
by `decide`, including the counterexample acceptors `answerOnce` and `finalizing`
on this language.
-/

public section

namespace Silmaril.Acceptor.Examples

open Silmaril Silmaril.Acceptor

/-- Byte strings with an even number of zero bytes. -/
def evenZeros : Language UInt8 := {w : List UInt8 | Even (w.count 0)}

instance : DecidablePred (· ∈ evenZeros) := fun w => inferInstanceAs (Decidable (Even (w.count 0)))

theorem mem_evenZeros (w : List UInt8) : w ∈ evenZeros ↔ Even (w.count 0) := Iff.rfl

/-- One bit of state: whether an odd number of zero bytes has been read. -/
def zeroParity : Acceptor Bool UInt8 where
  init := false
  process s b := if b = 0 then !s else s
  query s := (!s, s)
  reset _ := false

/-- `zeroParity` reading `ByteArray` chunks. -/
def evenZeroBytes : Acceptor Bool ByteArray := zeroParity.ofSymbols

theorem zeroParity_symbolCorrect : zeroParity.SymbolCorrect evenZeros := fun w => by
  show (!w.foldl (fun s b => if b = 0 then !s else s) false) = _
  simp [Silmaril.Proofs.Semantics.Acceptors.foldl_flip_count, member, mem_evenZeros]

theorem evenZeroBytes_correctInterleaved : evenZeroBytes.CorrectInterleaved evenZeros :=
  correctInterleaved_ofSymbols (fun _ => rfl) (fun _ => rfl) zeroParity_symbolCorrect

/-- A session: one zero in a two-byte chunk, an empty chunk, a second zero, then reset. -/
def session : List (Event ByteArray) :=
  [.process ⟨#[0, 1]⟩, .query, .process ⟨#[]⟩, .query, .process ⟨#[0]⟩, .query, .reset, .query]

example : (evenZeroBytes.run evenZeroBytes.init session).1 = [false, false, true, true] := by
  decide

example : specObs evenZeros session = [false, false, true, true] := by decide

/-! ## The counterexamples on this language -/

/-- A second query in a row: `answerOnce` answers `false`, the specification `true`. -/
example : ((answerOnce (χ := ByteArray) evenZeros).run (answerOnce (χ := ByteArray) evenZeros).init
    ([.query, .query] : List (Event ByteArray))).1 = [true, false] := by decide

example : specObs evenZeros ([.query, .query] : List (Event ByteArray)) = [true, true] := by
  decide

theorem answerOnce_evenZeros :
    (answerOnce (χ := ByteArray) evenZeros).CorrectImmediate evenZeros ∧
      ¬ (answerOnce (χ := ByteArray) evenZeros).CorrectInterleaved evenZeros :=
  ⟨answerOnce_correctImmediate, answerOnce_not_correctInterleaved ⟨#[]⟩ (by decide)⟩

theorem finalizing_evenZeros :
    (finalizing (χ := ByteArray) evenZeros).CorrectFold evenZeros ∧
      ¬ (finalizing (χ := ByteArray) evenZeros).CorrectImmediate evenZeros :=
  ⟨finalizing_correctFold, finalizing_not_correctImmediate ⟨#[0]⟩ ⟨#[0]⟩ (by decide) (by decide)⟩

end Silmaril.Acceptor.Examples
