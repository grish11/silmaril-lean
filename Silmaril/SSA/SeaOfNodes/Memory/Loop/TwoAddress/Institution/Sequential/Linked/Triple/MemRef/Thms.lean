module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Splice
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Comparison

/-! The pair-to-third edge, complete finite returns, and absence of finite returns. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {cells : Nat} {ambient next last : List ValueSort} {P Q R : EntrySignature}

/-- The old pair exit jumps with both words and the same post-store buffer. -/
theorem pair_exit_transition (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient)
    (firstWord secondWord : Word) (buffer : Buffer cells) :
    (Block.eval (evalBody firstWiring secondWiring input) ((lower cells first second third).block (.pair (.second .exit)))
      (.cons firstWord (.cons secondWord .nil))).run buffer =
      some (.inl ⟨.thirdEntry, .cons firstWord (.cons secondWord .nil)⟩, buffer) :=
  rfl

/-- The receiving entry seeds both in-bounds address arguments from the
same capture bank as the numbered boundary. Both words remain live. -/
theorem third_entry_transition (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient)
    (firstWord secondWord : Word) (buffer : Buffer cells) :
    let bank := selectThird firstWiring secondWiring input firstWord secondWord
    (Block.eval (evalBody firstWiring secondWiring input) ((lower cells first second third).block .thirdEntry)
      (.cons firstWord (.cons secondWord .nil))).run buffer =
      some (.inl ⟨.third .header, .cons firstWord (.cons secondWord
        (TwoAddress.MemRef.encodeAddresses (bank.get third.entryFirst) (bank.get third.entrySecond)))⟩, buffer) :=
  rfl

/-- A finite linked run factors through the actual pair's two words and
complete returned buffer, with a separate witness for the third loop. -/
theorem returns_iff_pair_then_third (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient)
    (initial final : Buffer cells) (firstWord secondWord thirdWord : Word) :
    (∃ fuel, runFuel first second third firstWiring secondWiring input fuel initial =
      some (firstWord, secondWord, thirdWord, final)) ↔
      ∃ pairFuel thirdFuel middle,
        Linked.MemRef.runFuel first second firstWiring input pairFuel initial = some (firstWord, secondWord, middle) ∧
        TwoAddress.MemRef.runFuel third (selectThird firstWiring secondWiring input firstWord secondWord)
          thirdFuel middle = some (thirdWord, final) :=
  Proofs.returns_iff_pair_then_third first second third firstWiring secondWiring input initial final
    firstWord secondWord thirdWord

/-- The actual emitted CF and numbered θ triple agree on the three words
and full final buffer, each at its own finite budget. -/
theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P)
    (initial final : Heap model.cells) (firstWord secondWord thirdWord : Word) :
    (∃ fuel, runFuel first second third firstWiring secondWiring model.input fuel ⟨initial⟩ =
      some (firstWord, secondWord, thirdWord, ⟨final⟩)) ↔
      (Triple.lower first second third firstWiring secondWiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) (Triple.resultCodec model.cells (firstWord, secondWord, thirdWord, final)) :=
  Proofs.returns_iff_numbered first second third firstWiring secondWiring model initial final firstWord secondWord thirdWord

/-- Absence quantifies over all finite budgets and every result tuple. -/
theorem no_return_iff_numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P)
    (initial : Heap model.cells) :
    (∀ fuel, runFuel first second third firstWiring secondWiring model.input fuel ⟨initial⟩ = none) ↔
      ∀ raw, ¬ (Triple.lower first second third firstWiring secondWiring).Returns (thetaRuntime model.cells)
        (encodeInput initial model.input) raw :=
  Proofs.no_return_iff_numbered first second third firstWiring secondWiring model initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef
