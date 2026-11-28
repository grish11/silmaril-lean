module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Comparison
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

/-! Finite observations of the single typed MemRef CFG and the linked numbered graph. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.MemRef.CF (wordWidth)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {cells : Nat} {ambient next : List ValueSort} {P Q : EntrySignature}

/-- Shifting operands past a reserved word leaves their evaluation unchanged. -/
theorem carryOperands_eval {scope delta : List Width} (word : Word) (env : Env scope)
    (operands : Operands scope delta) :
    (carryOperands operands).eval (Env.cons (w := wordWidth) word env) = operands.eval env :=
  Proofs.carryOperands_eval word env operands

theorem first_exit_transition (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (word : Word) (buffer : Buffer cells) :
    (Block.eval (evalBody wiring input) ((lower cells first second).block (.first .exit))
      (.cons word .nil)).run buffer = some (.inl ⟨.secondEntry, .cons word .nil⟩, buffer) :=
  rfl

theorem second_entry_transition (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (word : Word) (buffer : Buffer cells) :
    let bank := wiring.select word input
    (Block.eval (evalBody wiring input) ((lower cells first second).block .secondEntry)
      (.cons word .nil)).run buffer =
      some (.inl ⟨.second .header, .cons word
        (TwoAddress.MemRef.encodeAddresses (bank.get second.entryFirst) (bank.get second.entrySecond))⟩, buffer) :=
  rfl

/-- The first actual return buffer becomes the second actual entry buffer. The finite witnesses are independent. -/
theorem returns_iff_stages (first : Graph ambient) (second : Graph next)
    (wiring : Boundary.Wiring ambient next) (input : Tuple (Val cells) ambient)
    (initial : Buffer cells) (word nextWord : Word) (final : Buffer cells) :
    (∃ fuel, runFuel first second wiring input fuel initial = some (word, nextWord, final)) ↔
      ∃ firstFuel secondFuel middle,
        TwoAddress.MemRef.runFuel first input firstFuel initial = some (word, middle) ∧
        TwoAddress.MemRef.runFuel second (wiring.select word input) secondFuel middle = some (nextWord, final) :=
  Proofs.returns_iff_stages first second wiring input initial word nextWord final

/-- The linked numbered graph and single MemRef CFG agree on the exact word pair and every final cell. -/
theorem returns_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells)
    (word nextWord : Word) (final : Heap model.cells) :
    (∃ fuel, runFuel first second wiring model.input fuel ⟨initial⟩ = some (word, nextWord, ⟨final⟩)) ↔
      (Linked.lower first second wiring).Returns (thetaRuntime model.cells) (encodeInput initial model.input)
        (resultCodec model.cells (word, nextWord, final)) :=
  Proofs.returns_iff_numbered first second wiring model initial word nextWord final

/-- Absence of a finite observation agrees across the two actual linked graphs. -/
theorem no_return_iff_numbered (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ fuel, runFuel first second wiring model.input fuel ⟨initial⟩ = none) ↔
      ∀ raw, ¬ (Linked.lower first second wiring).Returns (thetaRuntime model.cells) (encodeInput initial model.input) raw :=
  Proofs.no_return_iff_numbered first second wiring model initial

theorem returns_iff_coloured (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells)
    (word nextWord : Word) (final : Heap model.cells) :
    (∃ fuel, runFuel first second wiring model.input fuel ⟨initial⟩ = some (word, nextWord, ⟨final⟩)) ↔
      RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells) (Linked.lower first second wiring)
        (encodeInput initial model.input) (resultCodec model.cells (word, nextWord, final)) :=
  (returns_iff_numbered first second wiring model initial word nextWord final).trans
    (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).symm

theorem no_return_iff_coloured (first : Graph P.args) (second : Graph Q.args)
    (wiring : Boundary.Wiring P.args Q.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ fuel, runFuel first second wiring model.input fuel ⟨initial⟩ = none) ↔
      ∀ raw, ¬ RVSDG.NestedTheta.Petri.Finishes (thetaRuntime model.cells) (Linked.lower first second wiring)
        (encodeInput initial model.input) raw :=
  (no_return_iff_numbered first second wiring model initial).trans
    (forall_congr' fun _ => not_congr (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef
