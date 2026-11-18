module

import Silmaril.Machine.Vex.CFG.Defs
public meta import Silmaril.Machine.Vex.CFG.Defs
import Silmaril.Machine.Vex.Validate.Thms
public meta import Silmaril.Machine.Vex.Scalar.Defs
import tests.vex.Fixtures
public meta import tests.vex.Fixtures

namespace Silmaril.Machine.Vex.Tests

open AMD64Scalar Fixtures

private def casesFromBytes : List (List UInt8 × Raw.Block) :=
  [(movBytes, movLift), (addBytes, addLift), (jeBytes, jeLift), (jneBytes, jneLift)]

example : casesFromBytes.all (fun (bytes, raw) => (validate 0x1000 bytes raw).isOk) = true := by decide +kernel

#guard casesFromBytes.all (fun (_, raw) =>
  ((check raw).toOption.map fun block => block.erase == raw) == some true)

private def runLift (bytes : List UInt8) (raw : Raw.Block) (input : Input) : Option Input := do
  let pair ← (validate 0x1000 bytes raw).toOption
  (pair.target.run input).toOption

example : runLift movBytes movLift ⟨77, 42, 9, true, 0x1000⟩ = some ⟨42, 42, 9, true, 0x1005⟩ := by decide
example : runLift movBytes movLift ⟨77, 42, 9, false, 0x1000⟩ = some ⟨42, 42, 9, false, 0x1005⟩ := by decide
example : runLift addBytes addLift ⟨0, 0xffffffffffffffff, 1, false, 0x1000⟩ =
    some ⟨0, 0xffffffffffffffff, 1, true, 0x1008⟩ := by decide
example : runLift jeBytes jeLift ⟨3, 8, 8, false, 0x1000⟩ = some ⟨3, 8, 8, true, 0x1009⟩ := by decide
example : runLift jeBytes jeLift ⟨3, 8, 7, true, 0x1000⟩ = some ⟨3, 8, 7, false, 0x1005⟩ := by decide
example : runLift jneBytes jneLift ⟨3, 8, 8, false, 0x1000⟩ = some ⟨3, 8, 8, true, 0x1005⟩ := by decide
example : runLift jneBytes jneLift ⟨3, 8, 7, true, 0x1000⟩ = some ⟨3, 8, 7, false, 0x1009⟩ := by decide

private def errorOf {error value : Type} : Except error value → Option error
  | .ok _ => none
  | .error failure => some failure

example : errorOf (validate 0x1000 jeBytes jneLift) = some .differentPlan := by decide
example : errorOf (validate 0x1000 movBytes { movLift with next := .const 64 0x1015 }) =
    some .differentPlan := by decide
example : errorOf (validate 0x1000 movBytes { movLift with statements := movLift.statements.drop 1 }) =
    some .marks := by decide
example : errorOf (validate 0x1000 (movBytes ++ [0x90]) movLift) =
    some (.x86 (.trailingBytes 0x1005)) := by decide
example : errorOf (validate 0x1000 movBytes
    { movLift with statements := movLift.statements ++ [.put 144 (.const 64 20)] }) =
    some (.observation .flagRecipe) := by decide

example : errorOf (check { movLift with next := .get 16 64 }) = some .indirectNext := by decide
example : errorOf (check { movLift with statements := [.put 16 (.tmp 0)] }) = some (.unbound 0) := by decide
example : errorOf (check { movLift with statements := [.put 16 (.const 1 0)] }) =
    some (.mismatch .i64 .i1) := by decide
example : errorOf (check { movLift with statements := [.opaque "Ist_Store" "synthetic"] }) =
    some (.extension "Ist_Store") := by decide

private def jump (address target : Word) : Block := ⟨address, [], .jump target⟩

private def splitBlock (address taken next : Word) : Block :=
  ⟨address, [], .branch (.flag true) taken next⟩

private def diamond : CFG :=
  ⟨#[splitBlock 10 20 30, jump 20 40, jump 30 50, jump 40 50, jump 50 60], [60]⟩

#guard diamond.reachable.mergeSort == [10, 20, 30, 40, 50]
#guard diamond.scope.toOption.map (fun tree => tree.flatten.map Block.address) == some [10, 20, 40, 30, 50]

private def irreducible : CFG := ⟨#[splitBlock 10 20 30, jump 20 30, jump 30 20], []⟩

example : errorOf irreducible.scope = some (.notForward 30 20) := by decide
example : errorOf (CFG.mk #[jump 10 10] []).scope = some (.notForward 10 10) := by decide
example : errorOf (CFG.mk #[jump 10 20] []).scope = some (.dangling 10 20) := by decide
example : errorOf (CFG.mk #[jump 10 30, jump 20 30] [30]).scope = some .unreachable := by decide
example : errorOf (CFG.mk #[jump 10 20] [10, 20]).scope = some .duplicateLabel := by decide

#print axioms validate_artifacts
#print axioms validate_sound
#print axioms validate_boundary
#print axioms validate_refines
#print axioms Term.selectBit_sound
#print axioms check_word_erase

end Silmaril.Machine.Vex.Tests
