module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.AddRewrite (rewrittenProgram)
open ConstantFold.LeftSpine (SourceIds step?)
open Diamond (Val dataPorts)
open SubZero (model word)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word, word, word]

/-- Here z is produced before y, but has the greater source node ID. -/
private def original : Program SubZero.Opcode inputs word where
  dataflow := .cons .sub (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
    (.cons .mul (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
      (.cons .add (.cons (.arg .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head) .nil))
          (.cons .mul (.cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)) .nil))))
  result := .output (4 : Fin 5) .head

private def sourceIds (y z : Int32) : SourceIds where
  lookup
    | .output 0 0 => some z
    | .output 1 0 => some y
    | _ => none

private def missing : SourceIds := ⟨fun _ => none⟩

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons .sub (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
    (.cons .mul (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
      (.cons .add (.cons (.arg .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 3) .head) .nil))
          (.cons .add (.cons (.output (3 : Fin 4) .head) (.cons (.output (1 : Fin 4) .head) .nil))
            (.cons .mul (.cons (.output (4 : Fin 5) .head) (.cons (.output (2 : Fin 5) .head) .nil)) .nil)))))
  result := .output (5 : Fin 6) .head

theorem follows_the_supplied_ids_and_exact_operand_occurrences :
    (step? (sourceIds 25 31) original).map (rewrittenProgram original) = some expected := rfl

theorem refuses_reversed_equal_or_missing_ids :
    (step? (sourceIds 31 25) original).isNone = true ∧
    (step? (sourceIds 25 25) original).isNone = true ∧
    (step? missing original).isNone = true := ⟨rfl, rfl, rfl⟩

private def entry (x u v w : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons u (.cons v (.cons w .nil)))

private def privateSum : Program SubZero.Opcode inputs word := { expected with result := .output (3 : Fin 6) .head }

theorem private_sum_wraps_and_the_original_inner_sum_is_still_read :
    privateSum.eval model (entry 0xffffffffffffffff 2 2 1) = (0 : BitVec 64) ∧
    (step? (sourceIds 25 31) original).map (fun edit =>
      ((rewrittenProgram original edit).eval model (entry 0xffffffffffffffff 2 2 1),
        (rewrittenProgram original edit).eval model (entry 5 3 11 2))) =
      some ((2 : BitVec 64), (220 : BitVec 64)) := ⟨rfl, rfl⟩

private def leftLiteral : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .add (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil)) .nil))
  result := .output (2 : Fin 3) .head

theorem literal_high_moves_right_without_ids :
    (step? missing leftLiteral).isSome = true := rfl

private def constantChain : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 1) .nil
    (.cons (.literal 2) .nil
      (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

theorem defers_the_two_right_constants_to_add_chain :
    (step? (sourceIds 25 31) constantChain).isNone = true ∧
    (ConstantFold.AddChain.step? constantChain).isSome = true := ⟨rfl, rfl⟩

private def twoAdds (same : Bool) : Program SubZero.Opcode inputs word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons .add (.cons (.output (0 : Fin 2) .head)
        (.cons (if same then .output (0 : Fin 2) .head else .output (1 : Fin 2) .head) .nil)) .nil))
  result := .output (2 : Fin 3) .head

private def earlierCaseIds : SourceIds where
  lookup
    | .arg 1 => some 25
    | .output 0 0 => some 31
    | .output 1 0 => some 32
    | _ => none

theorem defers_right_addition_and_same_source_to_earlier_rules :
    (step? earlierCaseIds (twoAdds false)).isNone = true ∧
    (ConstantFold.RightSpine.step? (twoAdds false)).isSome = true ∧
    (step? earlierCaseIds (twoAdds true)).isNone = true ∧
    (ConstantFold.Doubling.step? (twoAdds true)).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Regression
