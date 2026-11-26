module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.AddChain (WordWire rewrittenProgram step?)
open Diamond (Val dataPorts)
open SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word]
private abbrev args := dataPorts inputs

private def chain (inner : SubZero.BinaryOpcode)
    (innerLeft : WordWire args [[wordPort], [wordPort]])
    (outerRight : WordWire args [[wordPort], [wordPort], [wordPort]]) :
    Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 2) .nil
      (.cons inner (.cons innerLeft (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons outerRight .nil))
          (.cons .mul (.cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil))
            .nil))))
  result := .output (4 : Fin 5) .head

private def original := chain .add (.arg .head) (.output (1 : Fin 3) .head)

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 2) .nil
      (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons (.literal 1) .nil
          (.cons .add (.cons (.arg .head) (.cons (.output (3 : Fin 4) .head) .nil))
            (.cons .mul (.cons (.output (4 : Fin 5) .head) (.cons (.output (2 : Fin 5) .head) .nil))
              .nil)))))
  result := .output (5 : Fin 6) .head

theorem inserts_wrapped_literal_and_routes_both_downstream_uses :
    (step? original).map (rewrittenProgram original) = some expected := rfl

private def entry (value : BitVec 64) : Tuple (Val model.value) args := .cons value .nil

theorem downstream_value_wraps_and_still_depends_on_input :
    (step? original).map (fun edit =>
      ((rewrittenProgram original edit).eval model (entry 0xffffffffffffffff),
        (rewrittenProgram original edit).eval model (entry 2))) =
      some ((0 : BitVec 64), (3 : BitVec 64)) := rfl

theorem rejects_non_add_left_producer_and_runtime_outer_right :
    (step? (chain .sub (.arg .head) (.output (1 : Fin 3) .head))).isNone = true ∧
    (step? (chain .add (.arg .head) (.arg .head))).isNone = true :=
  ⟨rfl, rfl⟩

private def literalChain := chain .add (.output (1 : Fin 2) .head) (.output (1 : Fin 3) .head)

theorem defers_two_literal_inner_add_to_the_existing_fold :
    (step? literalChain).isNone = true ∧
    (ConstantFold.fold literalChain).eval model (entry 5) = (3 : BitVec 64) :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Regression
