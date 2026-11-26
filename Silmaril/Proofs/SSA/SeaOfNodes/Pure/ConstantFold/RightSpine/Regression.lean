module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Defs
import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.AddRewrite (rewrittenProgram)
open ConstantFold.RightSpine (WordWire step?)
open Diamond (Val dataPorts)
open SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word, word, word]
private abbrev args := dataPorts inputs

private def withOuter (lhs rhs : WordWire args [[wordPort], [wordPort]]) : Program SubZero.Opcode inputs word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
      (.cons .add (.cons lhs (.cons rhs .nil))
        (.cons .mul (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

private def original := withOuter (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head)

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
      (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.arg (.tail (.tail .head))) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
          (.cons .mul (.cons (.output (3 : Fin 4) .head) (.cons (.output (1 : Fin 4) .head) .nil)) .nil))))
  result := .output (4 : Fin 5) .head

theorem rotates_through_the_actual_ordered_right_addends :
    (step? original).map (rewrittenProgram original) = some expected := rfl

theorem original_result_addresses_skip_the_private_sum :
    (step? original).map (fun edit =>
      [(edit.route (.output (0 : Fin 4) .head)).address, (edit.route (.output (1 : Fin 4) .head)).address,
        (edit.route (.output (2 : Fin 4) .head)).address, (edit.route (.output (3 : Fin 4) .head)).address]) =
      some [.output 0 0, .output 1 0, .output 3 0, .output 4 0] := rfl

private def entry (x y z w : BitVec 64) : Tuple (Val model.value) args :=
  .cons x (.cons y (.cons z (.cons w .nil)))

private def returnPrivateSum : Program SubZero.Opcode inputs word :=
  { expected with result := .output (2 : Fin 5) .head }

theorem private_sum_wraps_and_downstream_observation_is_preserved :
    returnPrivateSum.eval model (entry 0xffffffffffffffff 0 1 2) = (0 : BitVec 64) ∧
    (step? original).map (fun edit =>
      ((rewrittenProgram original edit).eval model (entry 0xffffffffffffffff 0 1 2),
        (rewrittenProgram original edit).eval model (entry 5 7 11 13))) =
      some ((6 : BitVec 64), (864 : BitVec 64)) := ⟨rfl, rfl⟩

theorem refuses_earlier_swap_case_and_non_add_right :
    (step? (withOuter (.arg .head) (.output (1 : Fin 2) .head))).isNone = true ∧
    (step? (withOuter (.output (0 : Fin 2) .head) (.arg .head))).isNone = true :=
  ⟨rfl, rfl⟩

private def same := withOuter (.output (0 : Fin 2) .head) (.output (0 : Fin 2) .head)

theorem leaves_same_source_to_doubling :
    (step? same).isNone = true ∧ (ConstantFold.Doubling.step? same).isSome = true :=
  ⟨rfl, rfl⟩

private def rightZero : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 1) .nil
      (.cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
        (.cons .add (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .add (.cons (.output (2 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)) .nil))))
  result := .output (4 : Fin 5) .head

theorem leaves_a_known_zero_right_add_to_folding_and_identity :
    (step? rightZero).isNone = true ∧
    (RightIdentityPass.step? (ConstantFold.fold rightZero)).isSome = true :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Regression
