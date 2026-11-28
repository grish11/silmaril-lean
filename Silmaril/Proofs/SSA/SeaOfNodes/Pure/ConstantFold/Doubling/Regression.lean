module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Thms
import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.AddRewrite (rewrittenProgram)
open ConstantFold.Doubling (step?)
open Diamond (Val dataPorts)
open SubZero (model word)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs := [word, word]

private def original : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .add (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

private def expected : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons (.literal 2) .nil
        (.cons .mul (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))
          (.cons .add (.cons (.output (3 : Fin 4) .head) (.cons (.arg (.tail .head)) .nil)) .nil))))
  result := .output (4 : Fin 5) .head

theorem inserts_two_and_routes_the_same_source_and_downstream_use :
    (step? original).map (rewrittenProgram original) = some expected := rfl

private def entry (x y : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons x (.cons y .nil)

theorem doubling_signed_minimum_wraps_to_zero_before_downstream_use :
    (step? original).map (fun edit =>
      (rewrittenProgram original edit).eval model (entry 0x8000000000000000 7)) = some (7 : BitVec 64) := rfl

private def afterIdentity : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0) .nil
    (.cons (.literal 2) .nil
      (.cons .mul (.cons (.arg .head) (.cons (.output (1 : Fin 2) .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

theorem existing_right_identity_rewrites_the_new_multiplications_left_wire :
    ((step? original).map (rewrittenProgram original)).bind RightIdentityPass.step? =
      some afterIdentity := rfl

private def distinct : Program SubZero.Opcode inputs word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil
  result := .output (0 : Fin 1) .head

theorem rejects_distinct_wires_even_on_equal_inputs :
    (step? distinct).isNone = true ∧ distinct.eval model (entry 7 7) = (14 : BitVec 64) :=
  ⟨rfl, rfl⟩

private def literals : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .sub (.cons (.arg .head) (.cons (.arg .head) .nil))
        (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

private def folded : Program SubZero.Opcode inputs word where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 0xfffffffffffffffe) .nil
      (.cons (.literal 0) .nil
        (.cons (.literal 0) .nil .nil)))
  result := .output (3 : Fin 4) .head

theorem defers_explicit_literals_and_a_propagated_zero_to_literal_folding :
    (step? literals).isNone = true ∧ ConstantFold.fold literals = folded :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Regression
