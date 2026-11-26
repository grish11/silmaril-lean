module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.AddIdealize (Applied Outcome Rule step)
open ConstantFold.AddRewrite (rewrittenProgram)
open ConstantFold.LeftSpine (SourceIds)
open ConstantFold.RightSpine (WordWire)
open Diamond (dataPorts)
open GVN (Producer)
open SubZero (word wordPort)

private abbrev inputs := [word, word, word]
private abbrev args := dataPorts inputs
private abbrev WordProgram := Program SubZero.Opcode inputs word

private def missing : SourceIds := ⟨fun _ => none⟩

private def order (y z : Int32) : SourceIds where
  lookup
    | .arg 1 => some y
    | .arg 2 => some z
    | _ => none

private def selectedRule (ids : SourceIds) (program : WordProgram)
    (candidate : Producer program.dataflow word) : Outcome Rule :=
  (step ids program candidate).map (Option.map Applied.rule)

private def constantZero : WordProgram where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

private def foldedZero : WordProgram where
  dataflow := .cons (.literal 0) .nil (.cons (.literal 0) .nil .nil)
  result := .output (1 : Fin 2) .head

theorem literal_fold_precedes_right_zero_and_doubling :
    (step missing constantZero (.later .here)).map (Option.map fun applied =>
      (applied.rule, rewrittenProgram constantZero applied.rewrite)) = .ok (some (.literal, foldedZero)) := rfl

private def identity : WordProgram where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil))
      (.cons .mul (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil)) .nil))
  result := .output (2 : Fin 3) .head

private def afterIdentity : WordProgram where
  dataflow := .cons (.literal 0) .nil
    (.cons .mul (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil)
  result := .output (1 : Fin 2) .head

theorem explicit_right_zero_erases_and_routes_downstream_use :
    (step missing identity (.later .here)).map (Option.map fun applied =>
      (applied.rule, rewrittenProgram identity applied.rewrite)) = .ok (some (.rightZero, afterIdentity)) := rfl

private def knownZero : WordProgram where
  dataflow := .cons .sub (.cons (.arg .head) (.cons (.arg .head) .nil))
    (.cons .add (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

theorem refuses_the_higher_priority_zero_branch_without_an_explicit_literal :
    selectedRule (order 25 31) knownZero (.later .here) = .error (.outsideRuleProfile .rightZero) := rfl

private def twoAdds (lhs rhs : WordWire args [[wordPort], [wordPort]]) : WordProgram where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons .add (.cons lhs (.cons rhs .nil)) .nil))
  result := .output (2 : Fin 3) .head

theorem doubling_precedes_right_spine_and_distinct_adds_rotate :
    selectedRule missing (twoAdds (.output (0 : Fin 2) .head) (.output (0 : Fin 2) .head))
      (.later (.later .here)) = .ok (some .doubling) ∧
    selectedRule missing (twoAdds (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head))
      (.later (.later .here)) = .ok (some .rightSpine) := ⟨rfl, rfl⟩

private def nonAddLeft : WordProgram := twoAdds (.arg .head) (.output (1 : Fin 2) .head)

theorem non_add_left_swaps_before_the_right_add_rotation :
    (step missing nonAddLeft (.later (.later .here))).map (Option.map fun applied =>
      (applied.rule, rewrittenProgram nonAddLeft applied.rewrite)) =
      .ok (some (.nonAddLeftSwap, twoAdds (.output (1 : Fin 2) .head) (.arg .head))) := rfl

private def chainTable (computed : Bool) : WordProgram where
  dataflow := .cons (.literal 1) .nil
    (if computed then
      .cons .mul (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
          (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil))
    else
      .cons (.literal 2) .nil
        (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
          (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))
  result := .output (3 : Fin 4) .head

theorem constant_chain_is_selected_or_refused_at_its_own_branch :
    selectedRule missing (chainTable false) (.later (.later (.later .here))) = .ok (some .constantChain) ∧
    selectedRule missing (chainTable true) (.later (.later (.later .here))) =
      .error (.outsideRuleProfile .constantChain) := ⟨rfl, rfl⟩

private def leftSpine : WordProgram where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail (.tail .head))) .nil)) .nil)
  result := .output (1 : Fin 2) .head

theorem left_spine_distinguishes_signed_order_false_and_missing_evidence :
    selectedRule (order (-25) 31) leftSpine (.later .here) = .ok (some .leftSpine) ∧
    selectedRule (order 31 (-25)) leftSpine (.later .here) = .ok none ∧
    selectedRule missing leftSpine (.later .here) = .error .missingSourceIds := ⟨rfl, rfl, rfl⟩

private def offSpine (lhs rhs : WordWire args []) : WordProgram where
  dataflow := .cons .add (.cons lhs (.cons rhs .nil)) .nil
  result := .output (0 : Fin 1) .head

private def orderedPair : WordProgram := offSpine (.arg (.tail .head)) (.arg (.tail (.tail .head)))

theorem off_spine_swaps_on_signed_order_and_distinguishes_false_from_missing :
    (step (order (-25) 31) orderedPair .here).map (Option.map fun applied =>
      (applied.rule, rewrittenProgram orderedPair applied.rewrite)) =
      .ok (some (.offSpineSwap, offSpine (.arg (.tail (.tail .head))) (.arg (.tail .head)))) ∧
    selectedRule (order 31 (-25)) orderedPair .here = .ok none ∧
    selectedRule missing orderedPair .here = .error .missingSourceIds :=
  ⟨rfl, rfl, rfl⟩

private def literalLeftZero : WordProgram where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil))
      (.cons .mul (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil)) .nil))
  result := .output (2 : Fin 3) .head

theorem literal_left_swaps_without_ids_and_retains_the_new_identity_add :
    (step missing literalLeftZero (.later .here)).map (Option.map fun applied =>
      (applied.rule, rewrittenProgram literalLeftZero applied.rewrite)) = .ok (some (.offSpineSwap, identity)) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression
