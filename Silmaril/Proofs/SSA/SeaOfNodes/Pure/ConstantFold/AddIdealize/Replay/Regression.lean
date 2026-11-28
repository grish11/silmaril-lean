module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Regression

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold
open AddIdealize.Replay (run)
open LeftSpine (SourceIds)
open SubZero (model word)

private abbrev WordProgram := Program SubZero.Opcode [word, word] word

private def missing : SourceIds := ⟨fun _ => none⟩

private def literalLeft : WordProgram where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil))
      (.cons .mul (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil)) .nil))
  result := .output (2 : Fin 3) .head

private def erased : WordProgram where
  dataflow := .cons (.literal 0) .nil
    (.cons .mul (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil)
  result := .output (1 : Fin 2) .head

private def replayed := run 2 missing literalLeft (.later .here)

theorem swap_exposes_erasure_and_rewrites_the_suffix :
    replayed.rules = [.offSpineSwap, .rightZero] ∧ replayed.stop = .argument ∧
    AddRewrite.rewrittenProgram literalLeft replayed.rewrite = erased :=
  ⟨rfl, rfl, rfl⟩

theorem composed_route_redirects_the_old_add_and_shifts_the_suffix :
    (replayed.rewrite.route (.output (1 : Fin 3) .head) (t := SubZero.wordPort)).address = .arg 0 ∧
    (replayed.rewrite.route literalLeft.result).address = .output 1 0 :=
  ⟨rfl, rfl⟩

theorem replayed_suffix_still_wraps :
    (AddRewrite.rewrittenProgram literalLeft replayed.rewrite).eval model
      (.cons (0xffffffffffffffff : BitVec 64) (.cons (2 : BitVec 64) .nil)) =
      (0xfffffffffffffffe : BitVec 64) := rfl

theorem one_unit_stops_after_the_swap :
    let result := run 1 missing literalLeft (.later .here)
    result.rules = [.offSpineSwap] ∧ result.stop = .fuelExhausted :=
  ⟨rfl, rfl⟩

private def pair : WordProgram where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil
  result := .output (0 : Fin 1) .head

private def ordered : SourceIds where
  lookup
    | .arg 0 => some (-25)
    | .arg 1 => some 31
    | _ => none

theorem distinguishes_missing_ids_from_no_edit_after_a_swap :
    let result := run 2 ordered pair .here
    (run 2 missing pair .here).stop = .refused .missingSourceIds ∧
    result.rules = [.offSpineSwap] ∧ result.stop = .noEdit :=
  ⟨rfl, rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Regression
