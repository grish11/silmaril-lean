module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern (readId)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def x : InputWord inputs := .tail (.tail (.tail .head))
private def y : InputWord inputs := .tail (.tail .head)
private def z : InputWord inputs := .tail .head

/-- The shared operand and both arms compute (y + z) * y in separate
bindings. Both arms contain literal 8, and only the first introduces 9. -/
private def source (sameSecond : Bool) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg y) (.cons (.arg z) .nil))
      (.cons .mul (.cons (.output (1 : Fin 2) .head) (.cons (.arg y) .nil))
        (.cons .add (.cons (.arg x) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]
        dataflow := .cons (.literal 8) .nil
          (.cons .add (.cons (.arg y) (.cons (.arg z) .nil))
            (.cons .mul (.cons (.output (5 : Fin 6) .head) (.cons (.arg y) .nil))
              (.cons (.literal 9) .nil .nil)))
        outputs := .cons (.output (6 : Fin 8) .head) (.cons (.output (0 : Fin 8) .head) .nil) }
    | .second => {
        sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]
        dataflow := .cons (.literal 8) .nil
          (.cons (.literal 7) .nil
            (.cons .add (.cons (.arg y) (.cons (.arg (if sameSecond then z else y)) .nil))
              (.cons .mul (.cons (.output (6 : Fin 7) .head) (.cons (.arg y) .nil)) .nil)))
        outputs := .cons (.output (7 : Fin 8) .head) (.cons (.output (0 : Fin 8) .head) .nil) }

private def entry (guard : Bool) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (4 : BitVec 64) (.cons (3 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil)))

theorem repeated_chains_and_arm_literals_share_ids :
    (rewrite (source true) x .left).toOption.bind (fun
      | .materialized .right _ p =>
        let cuts := EntryReuse.Interned.numberCuts p
        some (readId cuts.entry cuts.shared (.output (2 : Fin 4) .head), cuts.first, cuts.second, cuts.table)
      | _ => none) =
    some (5, 5, 5, [.argument 1, .argument 2, .argument 3, .literal 7, .binary .add 1 0,
      .binary .mul 4 1, .binary .add 2 5, .literal 8, .literal 9]) := rfl

theorem actual_rewrite_forwards_the_representative_and_keeps_phi_wires :
    (rewrite (source true) x .left).toOption.bind (fun
      | .materialized .right _ p => do
        let target ← EntryReuse.Interned.discoverAndRewrite? p
        pure (target.diamond.merge, (target.diamond.arms .first).outputs.addresses,
          (target.diamond.arms .second).outputs.addresses, target.suffix.sigs.length,
          target.denote (entry false), target.denote (entry true))
      | _ => none) =
    some (⟨.onFalse⟩, [.output 3 0, .output 6 0], [.output 3 0, .output 7 0], 2, 27, 27) := rfl

theorem rejects_wrong_second_edge_child :
    (rewrite (source false) x .left).toOption.bind (fun
      | .materialized .right _ p =>
        let cuts := EntryReuse.Interned.numberCuts p
        some (readId cuts.entry cuts.shared (.output (2 : Fin 4) .head), cuts.first, cuts.second,
          (EntryReuse.Interned.discoverAndRewrite? p).isNone)
      | _ => none) = some (5, 5, 10, true) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.Regression
