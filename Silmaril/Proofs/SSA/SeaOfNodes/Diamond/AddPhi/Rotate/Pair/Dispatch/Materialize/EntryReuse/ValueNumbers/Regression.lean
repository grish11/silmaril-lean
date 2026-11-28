module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Origin Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

private def x : InputWord inputs := .tail (.tail (.tail .head))
private def y : InputWord inputs := .tail (.tail .head)
private def z : InputWord inputs := .tail .head

/-- The shared add uses (y + z) * y. The incoming arms independently
compute that word in different scopes, unless the second uses y twice. -/
private def source (sameOnSecond : Bool) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg y) (.cons (.arg z) .nil))
      (.cons .mul (.cons (.output (1 : Fin 2) .head) (.cons (.arg y) .nil))
        (.cons .add (.cons (.arg x) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [[wordPort], [wordPort]]
        dataflow := .cons .add (.cons (.arg y) (.cons (.arg z) .nil))
          (.cons .mul (.cons (.output (4 : Fin 5) .head) (.cons (.arg y) .nil)) .nil)
        outputs := .cons (.output (5 : Fin 6) .head) (.cons (.output (0 : Fin 6) .head) .nil) }
    | .second => {
        sigs := [[wordPort], [wordPort], [wordPort]]
        dataflow := .cons (.literal 8) .nil
          (.cons .add (.cons (.arg y) (.cons (.arg (if sameOnSecond then z else y)) .nil))
            (.cons .mul (.cons (.output (5 : Fin 6) .head) (.cons (.arg y) .nil)) .nil))
        outputs := .cons (.output (6 : Fin 7) .head) (.cons (.output (0 : Fin 7) .head) .nil) }

private def entry (guard : Bool) (zValue : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons zValue (.cons (3 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil)))

theorem reuses_entry_add_across_separately_computed_chains :
    (rewrite (source true) x .left).toOption.bind (fun
      | .materialized .right _ p => do
        let target ← EntryReuse.ValueNumbers.discoverAndRewrite? p
        pure ((EntryReuse.Discovery.discoverAndRewrite? p).isNone,
          (EntryReuse.Commutative.discoverAndRewrite? p).isNone, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
          target.suffix.sigs.length, target.denote (entry false 4), target.denote (entry true 4))
      | _ => none) =
    some (true, true, ⟨.onFalse⟩, [.output 3 0, .output 5 0], [.output 3 0, .output 6 0], 2, 27, 27) := rfl

theorem rejects_nested_operand_mismatch_despite_coinciding_sample :
    (rewrite (source false) x .left).toOption.bind (fun
      | .materialized .right value p => do
        let rep ← EntryReuse.findEntry? p (.output 3 0)
        let ⟨(_, rhs), _⟩ ← EntryReuse.addOperands? rep.key
        let shared := EntryReuse.ValueNumbers.sharedKeys p
        let key := EntryReuse.ValueNumbers.operandKey shared rhs
        let unchecked := EntryReuse.emit p rep value
        pure (key.matches (EntryReuse.ValueNumbers.phiKey p shared .first),
          key.matches (EntryReuse.ValueNumbers.phiKey p shared .second),
          (EntryReuse.ValueNumbers.discoverAndRewrite? p).isNone,
          p.denote (entry true 3), unchecked.denote (entry true 3),
          p.denote (entry true 4), unchecked.denote (entry true 4))
      | _ => none) = some (true, false, true, 24, 24, 24, 27) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Regression
