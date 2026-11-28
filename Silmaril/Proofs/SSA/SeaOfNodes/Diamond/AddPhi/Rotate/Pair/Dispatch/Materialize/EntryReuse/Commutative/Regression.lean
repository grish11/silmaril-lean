module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]

/-- The entry order is y + x, while the suffix order is x + Phi.
The first Region occurrence is false and the second arm has an extra local. -/
private def source (sameOnSecond : Bool) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.arg (.tail .head)) (.cons (.output (0 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [[wordPort]], dataflow := .cons (.literal 8) .nil .nil
        outputs := .cons (if sameOnSecond then .arg (.tail .head) else .arg (.tail (.tail .head)))
          (.cons (.output (0 : Fin 3) .head) .nil) }

private def x : InputWord inputs := .tail (.tail .head)

private def entry (guard : Bool) (y x : BitVec 64) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons y (.cons x .nil))

theorem reversed_add_is_reused_only_in_commutative_mode :
    (rewrite (source true) x .left).toOption.bind (fun
      | .materialized .right _ p => do
        let target ← EntryReuse.Commutative.discoverAndRewrite? p
        pure ((EntryReuse.Discovery.discoverAndRewrite? p).isNone, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
          target.suffix.sigs.length, target.denote (entry false 3 0xffffffffffffffff),
          target.denote (entry true 3 0xffffffffffffffff))
      | _ => none) = some (true, ⟨.onFalse⟩, [.output 1 0, .arg 1], [.output 1 0, .arg 1], 2, 9, 9) := rfl

/-- Only the first occurrence matches. The observation at this input
coincides with unchecked reuse because the two distinct arguments both read 3. -/
theorem wrong_second_occurrence_is_refused_even_when_values_coincide :
    (rewrite (source false) x .left).toOption.bind (fun
      | .materialized .right value p => do
        let rep ← EntryReuse.findEntry? p (.output 1 0)
        let ⟨(lhs, rhs), _⟩ ← EntryReuse.addOperands? rep.key
        pure (EntryReuse.Commutative.matchesAt p lhs rhs .first,
          EntryReuse.Commutative.matchesAt p lhs rhs .second,
          (EntryReuse.Commutative.discoverAndRewrite? p).isNone,
          p.denote (entry true 3 3), (EntryReuse.emit p rep value).denote (entry true 3 3))
      | _ => none) = some (true, false, true, 13, 13) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Regression
