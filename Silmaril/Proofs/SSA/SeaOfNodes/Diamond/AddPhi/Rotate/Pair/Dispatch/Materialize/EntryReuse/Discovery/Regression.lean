module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize (rewrite)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse (check)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery
open Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass (wordProducers)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]

/-- Shared word producers occur as literal, reversed add, and two
ordered adds (or subs). The true arm has one additional local add. -/
private def source (duplicates sameOperand : Bool) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (if duplicates then .add else .sub)
        (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil))
        (.cons (if duplicates then .add else .sub)
          (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil)) .nil)))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.arg (.tail .head)) (.cons (.output (0 : Fin 4) .head) .nil) }
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .add
          (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil)) .nil
        outputs := .cons (if sameOperand then .arg (.tail .head) else .arg (.tail (.tail .head)))
          (.cons (.output (0 : Fin 5) .head) .nil) }

private def x : InputWord inputs := .tail (.tail .head)

private def input (guard : Bool) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (3 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))

private def rightMaterialized (duplicates sameOperand : Bool) :=
  (rewrite (source duplicates sameOperand) x .left).toOption.bind fun
    | .materialized .right _ emitted => some emitted
    | _ => none

theorem skips_reversed_add_and_chooses_first_of_two_accepted :
    (rightMaterialized true true).map (fun p =>
      ((wordProducers p.diamond.shared).map (fun rep => (rep.origin.address, check p rep)),
        (findRepresentative? p).map (fun rep => rep.origin.address))) =
      some ([(.output 0 0, false), (.output 1 0, false), (.output 2 0, true), (.output 3 0, true)],
        some (.output 2 0)) := rfl

theorem actual_rewrite_forwards_selected_entry_on_both_occurrences :
    ((rightMaterialized true true).bind discoverAndRewrite?).map (fun target =>
      (target.diamond.merge, (target.diamond.arms .first).outputs.addresses,
        (target.diamond.arms .second).outputs.addresses, target.suffix.sigs.length,
        target.denote (input false), target.denote (input true))) =
      some (⟨.onFalse⟩, [.output 2 0, .arg 1], [.output 2 0, .arg 1], 2, 9, 9) := rfl

private def tryOnMaterialized (duplicates sameOperand : Bool) :
    Option (Option (Program inputs sigs [word, word])) :=
  (rightMaterialized duplicates sameOperand).map discoverAndRewrite?

theorem refuses_arm_local_only_match_and_mismatched_second_occurrence :
    tryOnMaterialized false true = some none ∧ tryOnMaterialized true false = some none :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Regression
