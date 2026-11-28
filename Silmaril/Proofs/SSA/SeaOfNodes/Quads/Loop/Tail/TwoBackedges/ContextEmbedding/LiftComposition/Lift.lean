module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! Exact lifts with prescribed unused values and their sequential reconstruction. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Proofs

open SeaOfNodes.Diamond (dataPorts)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Composition (thenMap reduct_thenMap)
open Factorization (Consistent extendInput extendInput_unused liftChecked liftChecked_eq liftChecked_none_iff
  liftChecked_sound liftChecked_unused preimage preimage_isSome preimage_sound reduct_consistent reduct_image_iff)
open Identification (PortMap reduct reduct_get)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature}

private theorem reconstruct (map : PortMap S T) (target fill : Valuation T)
    (unused : AgreesOnUnused map target fill) : extendInput map (reduct map target) fill = target := by
  calc
    _ = tabulate (dataPorts T.regs) (fun p => target.get p) := by
      unfold extendInput
      apply congrArg (tabulate (dataPorts T.regs))
      funext sort port
      cases found : preimage map port with
      | none =>
        have miss : ¬ ∃ old, map sort old = port := by
          rw [← preimage_isSome map port, found]
          simp
        exact (unused sort port miss).symm
      | some old =>
        have hit := preimage_sound map port old found
        exact (reduct_get map target old).trans (congrArg (fun p => target.get p) hit)
    _ = target := tabulate_get_eq target

theorem lift_spec (map : PortMap S T) (input : Valuation S) (fill target : Valuation T) :
    liftChecked map input fill = some target ↔
      reduct map target = input ∧ AgreesOnUnused map target fill := by
  constructor
  · intro lifted
    exact ⟨liftChecked_sound map input fill target lifted, fun _ port =>
      liftChecked_unused map input fill target lifted port⟩
  · rintro ⟨rfl, unused⟩
    exact (liftChecked_eq map _ fill target).mpr ⟨(reconstruct map target fill unused).symm, reduct_consistent map target⟩

private theorem staged_checks (first : PortMap S T) (second : PortMap T U)
    (input : Valuation S) (fill : Valuation U) (mid : Valuation T) (target : Valuation U)
    (ok : liftStaged first second input fill = some (mid, target)) :
    liftChecked first input (intermediateFill first second input fill) = some mid ∧
      liftChecked second mid fill = some target := by
  unfold liftStaged at ok
  cases ran : liftChecked first input (intermediateFill first second input fill) with
  | none => simp [ran] at ok
  | some candidate =>
    cases finished : liftChecked second candidate fill with
    | none => simp [ran, finished] at ok
    | some final =>
      obtain ⟨rfl, rfl⟩ : candidate = mid ∧ final = target := by simpa [ran, finished] using ok
      exact ⟨rfl, finished⟩

theorem liftStaged_eq_map (first : PortMap S T) (second : PortMap T U)
    (input : Valuation S) (fill : Valuation U) :
    liftStaged first second input fill =
      (liftChecked (thenMap first second) input fill).map (fun target => (reduct second target, target)) := by
  cases direct : liftChecked (thenMap first second) input fill with
  | none =>
    cases ran : liftStaged first second input fill with
    | none => rfl
    | some pair =>
      obtain ⟨mid, target⟩ := pair
      obtain ⟨firstOk, secondOk⟩ := staged_checks first second input fill mid target ran
      have reduced : reduct (thenMap first second) target = input := by
        rw [reduct_thenMap first second, liftChecked_sound _ _ _ _ secondOk, liftChecked_sound _ _ _ _ firstOk]
      exact ((liftChecked_none_iff _ _ _).mp direct (reduced ▸ reduct_consistent _ target)).elim
  | some target =>
    have original := liftChecked_sound _ _ _ _ direct
    have fromFill : intermediateFill first second input fill = reduct second target :=
      congrArg (reduct second) ((liftChecked_eq _ _ _ _).mp direct).1.symm
    have firstOk : liftChecked first input (intermediateFill first second input fill) = some (reduct second target) := by
      rw [fromFill]
      exact (lift_spec _ _ _ _).mpr ⟨(reduct_thenMap first second _).symm.trans original, fun _ _ _ => rfl⟩
    have secondOk : liftChecked second (reduct second target) fill = some target := by
      apply (lift_spec _ _ _ _).mpr ⟨rfl, ?_⟩
      intro sort port unused
      apply liftChecked_unused _ _ _ _ direct port
      rintro ⟨old, hit⟩
      exact unused ⟨first sort old, hit⟩
    simp [liftStaged, firstOk, secondOk]

theorem liftStaged_spec (first : PortMap S T) (second : PortMap T U) (input : Valuation S) (fill : Valuation U)
    (mid : Valuation T) (target : Valuation U) :
    liftStaged first second input fill = some (mid, target) ↔
      reduct second target = mid ∧ reduct first mid = input ∧ AgreesOnUnused (thenMap first second) target fill := by
  constructor
  · intro ok
    obtain ⟨firstOk, secondOk⟩ := staged_checks first second input fill mid target ok
    have direct : liftChecked (thenMap first second) input fill = some target := by
      rw [liftStaged_eq_map] at ok
      simpa only [Option.map_map, Function.comp_def, Option.map_id_apply', Option.map_some] using
        congrArg (Option.map Prod.snd) ok
    exact ⟨liftChecked_sound _ _ _ _ secondOk, liftChecked_sound _ _ _ _ firstOk,
      (lift_spec _ _ _ _).mp direct |>.2⟩
  · rintro ⟨rfl, reduced, unused⟩
    have direct : liftChecked (thenMap first second) input fill = some target :=
      (lift_spec _ _ _ _).mpr ⟨(reduct_thenMap first second _).trans reduced, unused⟩
    rw [liftStaged_eq_map, direct]
    rfl

theorem image_through_iff (first : PortMap S T) (second : PortMap T U) (input : Valuation S) :
    Consistent (thenMap first second) input ↔
      ∃ mid, reduct first mid = input ∧ Consistent second mid := by
  constructor
  · intro consistent
    obtain ⟨target, reduced⟩ := (reduct_image_iff _ _).mpr consistent
    exact ⟨reduct second target, (reduct_thenMap first second target).symm.trans reduced, reduct_consistent second target⟩
  · rintro ⟨mid, reduced, consistent⟩
    obtain ⟨target, matched⟩ := (reduct_image_iff second mid).mpr consistent
    exact (reduct_image_iff _ _).mp ⟨target, (reduct_thenMap first second target).trans
      ((congrArg (reduct first) matched).trans reduced)⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Proofs
