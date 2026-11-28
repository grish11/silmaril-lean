module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Thms
import Mathlib.Data.Nat.Pairing

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Comparison
open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL.Institution (LawfulModel)

private def model : PairModel Unit Part Nat :=
  ⟨{ unit := 0
     pair := Nat.pair
     inl := id
     inr := Nat.succ
     unpair n := pure (Nat.unpair n)
     split n := pure (.inl n)
     app _ n := pure (n + 1)
     abort _ := Part.none },
   ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩

private def collapse : Bool → Unit := fun _ => ()

example : ¬ Function.Injective collapse := by
  intro injective
  have same : false = true := injective rfl
  exact Bool.noConfusion same

private def reduct : PairModel Bool Part Nat := LawfulModel.reduct collapse model

/-- On packed one-field inputs this is the identity. On raw pairs the
tail is discarded. The unused block contains a real primitive call. -/
private def normalize : Graph Nat Bool 1 1 where
  locals := 2
  entry _ := .inl 0
  block i :=
    if i = 0 then
      ⟨0, .let2 1 2 (.val (.var 0)) (.term (.br (.inr 0) (.pair (.var 1) .unit)))⟩
    else
      ⟨0, .let1 1 (.app true (.var 0)) (.term (.br (.inr 0) (.var 1)))⟩
  closed i := by
    by_cases entry : i = 0 <;>
      simp [entry, Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def normalized : Profile normalize (fun _ => 1) (fun _ => 1) :=
  ⟨fun _ => 1, fun _ => rfl⟩

private def wire : Graph Nat Bool 1 1 := Graph.identity 1

private def wired : Profile wire (fun _ => 1) (fun _ => 1) :=
  ⟨Fin.elim0, fun _ => rfl⟩

private def project : Graph Nat Bool 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨0, .let2 1 2 (.val (.var 0)) (.let2 3 2 (.val (.var 2))
    (.term (.br (.inr 0) (.pair (.var 3) .unit))))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def projected : Profile project (fun _ => 2) (fun _ => 1) :=
  ⟨fun _ => 2, fun _ => rfl⟩

private theorem linked_verdict :
    refinement? (projected.link normalized) (projected.link wired) = some true := by cbv

example : refinement? ((projected.link normalized).mapOp collapse) ((projected.link wired).mapOp collapse) =
    some true := by
  rw [refinement?_mapOp, linked_verdict]

example : ∀ input, packedSat 2 model
    (namedSSAClass input (Quotient.mk _ ((project.link normalize).mapOp collapse)))
    (namedSSAClass input (Quotient.mk _ ((project.link wire).mapOp collapse))) :=
  ((refinement?_eq_some_packed_map_iff collapse model (separates_of_distinct reduct ⟨0, 1, by decide⟩)
    (projected.link normalized) (projected.link wired) true).mp linked_verdict).2.mp rfl

example : Sat (fun _ => 2) reduct (project.link normalize) (project.link wire) := by
  have typed : EntryTyped projected :=
    ((refinement?_eq_some_iff reduct (separates_of_distinct reduct ⟨0, 1, by decide⟩)
      projected projected true).mp (by cbv)).1.1
  exact Sat.link reduct projected typed (fun _ _ => le_rfl)
    (refinement_sound reduct normalized wired (by cbv))

private theorem normalizes_raw :
    normalize.denote reduct.val (0, Nat.pair 1 2) = Part.some (0, Nat.pair 1 0) := by
  have step : normalize.step reduct.val (.inl (0 : Fin 2), Nat.pair 1 2) =
      Part.some (.inr (.inr 0, Nat.pair 1 0)) := by
    simp [normalize, Graph.step, Body.evalJump, Body.exec, Op.eval, Term.exec, Val.eval, upd,
      reduct, LawfulModel.reduct, Model.reduct, model, Nat.unpair_pair]
  change iter (normalize.step reduct.val) (.inl (0 : Fin 2), Nat.pair 1 2) = _
  rw [congrFun (LawfulElgotMonad.fixpoint _) _, step, ← Part.pure_eq_some, pure_bind]
  change iter (normalize.step reduct.val) (.inr 0, Nat.pair 1 0) = _
  rw [congrFun (LawfulElgotMonad.fixpoint _) _]
  simp [Graph.step, Part.pure_eq_some]

private noncomputable def normalSide := namedSSAClass (0 : Fin 1) (Quotient.mk _ normalize : Arrow Nat Bool Nat 1 1)
private noncomputable def wireSide := namedSSAClass (0 : Fin 1) (Quotient.mk _ wire : Arrow Nat Bool Nat 1 1)

theorem packed_not_all_stores :
    packedSat 1 reduct normalSide wireSide ∧ ¬ Cyclic.Institution.Refinement.ssaSat reduct normalSide wireSide := by
  constructor
  · exact ((refinement?_eq_some_packed_iff reduct (separates_of_distinct reduct ⟨0, 1, by decide⟩)
      normalized wired true).mp (by cbv)).2.mp rfl 0
  · intro holds
    have atRaw := holds (fun _ => Nat.pair 1 2)
    change ssaClassObserve reduct (namedSSAClass (0 : Fin 1) (Quotient.mk _ normalize)) _ ≤
      ssaClassObserve reduct (namedSSAClass (0 : Fin 1) (Quotient.mk _ wire)) _ at atRaw
    rw [namedSSAClass_observe, namedSSAClass_observe, publicResult_le_iff] at atRaw
    change normalize.denote reduct.val (0, Nat.pair 1 2) ≤ wire.denote reduct.val (0, Nat.pair 1 2) at atRaw
    rw [normalizes_raw, wire, Graph.denote_identity] at atRaw
    have equal := Part.mem_some_iff.mp (atRaw _ (Part.mem_some _))
    exact (by decide : Nat.pair 1 0 ≠ Nat.pair 1 2) (congrArg Prod.snd equal)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
