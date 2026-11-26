module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms
import Mathlib.Data.Nat.Pairing

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Comparison

private def model : PairModel Empty Part Nat :=
  ⟨{ unit := 0
     pair := Nat.pair
     inl := id
     inr := Nat.succ
     unpair n := pure (Nat.unpair n)
     split n := pure (.inl n)
     app symbol := symbol.elim
     abort _ := Part.none },
   ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩

private def oneBlock (body : Body Nat (Label 1 1) Empty) (closed : body.toRegion.fv ⊆ {0}) :
    Graph Nat Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨0, body⟩
  closed _ := closed

private def project (second : Bool) : Graph Nat Empty 1 1 :=
  oneBlock (.let2 1 2 (.val (.var 0)) (.let2 3 2 (.val (.var 2))
    (.term (.br (.inr 0) (.pair (.var (if second then 3 else 1)) .unit))))) (by
      cases second <;> simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv])

private def projection (second : Bool) : Profile (project second) (fun _ => 2) (fun _ => 1) :=
  ⟨fun _ => 2, fun _ => rfl⟩

private def duplicate : Graph Nat Empty 1 1 :=
  oneBlock (.let2 1 2 (.val (.var 0))
    (.term (.br (.inr 0) (.pair (.var 1) (.pair (.var 1) .unit))))) (by
      simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv])

private def duplication : Profile duplicate (fun _ => 1) (fun _ => 2) :=
  ⟨fun _ => 1, fun _ => rfl⟩

example : Profile.certify (project true) (fun _ => 2) (fun _ => 1) (fun _ => 1) = none := by cbv

private def linked := (projection true).link duplication

example (packet : Fin 2 → Nat) :
    ((project true).link duplicate).denote model.val (0, encode model.val packet) =
      Part.some (0, encode model.val (fun _ : Fin 2 => packet 1)) := by
  apply entryOutcome_sound model linked (0 : Fin 1) packet
  cbv

example (packet : Fin 2 → Nat) :
    ssaClassObserve model
      (namedSSAClass (0 : Fin 1) (Quotient.mk _ ((project true).link duplicate)))
      (fun _ => encode model.val packet) = Part.some (.inr 0, encode model.val (fun _ : Fin 2 => packet 1)) := by
  have found : (entryOutcome linked 0).predict model.val packet =
      some (Part.some (0, encode model.val (fun _ : Fin 2 => packet 1))) := by cbv
  simpa [publicResult] using
    namedSSA_entryOutcome_sound model linked (0 : Fin 1) packet (fun _ => encode model.val packet) rfl _ found

private theorem different_projection : refinement? (projection true) (projection false) = some false := by cbv

example : ¬ Sat (fun _ => 2) model (project true) (project false) := by
  have exactVerdict := ((refinement?_eq_some_iff model (separates_of_distinct model ⟨0, 1, by decide⟩)
    (projection true) (projection false) false).mp different_projection).2
  exact fun included => Bool.noConfusion (exactVerdict.mpr included)

private def discard : Graph Nat Empty 1 1 :=
  oneBlock (.term (.br (.inr 0) .unit)) (by simp [Body.toRegion, Term.toRegion, Region.fv, Val.fv])

private def discarding : Profile discard (fun _ => 1) (fun _ => 0) :=
  ⟨fun _ => 1, fun _ => rfl⟩

private def emptyWire : Graph Nat Empty 1 1 := Graph.identity 1

private def emptyProfile : Profile emptyWire (fun _ => 0) (fun _ => 0) :=
  ⟨Fin.elim0, fun _ => rfl⟩

example : emptyWire.denote model.val (0, model.val.unit) = Part.some (0, model.val.unit) := by
  apply entryOutcome_sound model emptyProfile (0 : Fin 1) (fun i => Fin.elim0 i)
  cbv

example (packet : Fin 1 → Nat) :
    (discard.link emptyWire).denote model.val (0, encode model.val packet) = Part.some (0, model.val.unit) := by
  apply entryOutcome_sound model (discarding.link emptyProfile) (0 : Fin 1) packet
  cbv

example : Sat (fun _ => 1) model (discard.link emptyWire) discard := by
  have checked : refinement? (discarding.link emptyProfile) discarding = some true := by cbv
  exact ((refinement?_eq_some_iff model (fun _ _ => separatesWidths_zero model)
    (discarding.link emptyProfile) discarding true).mp checked).2.mp rfl

private def cycle : Graph Nat Empty 1 1 where
  locals := 2
  entry _ := .inl 0
  block i :=
    if i = 0 then ((project true).block (0 : Fin 1)).relabel (fun _ => .inl 1)
    else (duplicate.block (0 : Fin 1)).relabel (fun _ => .inl 0)
  closed i := by
    by_cases start : i = 0
    · simpa [start, Block.relabel, Graph.body_fv_relabel] using (project true).closed (0 : Fin 1)
    · simpa [start, Block.relabel, Graph.body_fv_relabel] using duplicate.closed (0 : Fin 1)

private def cyclic : Profile cycle (fun _ => 2) (fun _ => 2) :=
  ⟨fun (i : Fin 2) => if i = 0 then 2 else 1, fun _ => rfl⟩

example (packet : Fin 2 → Nat) :
    cycle.denote model.val (0, encode model.val packet) = Part.none := by
  apply entryOutcome_sound model cyclic (0 : Fin 1) packet
  rw [show entryOutcome cyclic 0 = .cycle (0 : Fin 2) by cbv]
  rfl

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
