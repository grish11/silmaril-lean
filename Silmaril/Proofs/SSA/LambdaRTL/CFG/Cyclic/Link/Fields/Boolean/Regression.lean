module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Thms
import Mathlib.Data.Nat.Pairing

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Width (Profile)
open Comparison

private def model : BooleanModel Empty Nat where
  pairModel :=
    ⟨{ unit := 0
       pair := Nat.pair
       inl := id
       inr := Nat.succ
       unpair n := pure (Nat.unpair n)
       split n := if n = 1 then pure (.inl 0) else pure (.inr 0)
       app symbol := symbol.elim
       abort _ := Part.none },
     ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩
  bit flag := if flag then 1 else 0
  split_bit flag := by cases flag <;> rfl

-- Check the first field, and swap the fields on the back edge.
private def swapUntilTrue : Graph Nat Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨0, .let2 1 2 (.val (.var 0)) (.let2 3 4 (.val (.var 2))
    (.term (.case (.val (.var 1))
      5 (.br (.inr 0) (.var 0))
      5 (.br (.inl 0) (.pair (.var 3) (.pair (.var 1) .unit))))))⟩
  closed _ := by
    simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]
    decide

private def swapping : Profile swapUntilTrue (fun _ => 2) (fun _ => 2) :=
  ⟨fun _ => 2, fun _ => rfl⟩

private def packet (left right : Bool) : Packet 2 :=
  Fin.cons left (Fin.cons right Fin.elim0)

private noncomputable def side := namedSSAClass (0 : Fin 1) (Quotient.mk _ swapUntilTrue : Arrow Nat Empty Nat 1 1)

example : ssaClassObserve model.pairModel side (fun _ => encodePacket model (packet false false)) = Part.none := by
  have found : (entryOutcome swapping 0 (packet false false)).predict model = some Part.none := by cbv
  simpa [side] using
    namedSSA_entryOutcome_sound model swapping (0 : Fin 1) (packet false false)
      (fun _ => encodePacket model (packet false false)) rfl _ found

-- This input revisits the same label with a new packet before returning.
example : ssaClassObserve model.pairModel side (fun _ => encodePacket model (packet false true)) =
    Part.some (.inr 0, encodePacket model (packet true false)) := by
  have found : (entryOutcome swapping 0 (packet false true)).predict model =
      some (Part.some (0, encodePacket model (packet true false))) := by cbv
  simpa [side, publicResult] using
    namedSSA_entryOutcome_sound model swapping (0 : Fin 1) (packet false true)
      (fun _ => encodePacket model (packet false true)) rfl _ found

private def wire : Graph Nat Empty 1 1 := Graph.identity 1
private def wired : Profile wire (fun _ => 2) (fun _ => 2) := ⟨Fin.elim0, fun _ => rfl⟩

example : refinementAt? swapping wired 0 (packet false false) = some true := by cbv
example : refinementAt? swapping wired 0 (packet true false) = some true := by cbv
example : refinementAt? swapping wired 0 (packet false true) = some false := by cbv

private theorem different : refinement? swapping wired = some false := by cbv

example : ¬ (∀ input, packedSat 2 model
    (namedSSAClass input (Quotient.mk _ swapUntilTrue)) (namedSSAClass input (Quotient.mk _ wire))) := by
  have exactVerdict := ((refinement?_eq_some_packed_iff model swapping wired false).mp different).2
  exact fun holds => Bool.noConfusion (exactVerdict.mpr holds)

example : refinement? swapping swapping = some true := by cbv

private def nestedArm : Graph Nat Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨0, .let2 1 2 (.val (.var 0))
    (.term (.case (.val (.var 1)) 3 (.br (.inr 0) (.var 0))
      3 (.case (.val (.var 1)) 3 (.br (.inr 0) (.var 0)) 3 (.br (.inr 0) (.var 0)))))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def nestedProfile : Profile nestedArm (fun _ => 2) (fun _ => 2) := ⟨fun _ => 2, fun _ => rfl⟩

example : refinementAt? nestedProfile wired 0 (packet true false) = some true := by cbv
example : refinementAt? nestedProfile wired 0 (packet false false) = none := by cbv
example : refinement? nestedProfile wired = none := by cbv

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
