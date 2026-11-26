module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Thms
import Mathlib.Data.Nat.Pairing

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Width (Profile)
open Comparison

private def modelWithApp {F : Type} (app : F → Nat → Part Nat) : BooleanModel F Nat where
  pairModel :=
    ⟨{ unit := 0
       pair := Nat.pair
       inl := id
       inr := Nat.succ
       unpair n := pure (Nat.unpair n)
       split n := if n = 1 then pure (.inl 0) else pure (.inr 0)
       app := app
       abort _ := Part.none },
     ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩
  bit flag := if flag then 1 else 0
  split_bit flag := by cases flag <;> rfl

private def model : BooleanModel Empty Nat := modelWithApp Empty.elim

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

example : primitiveRefinement? [] swapping wired = refinement? swapping wired := by cbv

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

section Primitive

private def setIfFalse (arg : Nat) : Part Nat :=
  if arg = 0 then Part.some 1 else Part.none

private def primitiveModel : BooleanModel Unit Nat := modelWithApp (fun _ => setIfFalse)

private def table : PrimitiveTable Unit := [((), ⟨some true, none⟩)]

private theorem compatible : table.Compatible primitiveModel := by
  intro symbol row found arg
  cases symbol
  have same : (⟨some true, none⟩ : PrimitiveRow) = row := Option.some.inj found
  subst row
  cases arg <;> rfl

private def testBody : Body Nat (Label 2 1) Unit :=
  .let2 1 2 (.val (.var 0)) (.term (.case (.val (.var 1))
    3 (.br (.inr 0) (.var 0)) 3 (.br (.inl 1) (.var 0))))

private def updateBody : Body Nat (Label 2 1) Unit :=
  .let2 1 2 (.val (.var 0)) (.let1 1 (.app () (.var 1))
    (.term (.br (.inl 0) (.pair (.var 1) (.var 2)))))

-- Entry 0 tests the bit. Entry 1 goes straight to the primitive.
private def updatingGraph : Graph Nat Unit 2 1 where
  locals := 2
  entry i := .inl i
  block i := ⟨0, if i = 0 then testBody else updateBody⟩
  closed i := by
    by_cases first : i = 0
    · simp [first, testBody, Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]
    · simp [first, updateBody, Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]
      decide

private def updating : Profile updatingGraph (fun _ => 1) (fun _ => 1) :=
  ⟨fun _ => 1, fun _ => rfl⟩

private def direct : Graph Nat Unit 2 1 where
  locals := 0
  entry _ := .inr 0
  block := Fin.elim0
  closed i := i.elim0

private def directProfile : Profile direct (fun _ => 1) (fun _ => 1) :=
  ⟨Fin.elim0, fun _ => rfl⟩

private def single (flag : Bool) : Packet 1 := fun _ => flag

-- A false input returns true after revisiting the test with a changed packet.
example :
    ssaClassObserve primitiveModel.pairModel (namedSSAClass 0 (Quotient.mk _ updatingGraph))
      (fun _ => encodePacket primitiveModel (single false)) =
      Part.some (.inr 0, encodePacket primitiveModel (single true)) := by
  have found : (primitiveEntryOutcome table updating 0 (single false)).predict primitiveModel =
      some (Part.some (0, encodePacket primitiveModel (single true))) := by cbv
  simpa [publicResult] using
    namedSSA_primitiveEntryOutcome_sound table primitiveModel compatible updating 0 (single false)
      (fun _ => encodePacket primitiveModel (single false)) rfl _ found

-- The same instruction on true is certified undefined when its row is present.
example : (match primitiveEntryOutcome table updating 1 (single true) with
    | .undefined _ => true
    | _ => false) = true := by cbv

example :
    ssaClassObserve primitiveModel.pairModel (namedSSAClass 1 (Quotient.mk _ updatingGraph))
      (fun _ => encodePacket primitiveModel (single true)) = Part.none := by
  have found : (primitiveEntryOutcome table updating 1 (single true)).predict primitiveModel = some Part.none := by cbv
  simpa [publicResult] using
    namedSSA_primitiveEntryOutcome_sound table primitiveModel compatible updating 1 (single true)
      (fun _ => encodePacket primitiveModel (single true)) rfl _ found

example : (primitiveEntryOutcome [] updating 1 (single true)).predict primitiveModel = none := by cbv

-- A listed opcode still requires a typed Boolean argument.
example : (primitiveBlock table (fun _ : Fin 1 => 1)
    (⟨0, .let1 1 (.app () .unit) (.term (.br 0 (.var 0)))⟩ : Block Nat (Fin 1) Unit)
    (single false)).predict (At.render primitiveModel) = none := by cbv

example : refinementAtWith? updating directProfile (primitiveAdvance table updating)
    (primitiveAdvance table directProfile) 1 (single true) = some true := by cbv

example : refinementAtWith? updating directProfile (primitiveAdvance [] updating)
    (primitiveAdvance [] directProfile) 1 (single true) = none := by cbv

example : primitiveRefinement? [] updating directProfile = none := by cbv

example : primitiveRefinement? table updating updating = some true := by cbv

example : ¬ (∀ input, packedSat 1 primitiveModel
    (namedSSAClass input (Quotient.mk _ updatingGraph)) (namedSSAClass input (Quotient.mk _ direct))) := by
  have different : primitiveRefinement? table updating directProfile = some false := by cbv
  have exactVerdict :=
    ((primitiveRefinement?_eq_some_packed_iff table primitiveModel compatible updating directProfile false).mp different).2
  exact fun holds => Bool.noConfusion (exactVerdict.mpr holds)

end Primitive

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
