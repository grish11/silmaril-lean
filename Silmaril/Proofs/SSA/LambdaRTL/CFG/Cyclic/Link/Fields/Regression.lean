module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms
import Mathlib.Data.Nat.Pairing

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

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

private def select (target : Label 1 1) (first second : Bool) : Graph Nat Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨0, .let2 1 2 (.val (.var 0))
    (.let2 3 2 (.val (.var 2))
      (.term (.br target (.pair (.var (if first then 3 else 1))
        (.pair (.var (if second then 3 else 1)) .unit)))))⟩
  closed _ := by
    cases first <;> cases second <;>
      simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]
    decide

private def swap : Graph Nat Empty 1 1 := select (.inr 0) true false
private def wire : Graph Nat Empty 1 1 := Graph.identity 1

private theorem different_fields : refinement? 2 swap wire = some false := by cbv

example : ¬ Sat 2 model swap wire := by
  have separates : Separates 2 model := separates_of_distinct model ⟨0, 1, by decide⟩
  have verdict := ((refinement?_eq_some_iff model separates swap wire false).mp different_fields).2
  exact fun included => Bool.noConfusion (verdict.mpr included)

private def firstTwice : Graph Nat Empty 1 1 := select (.inr 0) false false
private def secondTwice : Graph Nat Empty 1 1 := select (.inr 0) true true

-- The first stage changes which original field the second stage selects.
example : refinement? 2 (swap.link firstTwice) secondTwice = some true := by cbv
example : refinement? 2 (firstTwice.link swap) secondTwice = some false := by cbv

private def swappingLoop : Graph Nat Empty 1 1 := select (.inl 0) true false

example (packet : Fin 2 → Nat) :
    swappingLoop.denote model.val (0, encode model.val packet) = Part.none := by
  apply entryOutcome_sound model swappingLoop (0 : Fin 1) packet
  rw [show entryOutcome 2 swappingLoop 0 = .cycle (0 : Fin 1) by cbv]
  rfl

example : refinement? 2 swappingLoop swap = some true := by cbv
example : refinement? 2 swap swappingLoop = some false := by cbv

private def narrowing : Graph Nat Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨0, .let2 1 2 (.val (.var 0)) (.term (.br (.inr 0) (.pair (.var 1) .unit)))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

example : refinement? 2 narrowing wire = none := by cbv
example : refinement? 2 swappingLoop narrowing = none := by cbv

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields
