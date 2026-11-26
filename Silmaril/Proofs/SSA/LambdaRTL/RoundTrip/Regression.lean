module

import Silmaril.SSA.LambdaRTL.RoundTrip.Thms

namespace Silmaril.Proofs.SSA.LambdaRTL.RoundTrip.Regression

open Silmaril.SSA.LambdaRTL

private inductive Value where
  | word (n : Nat)
  | pair (left right : Value)
  | inl (value : Value)
  | inr (value : Value)

private def model : Model Empty Option Value where
  unit := .word 0
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => some (a, b)
    | _ => none
  split
    | .inl a => some (.inl a)
    | .inr a => some (.inr a)
    | _ => none
  app op _ := op.elim
  abort _ := none

private theorem pairs : model.PairLawful := ⟨fun _ _ => rfl⟩

-- The left branch overwrites register 2 before jumping to a handler that
-- reads it. The right branch exits directly with the original value.
private def source : Region Nat Nat Empty :=
  .join
    (.case (.val (.var 0)) 1
      (.let1 2 (.val (.var 1)) (.br 10 .unit))
      1 (.br 99 (.var 2)))
    10 3 (.br 42 (.var 2))

private def input (condition : Value) : Nat → Value
  | 0 => condition
  | 2 => .word 7
  | _ => .word 0

private noncomputable def recovered : Region Nat Nat Empty :=
  (Version.versionTop source).rename (RoundTrip.deversion (Version.versionTop source).vars)

-- The lexical reading of the original program does not see the mutation.
example : source.evalSSA model (input (.inl (.word 5))) = some (42, .word 7) := rfl

example : recovered.evalObs model (input (.inl (.word 5))) = some (42, .word 5) := by
  rw [recovered, roundTrip_evalObs model pairs]
  rfl

example : recovered.evalObs model (input (.inr (.word 5))) = some (99, .word 7) := by
  rw [recovered, roundTrip_evalObs model pairs]
  rfl

end Silmaril.Proofs.SSA.LambdaRTL.RoundTrip.Regression
