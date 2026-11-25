module

public import Silmaril.SSA.LambdaRTL.CFG.Thms

/-! Kernel fixtures for a checked exit-only alias, rejection of a capturing
alias, backward targets that miss the suffix, and monadic failure. -/

@[expose] public section
namespace Silmaril.SSA.LambdaRTL.CFG.LookupRelabel.Examples

private def source : CFG Nat Nat Unit :=
  ⟨.term (.case (.val (.var 0)) 1 (.br 10 (.var 0)) 1 (.br 11 (.var 0))),
    [(10, ⟨0, .term (.br 80 (.var 0))⟩), (11, ⟨0, .term (.br 81 (.var 0))⟩)]⟩

private def unifyReturns (label : Nat) : Nat := if label = 81 then 80 else label
private def aliasesHandler (label : Nat) : Nat := if label = 80 then 11 else label

private def model : Model Unit Option Nat where
  unit := 0
  pair a _ := a
  inl := id
  inr := id
  unpair _ := none
  split value := some (if value = 0 then .inr 0 else .inl 0)
  app _ _ := none
  abort _ := none

example : unifyReturns 80 = unifyReturns 81 := rfl
example : source.relabelLookupCheck unifyReturns = true := by decide
example (store : Nat → Nat) :
    (source.relabel unifyReturns).run model store =
      (fun outcome => (unifyReturns outcome.1, outcome.2)) <$> source.run model store :=
  run_relabel_of_check model unifyReturns source store (by decide)

example : (obs <$> (source.relabel unifyReturns).run model (fun _ => 1)) = some (80, 1) := rfl
example : (obs <$> (source.relabel unifyReturns).run model (fun _ => 0)) = some (80, 0) := rfl

example : source.relabelLookupCheck aliasesHandler = false := by decide
example : (obs <$> (source.relabel aliasesHandler).run model (fun _ => 1)) = some (81, 1) := rfl
example : ((fun out => (aliasesHandler out.1, out.2.1)) <$> source.run model (fun _ => 1)) =
    some (11, 1) := rfl

-- The branch back to 10 misses the remaining suffix and exits at its new name.
private def backwardExit : CFG Nat Nat Unit :=
  ⟨.term (.br 10 (.var 0)),
    [(10, ⟨0, .term (.br 10 (.var 0))⟩), (11, ⟨0, .term (.br 81 (.var 0))⟩)]⟩

example : backwardExit.relabelLookupCheck Nat.succ = true := by decide
example : (obs <$> (backwardExit.relabel Nat.succ).run model (fun _ => 7)) = some (11, 7) := rfl

private def failedOperation : CFG Nat Nat Unit :=
  ⟨.term (.br 10 (.var 0)),
    [(10, ⟨0, .let1 1 (.app () (.var 0)) (.term (.br 80 (.var 1)))⟩),
     (11, ⟨0, .term (.br 81 (.var 0))⟩)]⟩

example : failedOperation.relabelLookupCheck unifyReturns = true := by decide
example : failedOperation.run model (fun _ => 1) = none := rfl
example : (failedOperation.relabel unifyReturns).run model (fun _ => 1) = none := rfl

-- The older injective API is still available from the public header.
example (store : Nat → Nat) :
    (source.relabel Nat.succ).run model store =
      (fun outcome => (outcome.1.succ, outcome.2)) <$> source.run model store :=
  run_relabel model Nat.succ source (fun _ _ _ _ equality => Nat.succ.inj equality) store

end Silmaril.SSA.LambdaRTL.CFG.LookupRelabel.Examples
