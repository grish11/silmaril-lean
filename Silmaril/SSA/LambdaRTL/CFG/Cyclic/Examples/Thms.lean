module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
import Silmaril.Semantics.Elgot.Thms

/-! The edge from block 20 to block 10 is taken twice. Block 10 stops when the
countdown reaches zero and returns the number of visits to block 20. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Examples

open Silmaril.Elgot

private def model : Model Unit Part Nat where
  unit := 0
  pair := Nat.add
  inl := id
  inr := Nat.succ
  unpair _ := Part.none
  split
    | 0 => pure (.inl 0)
    | n + 1 => pure (.inr n)
  app _ n := pure (n + 1)
  abort _ := Part.none

-- Register false holds the countdown and register true counts visits.
private def registers (count visits : Nat) : Bool → Nat
  | false => count
  | true => visits

@[simp] private theorem registers_false (count visits : Nat) :
    registers count visits false = count := rfl

@[simp] private theorem registers_true (count visits : Nat) :
    registers count visits true = visits := rfl

private def header : Block Bool Nat Unit :=
  ⟨false, .term (.case (.val (.var false))
    false (.br 99 (.var true)) false (.br 20 (.var false)))⟩

private def loop : CFG Bool Nat Unit :=
  ⟨.term (.br 10 (.var false)),
    [(10, header), (20, ⟨false, .let1 true (.app () (.var true)) (.term (.br 10 (.var false)))⟩)]⟩

private theorem updateCount (count visits next : Nat) :
    upd (registers count visits) false next = registers next visits := by
  funext reg
  cases reg <;> rfl

private theorem updateVisits (count visits next : Nat) :
    upd (registers count visits) true next = registers count next := by
  funext reg
  cases reg <;> rfl

private theorem header_more (count visits : Nat) :
    step model loop.blocks (10, count + 1, registers (count + 1) visits) =
      Part.some (.inr (20, count, registers count visits)) := by
  simp [step, loop, header, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, model]

private theorem body_step (count visits : Nat) :
    step model loop.blocks (20, count, registers count visits) =
      Part.some (.inr (10, count, registers count (visits + 1))) := by
  simp [step, loop, List.lookup, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, updateVisits, model]

private theorem header_exit (visits : Nat) :
    step model loop.blocks (10, 0, registers 0 visits) =
      Part.some (.inr (99, visits, registers 0 visits)) := by
  simp [step, loop, header, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, model]

private theorem exit_step (visits : Nat) :
    step model loop.blocks (99, visits, registers 0 visits) =
      Part.some (.inl (99, visits, registers 0 visits)) := rfl

-- The second and fourth transitions take the back edge and pass the updated store.
example : Cyclic.run model loop (registers 2 0) = Part.some (99, 2, registers 0 2) := by
  change iter (step model loop.blocks) (10, 2, registers 2 0) = Part.some _
  apply Part.eq_some_iff.mpr
  apply (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
  exact .more (Part.eq_some_iff.mp (header_more 1 0)) <|
    .more (Part.eq_some_iff.mp (body_step 1 0)) <|
    .more (Part.eq_some_iff.mp (header_more 0 1)) <|
    .more (Part.eq_some_iff.mp (body_step 0 1)) <|
    .more (Part.eq_some_iff.mp (header_exit 2)) <|
    .done (Part.eq_some_iff.mp (exit_step 2))

-- Suffix lookup reports the label of the first backward transfer as its exit.
example : loop.run model (registers 2 0) = Part.some (10, 1, registers 1 1) := by
  simp [CFG.run, loop, header, jump, Body.exec, Term.exec, Op.eval, Val.eval,
    updateCount, updateVisits, model]

example : ¬ IsForward loop := by
  intro forward
  have bad := forward.2.1 10 (by simp [Body.targets, Term.targets])
  simp [loop, List.lookup] at bad

private def forwardGraph : CFG Bool Nat Unit :=
  ⟨loop.entry, [(10, header), (20, ⟨false, .term (.br 99 (.var true))⟩)]⟩

example (store : Bool → Nat) :
    Cyclic.run model forwardGraph store = forwardGraph.run model store :=
  run_eq_forward model forwardGraph (by
    simp [IsForward, ForwardTargets, forwardGraph, header, Body.targets, Term.targets, List.lookup])
    store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Examples
