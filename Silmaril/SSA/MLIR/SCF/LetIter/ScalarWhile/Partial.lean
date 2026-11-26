module

public import Silmaril.SSA.MLIR.SCF.LetIter.ScalarWhile.Thms
public import Silmaril.Semantics.Elgot.Thms

/-! # Partial iteration for the deterministic scalar while

A successful step either yields the next before state or returns the result
of the parent continuation. Finite returns are membership in the Elgot
iteration in Part. In this total-primitive fragment, divergence is exactly an
undefined partial result.
-/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.ScalarWhile

open Arith (Width Env)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.Elgot (iter)

variable {Op : OpSignature} {Input Result : List Width}
variable (loop : While Op Input Result) (evalOp : Pure.Eval Op) (input : Env Input)

/-- The scalar step up to the while result or the next before state. -/
def stepToPayload (state : Env loop.State) : Env loop.Payload ⊕ Env loop.State :=
  let (test, payload) := loop.before.eval evalOp Condition.eval (state.append input)
  if test then .inr (loop.after.eval evalOp Yield.eval (payload.append input))
  else .inl payload

/-- A complete tick also runs the parent on the exiting branch. -/
def step (state : Env loop.State) : Env Result ⊕ Env loop.State :=
  Sum.map (fun payload => loop.cont.eval evalOp Return.eval (payload.append input)) id
    (stepToPayload loop evalOp input state)

/-- The scalar loop interpreted by the repository's finite-run iteration in Part. -/
noncomputable def denotePart : Part (Env Result) :=
  iter (fun state => Part.some (step loop evalOp input state)) (loop.init.eval input)

/-- Iterating to the while payload and sequencing the parent agrees with
the iteration that runs the parent on its exiting branch. -/
theorem denotePart_eq_iter_bind : denotePart loop evalOp input =
    (iter (fun state => Part.some (stepToPayload loop evalOp input state)) (loop.init.eval input)).bind
      (fun payload => Part.some (loop.cont.eval evalOp Return.eval (payload.append input))) := by
  let body := fun state => Part.some (stepToPayload loop evalOp input state)
  let parent := fun payload : Env loop.Payload => Part.some (loop.cont.eval evalOp Return.eval (payload.append input))
  have mapBody : Elgot.mapReturn body parent = fun state => Part.some (step loop evalOp input state) := by
    funext state
    cases h : stepToPayload loop evalOp input state <;>
      simp [Elgot.mapReturn, body, parent, step, h]
  have natural := congrFun (Elgot.Part.naturality body parent) (loop.init.eval input)
  rw [mapBody] at natural
  exact natural.symm

private theorem runFrom_step (fuel : Nat) (state : Env loop.State) :
    loop.runFrom evalOp input (fuel + 1) state =
      (step loop evalOp input state).elim some (loop.runFrom evalOp input fuel) := by
  cases h : loop.before.eval evalOp Condition.eval (state.append input) with
  | mk test payload => cases test <;> simp [While.runFrom, step, stepToPayload, h]

private theorem runs_iff_fuel {state : Env loop.State} {result : Env Result} :
    Elgot.Part.Runs (fun state => Part.some (step loop evalOp input state)) state result ↔
      ∃ fuel, loop.runFrom evalOp input fuel state = some result := by
  constructor
  · intro run
    induction run with
    | done ret =>
        exact ⟨1, by rw [runFrom_step, ← Part.mem_some_iff.mp ret]; rfl⟩
    | more again _ ih =>
        obtain ⟨fuel, run⟩ := ih
        exact ⟨fuel + 1, by rw [runFrom_step, ← Part.mem_some_iff.mp again]; exact run⟩
  · rintro ⟨fuel, run⟩
    induction fuel generalizing state with
    | zero => cases run
    | succ fuel ih =>
        rw [runFrom_step] at run
        cases h : step loop evalOp input state with
        | inl out =>
            rw [h] at run
            cases run
            exact .done (Part.mem_some_iff.mpr h.symm)
        | inr next =>
            rw [h] at run
            exact .more (Part.mem_some_iff.mpr h.symm) (ih run)

/-- A partial result is present exactly when the independent fuel evaluator returns it. -/
theorem mem_denotePart_iff (result : Env Result) :
    result ∈ denotePart loop evalOp input ↔ ∃ fuel, loop.run evalOp fuel input = some result :=
  (Elgot.Part.mem_iter_iff _ _ _).trans (runs_iff_fuel loop evalOp input)

/-- In the pure scalar model an undefined partial result means divergence. -/
theorem denotePart_eq_none_iff : denotePart loop evalOp input = Part.none ↔ loop.Diverges evalOp input := by
  rw [Part.eq_none_iff]
  constructor
  · intro noResult fuel
    cases h : loop.run evalOp fuel input with
    | none => rfl
    | some value => exact (noResult value ((mem_denotePart_iff loop evalOp input value).mpr ⟨fuel, h⟩)).elim
  · intro div value mem
    obtain ⟨fuel, run⟩ := (mem_denotePart_iff loop evalOp input value).mp mem
    rw [div fuel] at run
    cases run

end Silmaril.MLIR.SCF.LetIter.ScalarWhile

namespace Silmaril.MLIR.SCF.LetIter

/-- A loop body that always takes its backedge. Its return type is inhabited. -/
def repeatBool : Unit → Bool ⊕ Unit := Sum.inr

/-- Even the naturality equation at one inhabited return type excludes
total iteration. Boolean negation leaves the repeat body unchanged and
would have to fix the Boolean chosen for its result. -/
theorem total_repeat_not_natural
    (iterate : (Unit → Bool ⊕ Unit) → Unit → Bool)
    (naturality : ∀ (body : Unit → Bool ⊕ Unit) (cont : Bool → Bool),
      cont ∘ iterate body = iterate (Sum.map cont id ∘ body)) : False := by
  have fixed : Bool.not (iterate repeatBool ()) = iterate repeatBool () :=
    congrFun (naturality repeatBool Bool.not) ()
  cases h : iterate repeatBool () <;> simp [h] at fixed

/-- The same body is handled by undefinedness in the finite-run interpretation. -/
theorem repeatBool_partial :
    Elgot.iter (fun state => Part.some (repeatBool state)) () = Part.none :=
  Elgot.Part.iter_forever ()

end Silmaril.MLIR.SCF.LetIter
