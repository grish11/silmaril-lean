module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Thms

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Pure

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Execution.Core.Intrinsic.Pure
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {locals input middle output : List IntType}

theorem eval_append (frame : Values locals) (left : Code locals input middle)
    (right : Code locals middle output) (stack : Values input) :
    eval frame (left.append right) stack = (eval frame left stack).bind (eval frame right) := by
  induction left with
  | done => rfl
  | seq op tail ih =>
    simp only [Code.append, eval]
    split
    · exact ih right _
    · rfl

private theorem run_final_trap {H : Type} {context : Validation.Context} {world : World H context}
    (frame : LocalFrame world locals) (fuel : Nat) :
    (State.mk (results := output) frame (.trapping .nil .done)).runFor fuel =
      State.mk frame (.trapping .nil .done) := by
  cases fuel <;> rfl

theorem run_eval {H : Type} {context : Validation.Context} {world : World H context}
    (frame : LocalFrame world locals) (code : Code locals input output) (stack : Values input) :
    ((State.mk frame (.run stack code)).runFor (budget code)).control.result? =
      some (eval frame.values code stack) := by
  induction code with
  | done => rfl
  | seq op tail ih =>
    simp only [budget, State.runFor, State.step?, Control.step?, Option.map_some, eval]
    cases effect : op.eval frame.values stack with
    | next values => exact ih values
    | trap saved =>
      simp only [Effect.resume]
      cases tail <;> cases saved <;>
        simp [budget, State.runFor, State.step?, Control.step?, run_final_trap,
          Control.result?, Code.isEmpty, Values.isEmpty]

theorem invoke_denotes {H : Type} {context : Validation.Context} {world : World H context}
    {parameters results : List IntType} (call : DirectCall world parameters results)
    (args : Values parameters) (oracle : GrowOracle) :
    behaviours (profile oracle) noHost world.store call.address args.erase =
      {(invokeResult (denotes call.body args)).toBehaviour} :=
  call.invoke_behaviours (oracle := oracle) args (run_eval _ _ _)

private theorem denotes_cast {parameters declared other results : List IntType}
    (body : Code (parameters ++ declared) [] results) (args : Values parameters)
    (equal : declared = other) : denotes (equal ▸ body) args = denotes body args := by
  subst other
  rfl

theorem linked_observation {parameters declared results : List IntType}
    {body : Code (parameters ++ declared) [] results} (entry : Linked body)
    (args : Values parameters) (oracle : GrowOracle) :
    behaviours (profile oracle) noHost entry.world.store entry.call.address args.erase =
      {(invokeResult (denotes body args)).toBehaviour} := by
  rw [invoke_denotes, ← denotes_cast entry.call.body args entry.locals, entry.code]

private theorem append_done (code : Code locals input output) : code.append .done = code := by
  induction code with
  | done => rfl
  | seq op tail ih => simp only [Code.append, ih]

private theorem erase_injective {types : List IntType} {left right : Values types}
    (equal : left.erase = right.erase) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons bits rest ih =>
    cases right with
    | cons other tail =>
      simp only [Values.erase, List.cons.injEq, Val.num.injEq] at equal
      obtain ⟨head, remaining⟩ := equal
      cases head
      rw [ih remaining]

private theorem result_injective {types : List IntType} {left right : Option (Values types)}
    (equal : (invokeResult left).toBehaviour = (invokeResult right).toBehaviour) : left = right := by
  have same := Result.toBehaviour_injective equal
  cases left <;> cases right
  · rfl
  · cases same
  · cases same
  · apply congrArg some
    exact erase_injective (by simpa using congrArg List.reverse (Result.values.inj same))

theorem postEquivalent_iff {parameters declared results : List IntType}
    {first second : Code (parameters ++ declared) [] results}
    (firstEntry : Linked first) (secondEntry : Linked second) (oracle : GrowOracle) :
    PostEquivalent first second ↔ ∀ args, denotes first args = denotes second args := by
  constructor
  · intro equivalent args
    have left : Linked (first.append .done) := (append_done first).symm ▸ firstEntry
    have right : Linked (second.append .done) := (append_done second).symm ▸ secondEntry
    have valid := (left.call.invokeOk_iff args.erase).mpr ⟨args, rfl⟩
    have observed := equivalent .done left right oracle args.erase valid
    rw [linked_observation left args, linked_observation right args, append_done, append_done] at observed
    exact result_injective ((Set.singleton_eq_singleton_iff).mp observed)
  · intro equal observed tail left right profile raw valid
    obtain ⟨args, rfl⟩ := (left.call.invokeOk_iff raw).mp valid
    have denotation : denotes (first.append tail) args = denotes (second.append tail) args := by
      have hole := equal args
      unfold denotes at hole ⊢
      simp only [eval_append, hole]
    rw [linked_observation left args, linked_observation right args, denotation]

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Pure
