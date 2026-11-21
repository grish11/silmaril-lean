module

public import Silmaril.Wasm.Execution.Core.MemoryProfile.Defs
public import Silmaril.Semantics.Operational.Policy.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Execution.Core.MemoryProfile

public section

namespace Silmaril.Wasm.Execution.Core.MemoryProfile

open Validation SingleThreaded SingleThreaded.Det Semantics.Operational

variable {oracle : GrowOracle} {input output : Nat}

/-- Exact active Core step, in any flat surrounding value prefix and suffix.
An OOB access installs a pending trap, not a policy UB. -/
theorem load_step_iff (bytes : ByteArray) (address : BitVec 32) (saved : List Val) (rest : List Admin)
    (target : Config Unit) :
    Step (profile oracle) noHost (config bytes (vals saved ++ ((word address).toAdmin :: load :: rest))) target ↔
      target = config bytes (vals saved ++
        (match Memory.load bytes address.toNat 4 with
        | none => [.trap]
        | some bits => [(word bits).toAdmin]) ++ rest) :=
  Proofs.Wasm.Execution.Core.MemoryProfile.load_step_iff bytes address saved rest target

/-- Exact active Core store step, including the final bytes on success and
unchanged bytes on an OOB trap. -/
theorem store_step_iff (bytes : ByteArray) (address bits : BitVec 32) (saved : List Val)
    (rest : List Admin) (target : Config Unit) :
    Step (profile oracle) noHost (config bytes (vals saved ++
      ((word address).toAdmin :: (word bits).toAdmin :: store :: rest))) target ↔
      target = match Memory.store bytes address.toNat (count := 4) bits with
        | none => config bytes (vals saved ++ [.trap] ++ rest)
        | some after => config after (vals saved ++ rest) :=
  Proofs.Wasm.Execution.Core.MemoryProfile.store_step_iff bytes address bits saved rest target

theorem config_typed {bytes : ByteArray} {code : List Admin} {types : List CValType}
    (page : bytes.size = Memory.pageSize)
    (instructions : AdminsOk (world bytes) context code (.plain [] types)) :
    ConfigOk (config bytes code) types :=
  Proofs.Wasm.Execution.Core.MemoryProfile.config_typed page instructions

/-- The tape's typing implies Core `ConfigOk` for a one-page memory. This
precondition says nothing about whether an individual address is in bounds. -/
theorem Code.start_typed (code : Code input output) (stack : Stack input) {bytes : ByteArray}
    (page : bytes.size = Memory.pageSize) : ConfigOk (code.start stack bytes) (resultTypes output) :=
  Proofs.Wasm.Execution.Core.MemoryProfile.start_typed code stack page

/-- All Core prefixes stay in the policy, even alternate trap bubbling paths. -/
theorem Code.raw_prefix_admitted (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) {target : Config Unit}
    (path : Steps (profile oracle) noHost (code.start stack bytes) target) : Admitted output target :=
  Proofs.Wasm.Execution.Core.MemoryProfile.raw_prefix_admitted code stack bytes typed path

theorem Code.safe (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) :
    (semantics oracle output).SafeAt (code.start stack bytes) :=
  Proofs.Wasm.Execution.Core.MemoryProfile.safe code stack bytes typed

/-- From the typed entry the guarded relation preserves and reflects Core
reachability, including all intermediate states. -/
theorem Code.reach_iff (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) (target : Config Unit) :
    (semantics oracle output).toOpSem.Reach (code.start stack bytes) target ↔
      Steps (profile oracle) noHost (code.start stack bytes) target :=
  Proofs.Wasm.Execution.Core.MemoryProfile.reach_iff code stack bytes typed target

/-- Exact normal-form readback, including the byte store and the final code.
This is not equality of evaluator and Core administrative traces. -/
theorem Code.normal_iff (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (target : Config Unit) :
    (Steps (profile oracle) noHost (code.start stack bytes) target ∧
      ∀ next, ¬ Step (profile oracle) noHost target next) ↔
      target = (code.eval stack bytes).erase :=
  Proofs.Wasm.Execution.Core.MemoryProfile.normal_iff code stack bytes target

theorem Code.may_iff (code : Code input output) (stack : Stack input) (bytes : ByteArray)
    (typed : ConfigOk (code.start stack bytes) (resultTypes output)) (outcome : Outcome Intrinsic.Completion) :
    (semantics oracle output).toOpSem.May (code.start stack bytes) outcome ↔
      outcome = Intrinsic.observeResult (code.eval stack bytes).result :=
  Proofs.Wasm.Execution.Core.MemoryProfile.may_iff code stack bytes typed outcome

theorem Code.not_diverges (code : Code input output) (stack : Stack input) (bytes : ByteArray) :
    ¬ Diverges (profile oracle) noHost (code.start stack bytes) :=
  Proofs.Wasm.Execution.Core.MemoryProfile.not_diverges code stack bytes

end Silmaril.Wasm.Execution.Core.MemoryProfile
