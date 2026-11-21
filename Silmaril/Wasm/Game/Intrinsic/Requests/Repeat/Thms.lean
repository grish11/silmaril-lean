module

public import Silmaril.Wasm.Game.Intrinsic.Requests.Repeat.Defs
public import Silmaril.Wasm.Game.Intrinsic.Thms
import Silmaril.Proofs.Wasm.Game.Intrinsic.Requests.Repeat

public section

namespace Silmaril.Wasm.Game.Intrinsic.Requests

open Silmaril.Games Execution.Core Numerics SingleThreaded

variable {source : Module} {instance_ : ScalarInstance} {request : NamedImport source instance_}
  {args : Typed request.signature.params} {reply : Typed request.signature.results}
  {profile_ : Profile} {store : Store Nat} {waiting : Thread}

/-- The environment really returns the selected values at the callout. No
diverged-host step or store replacement is used. -/
theorem Repeat.reply_step (loop : Repeat profile_ request args reply store waiting)
    (env : Env instance_.E) (answers : env.Answers (request.question args) (.values reply)) :
    Step profile_ (hostOf instance_.imports env) (waiting.config store)
      ((resumeResult store waiting (.values reply.val)).config store) :=
  Proofs.Wasm.Game.Intrinsic.Requests.Repeat.reply_step loop env answers

/-- One coherent infinite stock Core trace. At every period boundary the next
step is the resumption from the same answered callout. All other steps are
host-free; a finite prefix family alone is not used to infer productivity. -/
theorem Repeat.periodic_core (loop : Repeat profile_ request args reply store waiting)
    (env : Env instance_.E) (answers : env.Answers (request.question args) (.values reply)) :
    ∃ period > 0, ∃ trace : Nat → Config Nat, trace 0 = waiting.config store ∧
      (∀ time, Step profile_ (hostOf instance_.imports env) (trace time) (trace (time + 1))) ∧
      (∀ time, time % period ≠ 0 → Step profile_ Det.noHost (trace time) (trace (time + 1))) ∧
      ∀ cycle, trace (cycle * period) = waiting.config store ∧
        trace (cycle * period + 1) = (resumeResult store waiting (.values reply.val)).config store :=
  Proofs.Wasm.Game.Intrinsic.Requests.Repeat.periodic_core loop env answers

/-- The same answered request stream has all its complete-pair prefixes in
the open stock game. Each ends with the next import already pending. -/
theorem Repeat.game_prefix {op : instance_.F.Op} (loop : Repeat profile_ request args reply store waiting)
    (enter : Reach profile_ (store, instance_.initThread op) (store, waiting)) (count : Nat) :
    .inr (.ask op) :: .inl (.ask (request.question args)) :: Repeat.moves request args reply count ∈
      instance_.strategy profile_ store :=
  Proofs.Wasm.Game.Intrinsic.Requests.Repeat.game_prefix loop enter count

end Silmaril.Wasm.Game.Intrinsic.Requests
