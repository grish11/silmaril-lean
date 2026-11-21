module

public import Silmaril.Wasm.Game.Intrinsic.Requests.Defs
public import Silmaril.Wasm.Game.Intrinsic.Thms
import Silmaril.Proofs.Wasm.Game.Intrinsic.Requests

public section

namespace Silmaril.Wasm.Game.Intrinsic.Requests

open Silmaril.Games Execution.Core Numerics SingleThreaded
open Validation (Context DefType)

variable {source : Module} {I : ScalarInstance} {op : I.F.Op} {n : Nat}
  {tree : Tree source I (I.exports.get op.1)} {store target : Store Nat} {thread : Thread}
  {moves : List (Move I.E I.F)}

/-- A completed tree trace has a game path to an actual post-call store,
for any profile in which the implementation evidence holds. -/
theorem Realizes.path_of_completes {P : Profile} (implementation : Realizes P n op tree store thread)
    (complete : Completes n op tree moves) :
    ∃ target, I.Path P (.running op store thread) moves (.idle target) ∧
      ∀ next, .inr (.ask next) ∉ moves :=
  Proofs.Wasm.Game.Intrinsic.Requests.path_of_completes implementation complete

/-- In a deterministic profile there are no other completed single-call game
paths with admissible replies. This does not compare divergent or partial plays. -/
theorem Realizes.completes_of_path {oracle : GrowOracle}
    (implementation : Realizes (profile oracle) n op tree store thread)
    (path : I.Path (profile oracle) (.running op store thread) moves (.idle target))
    (single : ∀ next, .inr (.ask next) ∉ moves) (legal : I.PlayThrowsBelow n moves) :
    Completes n op tree moves :=
  Proofs.Wasm.Game.Intrinsic.Requests.completes_of_path implementation path single legal

/-- A separate store-preserving host interpretation is sound against Core.
If the handler does not answer, this witnesses an actual infinite Core trace. -/
theorem Realizes.handled_mem_core {P : Profile} (implementation : Realizes P n op tree store thread)
    (env : Env I.E) (legal : ThrowsBelow env n) :
    tree.handledBehaviour env ∈ behavioursOf P (hostOf I.imports env) (thread.config store) :=
  Proofs.Wasm.Game.Intrinsic.Requests.handled_mem_core implementation env legal

/-- Exact agreement on completed traces of an intrinsic entry. The resulting
store is supplied by the stock game, not reconstructed from the visible trace. -/
theorem completes_iff_entry_round {context : Context} {type : DefType}
    {func : Validation.Intrinsic.Function context type} {sig : FnType} {oracle : GrowOracle}
    (entry : Entry func I store sig) (args : Typed sig.params)
    {tree : Tree source I (I.exports.get (entry.question args).1)}
    (implementation : Realizes (profile oracle) n (entry.question args) tree store
      (I.initThread (entry.question args))) (legal : I.PlayThrowsBelow n moves) :
    Completes n (entry.question args) tree moves ↔ ∃ target, entry.round (profile oracle) args moves target :=
  ⟨implementation.path_of_completes, fun ⟨_, path, single⟩ =>
    implementation.completes_of_path path single legal⟩

/-- The handled observation belongs to the stock divergence-observing game of
the erased function. This is soundness for the chosen handler, not open
equivalence or completeness for an arbitrary nondeterministic profile. -/
theorem handled_mem_entry {context : Context} {type : DefType}
    {func : Validation.Intrinsic.Function context type} {sig : FnType} {P : Profile}
    (entry : Entry func I store sig) (args : Typed sig.params)
    {tree : Tree source I (I.exports.get (entry.question args).1)}
    (implementation : Realizes P n (entry.question args) tree store (I.initThread (entry.question args)))
    (hw : I.WellFormed store) (env : Env I.E) (legal : ThrowsBelow env n)
    (throws : ThrowsBelow env store.exns.length) :
    tree.handledBehaviour env ∈ entry.denote P env args := by
  rw [entry.adequacy hw env throws args]
  have resolve : I.addr (entry.question args).1 = entry.address := entry.resolved
  simpa only [ScalarInstance.initThread, Thread.config, resolve, entry.question_values, behaviours] using
    implementation.handled_mem_core env legal

end Silmaril.Wasm.Game.Intrinsic.Requests
