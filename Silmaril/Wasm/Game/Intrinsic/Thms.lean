module

public import Silmaril.Wasm.Game.Intrinsic.Defs
public import Silmaril.Wasm.Game.DivAdequacy.Thms
import Silmaril.Proofs.Wasm.Game.Intrinsic

public section

namespace Silmaril.Wasm.Game.Intrinsic

open Silmaril.Games Execution.Core Numerics SingleThreaded
open Validation (CModuleType Context DefType)

variable {interface : CModuleType} {program : Validation.Intrinsic.Module interface}
  {context : Context} {type : DefType} {func : Validation.Intrinsic.Function context type}
  {I : ScalarInstance} {store target : Store Nat} {sig : FnType} {P : Profile}

theorem Entry.question_values (entry : Entry func I store sig) (args : Typed sig.params) :
    (entry.question args).2.val = args.val :=
  Proofs.Wasm.Game.Intrinsic.question_values entry args

theorem Entry.invokeOk (entry : Entry func I store sig) (args : Typed sig.params) :
    InvokeOk store entry.address args.val :=
  Proofs.Wasm.Game.Intrinsic.invokeOk entry args

/-- The game entry installs the erased intrinsic code in the actual Core call
frame. In particular, the link is not justified just by equal signatures. -/
theorem Entry.enter (entry : Entry func I store sig) (host : HostSemantics Nat) (args : Typed sig.params) :
    Step P host (invoke store entry.address args.val)
      ⟨store, {}, [.frame sig.results.length (Frame.forCall entry.implementation args.val func.erase.locals)
        [.label sig.results.length [] (expression func.erase.body)]]⟩ :=
  Proofs.Wasm.Game.Intrinsic.enter entry host args

/-- `Entry.denote` is adequate for the actual invocation of the erased intrinsic
body at the registered address. This is equality of observations in both
directions, not equality of open strategies. -/
theorem Entry.adequacy (entry : Entry func I store sig) (hw : I.WellFormed store)
    (env : Env I.E) (throws : ThrowsBelow env store.exns.length) (args : Typed sig.params) :
    entry.denote P env args = behaviours P (hostOf I.imports env) store entry.address args.val :=
  Proofs.Wasm.Game.Intrinsic.entry_adequacy entry hw env throws args

/-- Reading the first import move does not close the strategy or hide its import.
Its arguments come from the actual Core callout redex. -/
theorem Entry.first_import_iff (entry : Entry func I store sig) (args : Typed sig.params) (op : I.E.Op) :
    [.inr (.ask (entry.question args)), .inl (.ask op)] ∈ I.strategy P store ↔
      ∃ config, Steps P (Det.noHost : HostSemantics Nat) (invoke store entry.address args.val) config ∧
        ∃ eval addr host values, decompose? config.store config.code = some (eval, addr, host, values) ∧
          I.importOp? host values = some op :=
  Proofs.Wasm.Game.Intrinsic.first_import_iff entry args op

/-- A finished application accounts for an activation of the original game,
with its actual ending store. -/
theorem Entry.prepend_question (entry : Entry func I store sig) (args : Typed sig.params)
    {moves : List (Move I.E I.F)} (run : entry.round P args moves target) :
    I.Activation P store (.inr (.ask (entry.question args)) :: moves) target :=
  .cons (.call store _) run.1

theorem Entry.round_iff_activation (entry : Entry func I store sig) (args : Typed sig.params)
    (moves : List (Move I.E I.F)) (single : ∀ op, .inr (.ask op) ∉ moves) :
    entry.round P args moves target ↔
      I.Activation P store (.inr (.ask (entry.question args)) :: moves) target :=
  Proofs.Wasm.Game.Intrinsic.round_iff_activation entry args moves single

/-- Any valid play at the post-round store can follow the open application. -/
theorem Entry.continue (entry : Entry func I store sig) (args : Typed sig.params)
    {moves next : List (Move I.E I.F)} (run : entry.round P args moves target)
    (resume : next ∈ I.strategy P target) :
    (.inr (.ask (entry.question args)) :: moves) ++ next ∈ I.strategy P store :=
  ScalarInstance.append_mem_of (entry.prepend_question args run) resume

/-- Adequacy of the registered module strategy at each actual exported question.
`ready` provides initial store well-formedness, not just source validation. -/
theorem Registered.adequacy (registered : Registered program) (env : Env registered.instance_.E)
    (throws : ThrowsBelow env registered.instance_.store.exns.length) (op : registered.instance_.F.Op) :
    dcompositeObs (env.dstrategy.comp (registered.denote P)) op =
      behaviours P (hostOf registered.instance_.imports env) registered.instance_.store
        (registered.instance_.addr op.1) op.2.val :=
  (ScalarInstance.adequacy_div_comp registered.ready.ok env throws op).symm

theorem Registered.entry_denote (registered : Registered program)
    (entry : Entry func registered.instance_ registered.instance_.store sig)
    (env : Env registered.instance_.E) (args : Typed sig.params) :
    entry.denote P env args = dcompositeObs (env.dstrategy.comp (registered.denote P)) (entry.question args) :=
  rfl

/-- Different intrinsic witnesses of the same closed source syntax and interface
cannot change the registered scalar instance. -/
theorem Registered.instance_eq_of_erase_eq {other : Validation.Intrinsic.Module interface}
    (left : Registered program) (right : Registered other) (erase : program.erase = other.erase) :
    left.instance_ = right.instance_ :=
  left.ready.unique (erase.symm ▸ right.ready)

end Silmaril.Wasm.Game.Intrinsic
