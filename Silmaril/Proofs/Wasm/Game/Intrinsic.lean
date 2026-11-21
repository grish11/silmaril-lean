module

public import Silmaril.Wasm.Game.Intrinsic.Defs
public import Silmaril.Wasm.Game.DivAdequacy.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.Intrinsic

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.Intrinsic
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Validation (DefType Ty)

variable {context : Validation.Context} {type : DefType} {func : Validation.Intrinsic.Function context type}
  {I : ScalarInstance} {store : Store Nat} {sig : FnType} {P : Profile}

theorem question_values (entry : Entry func I store sig) (args : Typed sig.params) :
    (entry.question args).2.val = args.val := by
  obtain ⟨slot, signature, scalar, address, resolved, implementation, code⟩ := entry
  subst sig
  rfl

theorem invokeOk (entry : Entry func I store sig) (args : Typed sig.params) :
    InvokeOk store entry.address args.val := by
  refine ⟨_, Ty.ofList (sig.params.map ScalarType.toC), Ty.ofList (sig.results.map ScalarType.toC),
    entry.code, FnType.expand_of_ofDefType? entry.scalar, ?_⟩
  simpa [Ty.toList_ofList] using
    (List.forall₂_map_right_iff.mpr (args.property.flip.imp (fun value ty valid =>
      (ScalarType.hasVal_iff_valOk store ty value).mp valid)) :
        List.Forall₂ (ValOk store) args.val (sig.params.map ScalarType.toC))

theorem enter (entry : Entry func I store sig) (host : HostSemantics Nat) (args : Typed sig.params) :
    Step P host (invoke store entry.address args.val)
      ⟨store, {}, [.frame sig.results.length (Frame.forCall entry.implementation args.val func.erase.locals)
        [.label sig.results.length [] (expression func.erase.body)]]⟩ := by
  have expanded := FnType.expand_of_ofDefType? entry.scalar
  change Validation.Expand type (.func (Ty.ofList (sig.params.map ScalarType.toC))
    (Ty.ofList (sig.results.map ScalarType.toC))) at expanded
  have arity : args.val.length = (Ty.ofList (sig.params.map ScalarType.toC)).length := by
    simpa [Ty.length_ofList] using args.property.length_eq.symm
  unfold invoke
  rw [entry.code]
  simpa [Ty.length_ofList] using
    (Step.callRefFunc (P := P) (host := host) (f := {}) (c := .callRefType type)
      trivial entry.code expanded arity rfl)

theorem entry_adequacy (entry : Entry func I store sig) (hw : I.WellFormed store)
    (env : Env I.E) (throws : ThrowsBelow env store.exns.length) (args : Typed sig.params) :
    entry.denote P env args = behaviours P (hostOf I.imports env) store entry.address args.val := by
  unfold Entry.denote
  rw [← ScalarInstance.adequacy_div_comp hw env throws, question_values, show
    I.addr (entry.question args).1 = entry.address from entry.resolved]

theorem first_import_iff (entry : Entry func I store sig) (args : Typed sig.params) (op : I.E.Op) :
    [.inr (.ask (entry.question args)), .inl (.ask op)] ∈ I.strategy P store ↔
      ∃ config, Steps P (Det.noHost : HostSemantics Nat) (invoke store entry.address args.val) config ∧
        ∃ eval addr host values, decompose? config.store config.code = some (eval, addr, host, values) ∧
          I.importOp? host values = some op := by
  rw [ScalarInstance.ask_call_iff, question_values, show
    I.addr (entry.question args).1 = entry.address from entry.resolved]

theorem round_iff_activation (entry : Entry func I store sig) (args : Typed sig.params)
    {target : Store Nat} (moves : List (Move I.E I.F)) (single : ∀ op, .inr (.ask op) ∉ moves) :
    entry.round P args moves target ↔ I.Activation P store (.inr (.ask (entry.question args)) :: moves) target := by
  constructor
  · intro round
    exact .cons (.call store _) round.1
  · intro activation
    cases activation with
    | cons call path => cases call; exact ⟨path, single⟩

end Silmaril.Proofs.Wasm.Game.Intrinsic
