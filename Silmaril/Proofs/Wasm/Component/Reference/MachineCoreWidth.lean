module

public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Grows.Defs

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineCoreWidth

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

theorem read_width (run : CoreGrowthSteps profile ready dispatch before trace after)
    (context : LiftLowerContext (core3 grow)) {memory : Nat} {width : AddrType}
    (linked : context.opts.memory = some memory)
    (known : (core3 grow).memAddrType? before.store.core memory = some width)
    (next : AddrType → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (ptrType context >>= next), segments⟩ :: rest) :
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog (next width), segments⟩ :: rest } := by
  have reached : (core3 grow).memAddrType? after.store.core memory = some width := run.grows.memAddrType known
  have readsWidth : ptrTypeIn after.store context = width := by
    simp [ptrTypeIn, CanonOpts.ptrType, linked, reached]
  have read : after.ctl = ⟨thread, .prog (.op .get (fun current => next (ptrTypeIn current context))),
      segments⟩ :: rest := focused
  have step := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) read
  rw [readsWidth] at step
  exact .cons (by simp [CoreUpdateGrows, read]) step (.refl _)

end Silmaril.Proofs.Wasm.Component.Reference.MachineCoreWidth
