module

public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Proofs.Wasm.Component.Reference.MachineCoreWidth

public section

namespace Silmaril.Wasm.Component.Machine

open Silmaril.Wasm Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

/-- At any reached pointer-width read, the actual scheduler takes one silent
step and feeds the originally checked width to the continuation. The callback
prefix may write bytes, grow the memory, or execute certified reentrant calls. -/
theorem CoreGrowthSteps.read_width (run : CoreGrowthSteps profile ready dispatch before trace after)
    (context : LiftLowerContext (core3 grow)) {memory : Nat} {width : AddrType}
    (linked : context.opts.memory = some memory)
    (known : (core3 grow).memAddrType? before.store.core memory = some width)
    (next : AddrType → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (ptrType context >>= next), segments⟩ :: rest) :
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog (next width), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreWidth.read_width run context linked known next focused

end Silmaril.Wasm.Component.Machine
