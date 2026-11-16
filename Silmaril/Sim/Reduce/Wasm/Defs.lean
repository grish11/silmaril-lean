module

public import Silmaril.Sim.Reduce.Core.Defs
public import Silmaril.Sim.Wasm.Defs
public import Silmaril.Wasm.Logic.Core.Defs

/-!
# Reducing ISA problems to Wasm problems: the call-level Wasm problem

The Wasm problem of the reduction (`Silmaril.Sim.Reduce.WasmTotal`) in the call-level form of the
Wasm specification library (`Silmaril.Wasm.Logic.Core.FuncSpec`, as `Silmaril.WasmSpec.*.CallSpec`),
for a certified Wasm simulator with one command (`Silmaril.Sim.Wasm.ExportSim Unit L V H` with a
certificate `Ct : K.Cert (Machine.ofStep step view)`, run-level simulator
`SoundSim.ofExportCert Ct`):

* `runSpec K Init Pre Post`: from every store that is a freshly loaded simulator (`Init`)
  meeting `Pre`, one call of the command's export (on `K.args ()`) can return accepted results
  (`K.ok ()`) in a store meeting `Post`.

`Silmaril.Sim.Reduce.Wasm.Thms` proves `runSpec ⇒ WasmTotal` (`wasmTotal_of_runSpec`) and chains
it with the x86 contract reduction (`specRunReduction`).
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Wasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {L V H : Type}

/-- **The Wasm problem, call-level form** (`FuncSpec` of the export of the single command). -/
def runSpec (K : Silmaril.Sim.Wasm.ExportSim Unit L V H) (Init : Store H → Prop)
    (Pre : Store H → Prop) (Post : Store H → Store H → Prop) : Prop :=
  FuncSpec K.P K.host (K.addr ()) (fun s args => args = K.args () ∧ Init s ∧ Pre s)
    (fun s _ s' res => K.ok () res ∧ Post s s')

end Silmaril.Sim.Reduce.Wasm
