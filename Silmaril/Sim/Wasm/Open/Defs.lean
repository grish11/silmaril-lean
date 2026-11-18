module

public import Silmaril.Sim.Wasm.Defs
public import Silmaril.Wasm.Logic.Open.Defs

/-!
# Wasm simulators: open modules and import environments (header)

The adapter from open Wasm modules (`Silmaril.Wasm.Logic.Open`: imports are host stubs answered by
the most general environment `specHost bind Γi` meeting the import contracts `Γi`, the
game-semantic reading of imports) to the bridge interface `Silmaril.Sim.Wasm.ExportSim`. No new
definitions; the results are in `Thms`:

* `ExportSim.methodOK_of_moduleSat`: an open module meeting its export contexts under the most
  general environment of its import contracts gives `MethodOK`;
* `ExportSim.methodOK_of_core`: a core verified once as an open module (accessors as imports
  with contracts `Γi`) plus, per representation, its accessors as a host relation sound and
  live for `Γi`.
-/
