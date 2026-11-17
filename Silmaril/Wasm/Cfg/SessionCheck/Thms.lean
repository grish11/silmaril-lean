module

public import Silmaril.Wasm.Cfg.SessionCheck.Defs
public import Silmaril.Wasm.Cfg.Session.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.SessionCheck

@[expose] public section

/-!
# Checking the CFG session's domain, and components on it

* **`hfOk_of_check`** (validation bridge): a validated module without imports
  (`Validation.validate?`), instantiated into the empty store by `prepare?` with no start
  function, gives a store at which every scalar instance passing the executable check `hfCheck`
  is in the CFG session's domain `HFOk`. Store typing comes from the module's validation and
  instantiation (`prepare?_sound`, `Instantiate.ok`). The rest comes from existing checkers:
  `storeChkEB tExt` for the arity check, and `expand?` for the export types.
* **`denUD_congrIn`**: a component's divergence-observing denotation depends only on the core
  semantics of the core instances it uses (`CompIn`).
* **`denUD_core3SemD_eq_cfgSession`, `denD_core3SemD_eq_cfgSession`** (component replacement on
  an explicit domain): when **every** core instance of the component `c` is in the domain
  (`CompIn (fun m => HFOk m.inst m.inst.store) c`), its denotation under Core 3.0
  (`core3SemD (profile o)`) is its denotation with each instance interpreted by its CFG session.
  There is no fallback here; outside the domain nothing is claimed.

The CFG session is oracle-backed (`CX closedCallX`) and host-free, as stated in
`Silmaril.Wasm.Cfg.Session`.
-/

namespace Silmaril.Wasm.Cfg.SessionCheck

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Cfg.Session
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.Abstract.InstSession (threadSemSD core3SemD)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **The executable check gives the CFG session's domain**, for the store of a validated module
without imports instantiated into the empty store. -/
theorem hfOk_of_check {I : ScalarInstance} {mod : Module} {mt : Validation.CModuleType}
    {c : Config Nat} (hv : Validation.validate? mod = some mt) (himp : mt.imports = [])
    (hp : prepare? evalConst? ({} : Store Nat) mod [] = some (c, none))
    (hs : I.store = c.store) (hb : hfCheck I = true) : HFOk I I.store :=
  Proofs.SessionCheck.hfOk_of_check hv himp hp hs hb

/-- **Denotations depend only on the core instances used.** -/
theorem denUD_congrIn {M : Type} [CoreModule M] {p : M → Prop} {C C' : DCoreSem M}
    (h : ∀ m, p m → C.sem m = C'.sem m) (c : Comp M) (hc : CompIn p c) :
    c.denUD C = c.denUD C' :=
  Proofs.SessionCheck.denUD_congrIn h c hc

/-- **A component whose core instances are all in the domain**: its divergence-observing
denotation under Core 3.0 is the one with every instance interpreted by its CFG session. -/
theorem denUD_core3SemD_eq_cfgSession {o : GrowOracle} (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => HFOk m.inst m.inst.store) c) :
    c.denUD (core3SemD (profile o)) =
      c.denUD (threadSemSD fun m => cfgSession m.inst o m.inst.store) :=
  denUD_congrIn (fun m hm => congrArg (Abstract.InstSession.semOfSD m)
    (cfgSession_eq_instSession hm).symm) c hc

/-- The same at the component's interface signatures. -/
theorem denD_core3SemD_eq_cfgSession {o : GrowOracle} (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => HFOk m.inst m.inst.store) c) :
    c.denD (core3SemD (profile o)) =
      c.denD (threadSemSD fun m => cfgSession m.inst o m.inst.store) :=
  congrArg (Component.DStrategy.atSizes _ _) (denUD_core3SemD_eq_cfgSession c hc)

end Silmaril.Wasm.Cfg.SessionCheck
