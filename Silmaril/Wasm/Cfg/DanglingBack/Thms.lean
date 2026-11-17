module

public import Silmaril.Wasm.Cfg.DanglingBack.Defs
public import Silmaril.Wasm.Cfg.DanglingExn.Thms
import Silmaril.Proofs.Wasm.Cfg.DanglingBack

@[expose] public section

/-!
# The reverse inclusion for dangling host exceptions: theorems

The backward simulations (`Abstract.HostClosingXP`, `Abstract.HostClosingInfXPBack`) are proved
once for every `Interp.BackInv`; the relaxed instance `backD` (`DanglingTyped.ConfigOkD` against
`DanglingTyped.HostTypedD` hosts, definitions in `Silmaril.Wasm.Cfg.DanglingBack.Defs`) gives
them for runs with dangling host exceptions. Domain: `I.WellFormed s` and the store's functions
in the checker's instruction profile (`Interp.CheckComplete.StoreSupported`, decided by
`storeSupportedB`), hence `CfgInst.InstDom I s` and every export question in `ConfigOkD`
(`DanglingTyped.configOkD_of_supported`). Host: `instHost I` on the Core side, the unrestricted
`instHostU I` on the CFG side (every answer, dangling throws included). Profile: `profile o`.

* `instTripleS_sub_cfgInstTripleU`: every finished behaviour (values, uncaught exception, trap in
  its store, divergence after a log), pending call and productive stream of the instance triple
  `instTripleS I (profile o)` is one of the CFG instance triple `cfgInstTripleU I`;
* `instTripleS_agree_cfgInstTripleU`: with #988's direction (`DanglingExn.cfgInstTripleU_sub`),
  **per question the two triples agree** on all four observations (`AgreeAt`).

The supported profile is a hypothesis through `StoreSupported` (it excludes `ref.test`,
`br_on_cast*`, aggregates and abstract-heap `ref.cast`, whose Core decision on a dangling
reference differs from the witness's). Checker acceptance alone does not suffice for the domain
(`ExampleAlias.dc_not_funcsSupp`).
-/

namespace Silmaril.Wasm.Cfg.DanglingBack

open Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Abstract.InstSession (instTripleS)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {I : ScalarInstance} {o : GrowOracle}

/-- **The reverse inclusion**: every instance behaviour, dangling host throws included, is a CFG
behaviour at the unrestricted host (well-formed store in the checker's profile, deterministic
profile). -/
theorem instTripleS_sub_cfgInstTripleU {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    (instTripleS I (profile o)).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (instTripleS I (profile o)).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (instTripleS I (profile o)).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a :=
  Proofs.DanglingBack.instTripleS_sub_cfgInstTripleU hw hsup a

/-- **Per question, the instance triple is the CFG instance triple at the unrestricted host**:
finished behaviours, pending calls and productive streams (well-formed store in the checker's
profile, deterministic profile). -/
theorem instTripleS_agree_cfgInstTripleU {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I (profile o)) (cfgInstTripleU I) s a :=
  Proofs.DanglingBack.instTripleS_agree_cfgInstTripleU hw hsup a

end Silmaril.Wasm.Cfg.DanglingBack
