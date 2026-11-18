module

public import Silmaril.Wasm.Component.Reference.LinkedGComp.Thms
public import Silmaril.Games.Abstract.SessionLink.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet.Main

/-!
# Full determinism of simple, linked and chained exporters: theorems

**Scope.** The deterministic profiles `profile o`. A simple exporter `Simple.expSpec c I`, a
linked component `g.toExp Ii` (`LinkedG`, an abstract exporter `g.exp`, a simple importer at a
core instance `Ii`) and chains `chainExp e bs Is` (so `LinkedN.spec n Ib Is`). `ExpSpec.DivExcl`
and `ExpSpec.afunDet_sessTripleS_iff` are from `LinkedGComp`.

**Hypotheses.** A simple exporter: none (as for `Simple.expSpec_det`). A linked component: the
exporter is deterministic (`ExpSpec.Det`, as for `LinkedG.toExp_det`), its divergences exclude
steps (`ExpSpec.DivExcl`) and the wiring is well typed (`LinkedG.WireTy`; for chains
`ChainWire`, implied by `ChainOk`). `WireTy` is used for one fact: a served call that diverges by
`LinkedG.DivA` is a typed question of the exporter, so that its `DivExcl` applies. Not needed:
`Adeq`, `AdeqD`, `Good`, instances of the core modules.

**Proved.**

1. **Simple exporters** (`Simple.expSpec_divExcl`): `(Simple.expSpec c I).DivExcl (profile o)`: a
   returned or trapped call reaches a host-free normal form (`ResultAt`), which excludes a
   host-free infinite run of the same activation (`LinkedGComp`'s `not_inf_of_nf`). Hence
   `Simple.afunDet_sessTripleS`: `AFun.Det ((Simple.expSpec c I).sessTripleS (profile o)).1`.
2. **Linked components** (`LinkedG.toExp_divExcl`): `(g.toExp Ii).DivExcl (profile o)` from
   `g.exp.Det`, `g.exp.DivExcl` and `g.WireTy`. A diverging round and a finished round of the same
   question from the same state agree on the diverging round's prefix (the importer's Proponent
   moves are unique, the exporter answers uniquely); then each source of divergence excludes the
   finished round: `DivB` (the importer runs host-free forever) excludes every move, `DivA` makes
   the finished round step the exporter on the question that diverges (excluded by `DivExcl` of
   the exporter), chatter would agree with the finished round's import calls forever while the
   finished round answers. Hence `LinkedG.toExp_afunDet_sessTripleS`.
3. **Chains** (`chainExp_divExcl`, `chainExp_afunDet_sessTripleS`; `LinkedN.spec_divExcl`,
   `LinkedN.afunDet_sessTripleS` for a simple base): by induction, with `chainExp_det`.
4. **Composition by `comp_threadS_of_det`** (`ExpSpec.comp_impSession_eq_threadS_linkS`,
   `LinkedN.comp_impSession_eq_threadS_linkS`): for an exporter whose triple is `AFun.Det`, its
   session composed with one more importer's session is the session of the linked triples:

   `(e.session (profile o)).comp (b.impSession (profile o) w I) = threadS (linkS (e.sessTripleS (profile o)) (b.impTripleS (profile o) w I)) (e.init, I.store)`,

   for every simple exporter and every chain on one (no wiring hypothesis on the new importer).
   `LinkedGComp`'s compositions use `RetDet` only and are unchanged.

**Not claimed.**

* `DivExcl` (hence `AFun.Det`) at nondeterministic profiles, or for a linked component whose
  exporter is not `DivExcl` (`cexExp` is `ExpSpec.Det` but not `DivExcl`) or whose wiring is not
  well typed.
* `AFun.Det` of linked triples (`linkS`) in general; host imports (`HLinked2`, `hostLinkS`).

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet.Main`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS comp_threadS_of_det)
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Game (ScalarInstance)

/-! ## Simple exporters -/

/-- **A simple exporter: divergence excludes a step** at `profile o` (proved). -/
theorem Simple.expSpec_divExcl (o : GrowOracle) (c : Simple) (I : ScalarInstance) :
    (Simple.expSpec c I).DivExcl (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet.simple_divExcl o c I

/-- **The triple of a simple exporter is deterministic given answers** at `profile o`
(proved). -/
theorem Simple.afunDet_sessTripleS (o : GrowOracle) (c : Simple) (I : ScalarInstance) :
    AFun.Det ((Simple.expSpec c I).sessTripleS (profile o)).1 :=
  ExpSpec.afunDet_sessTripleS (Simple.expSpec_det o c I) (Simple.expSpec_divExcl o c I)

/-! ## Linked components -/

namespace LinkedG

variable {o : GrowOracle} {g : LinkedG} {Ii : ScalarInstance}

/-- **A linked component: divergence excludes a step** at `profile o` (proved), for a
deterministic exporter whose divergences exclude steps, with a well-typed wiring. -/
theorem toExp_divExcl (hd : g.exp.Det (profile o)) (hx : g.exp.DivExcl (profile o))
    (hw : g.WireTy) : (g.toExp Ii).DivExcl (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet.toExp_divExcl hd hx hw

/-- **The triple of a linked component is deterministic given answers** at `profile o`
(proved). -/
theorem toExp_afunDet_sessTripleS (hd : g.exp.Det (profile o)) (hx : g.exp.DivExcl (profile o))
    (hw : g.WireTy) : AFun.Det ((g.toExp Ii).sessTripleS (profile o)).1 :=
  ExpSpec.afunDet_sessTripleS (toExp_det hd) (toExp_divExcl hd hx hw)

end LinkedG

/-! ## Chains -/

/-- **Chains: divergence excludes a step** at `profile o` (proved). -/
theorem chainExp_divExcl (o : GrowOracle) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (hd : e.Det (profile o)) (hx : e.DivExcl (profile o))
    (h : ChainWire e bs Is) : (chainExp e bs Is).DivExcl (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet.chain_divExcl o e bs Is hd hx h

/-- **The triple of a chain is deterministic given answers** at `profile o` (proved). -/
theorem chainExp_afunDet_sessTripleS (o : GrowOracle) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (hd : e.Det (profile o))
    (hx : e.DivExcl (profile o)) (h : ChainWire e bs Is) :
    AFun.Det ((chainExp e bs Is).sessTripleS (profile o)).1 :=
  ExpSpec.afunDet_sessTripleS (chainExp_det o hd) (chainExp_divExcl o hd hx h)

/-- **An exporter with a deterministic triple composed with one more importer is the link of
their triples** at `profile o` (proved, `comp_threadS_of_det`). -/
theorem ExpSpec.comp_impSession_eq_threadS_linkS {o : GrowOracle} {e : ExpSpec}
    (he : AFun.Det (e.sessTripleS (profile o)).1) (b : SimpleI) (w : List Nat)
    (I : ScalarInstance) :
    (e.session (profile o)).comp (b.impSession (profile o) w I) =
      threadS (linkS (e.sessTripleS (profile o)) (b.impTripleS (profile o) w I))
        (e.init, I.store) :=
  comp_threadS_of_det ExpSpec.noPlainTrap_sessTripleS he (SimpleI.det_impTripleS o) _ _

namespace LinkedN

variable {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}

/-- **A chain of simple modules: divergence excludes a step** at `profile o` (proved). -/
theorem spec_divExcl (o : GrowOracle) (h : ChainWire (Simple.expSpec n.base Ib) n.links Is) :
    (n.spec Ib Is).DivExcl (profile o) :=
  chainExp_divExcl o (Simple.expSpec_det o _ _) (Simple.expSpec_divExcl o _ _) h

/-- **The triple of a chain of simple modules is deterministic given answers** at `profile o`
(proved). -/
theorem afunDet_sessTripleS (o : GrowOracle)
    (h : ChainWire (Simple.expSpec n.base Ib) n.links Is) :
    AFun.Det ((n.spec Ib Is).sessTripleS (profile o)).1 :=
  chainExp_afunDet_sessTripleS o (Simple.expSpec_det o _ _) (Simple.expSpec_divExcl o _ _) h

/-- **A chain of simple modules composed with one more importer is the link of their triples**
at `profile o` (proved). -/
theorem comp_impSession_eq_threadS_linkS (o : GrowOracle)
    (h : ChainWire (Simple.expSpec n.base Ib) n.links Is) (b : SimpleI) (w : List Nat)
    (I : ScalarInstance) :
    ((n.spec Ib Is).session (profile o)).comp (b.impSession (profile o) w I) =
      threadS (linkS ((n.spec Ib Is).sessTripleS (profile o)) (b.impTripleS (profile o) w I))
        ((n.spec Ib Is).init, I.store) :=
  ExpSpec.comp_impSession_eq_threadS_linkS (afunDet_sessTripleS o h) b w I

end LinkedN

end Silmaril.Wasm.Component.Reference
