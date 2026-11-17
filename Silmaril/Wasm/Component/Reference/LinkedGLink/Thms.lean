module

public import Silmaril.Wasm.Component.Reference.LinkedGLink.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGSession.Thms
public import Silmaril.Games.Abstract.SessionLink.Defs
public import Silmaril.Games.Abstract.SessionCat.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Thread
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Det

/-!
# The importer of a linked component as a session client: theorems

**Scope.** A linked component `g : LinkedG` (an abstract exporter `g.exp`, a simple importer
`g.imp` at a core instance `Ii`, the wiring `g.wire`), at every profile `P`, nondeterministic
profiles included. The importer's own session triple `SimpleI.impTripleS P g.imp g.wire Ii`
(`Defs`) is related to the generic session-linking API of `Games.Abstract`: `SessionLink.linkS`,
`SessionLinkAssoc.mapStore`, `SessionLinkAssoc.linkS_assoc`, `SessionTrap.TrapAbortsRound`.

**Hypotheses.** The equality needs only `LinkedG.WireTy` (one wired export per import, of the
import's type); the session form needs in addition that `Ii` is an instance of the importer's
core module (`LinkedG.compSession` picks that instance). Not needed: `g.exp.Adeq P`, `g.imp.Good`,
determinism.

**Proved.**

1. **Traps of the importer** (`SimpleI.impTripleS_trapAbortsRound`):
   `TrapAbortsRound IsTrapS (impTripleS P b wire Ii)`. A wired call answered `.inr ()` is the last
   call of its round, which then returns the trap `.inr ()` (keeping the importer's store); no
   pending call follows it and no productive stream receives it. Proved from
   `NodeTrap.instTripleS_trapAbortsRound` (a Core 3.0 instance traps the caller of a trapping
   import): the component trap answer is lowered to the core trap (`ImpRel`), not assumed.
   `SimpleI.noPlainTrap_impTripleS`: no plain traps. `SimpleI.satP_impTripleS_subset`: every call
   prefix forced by the triple is one of its pending calls (it is saturated).
   `SimpleI.retDet_impTripleS`: at the deterministic profiles `profile o`, returns are
   deterministic (`SessionCat.RetDet`), from `ScalarInstance.Trans.functional`/`player_unique`.
2. **The linked triple** (`LinkedG.compTripleS_eq_linkS`): under `g.WireTy`,

   `LinkedG.compTripleS P g Ii = mapStore (Equiv.prodComm _ _) (linkS (g.exp.sessTripleS P) (SimpleI.impTripleS P g.imp g.wire Ii))`.

   An exact equality of triples (finished behaviours, pending calls, productive streams), with
   no restriction to typed questions. The correspondences: an ill-typed question traps at once
   on both sides with the stores unchanged; a typed `SessRound` is a returning round of the
   importer whose wired calls are served by rounds of the exporter's triple (`ExpRun` = served
   `Rounds`, the wired calls being typed by `WireTy`); the three divergences of
   `LinkedG.RoundDiv` are the three divergence disjuncts of `linkS` (`DivB`: the client
   diverges; `DivA`: the server diverges inside a served call; `Chatter`: a client stream served
   coherently, with no server calls). The pending calls and productive streams of both sides are
   empty (the exporter's triple makes no lower calls).
3. **Sessions.** `threadS_mapStore`: transporting a triple along a store
   equivalence does not change its session from corresponding stores (proved here; not on `main`
   under another name). Hence `LinkedG.compSession_eq_threadS_linkS`:
   `LinkedG.compSession P g = threadS (linkS (g.exp.sessTripleS P) (impTripleS P g.imp g.wire Ii)) (g.exp.init, Ii.store)`,
   and `LinkedG.compSession_eq_mapStore` (the `mapStore` form).
4. **One more importer** (`LinkedG.compTripleS_toExp_eq_linkS`, `LinkedG.compSession_toExp_eq`):
   for the exporter `g.toExp Ii` (so for every link of a chain `LinkedN`, whose exporters are
   built by `LinkedG.toExp`), the triple of `⟨g.toExp Ii, b, w⟩` is the base exporter serving
   `linkS (impTripleS … g.imp …) (impTripleS … b …)`, by `linkS_mapStore_left` and `linkS_assoc`,
   and its session object is the session of that triple from `(g.exp.init, (Ii.store, I.store))`.

**Not claimed.**

* Here only `RetDet` of the importer's triple is proved. Full determinism
  (`SimpleI.det_impTripleS`), the composition form `LinkedG.compSession_eq_comp` (through
  `comp_threadS`) and the closed `n`-fold chain statements are in `LinkedGComp`.
* Host imports (`HLinked2`, `hostLinkS`); the relation of `impTripleS` to the IR denotation
  `g.imp.toComp.den` or to the reference machine; contextual full abstraction; bytes to `Comp`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.{Basic, Link, Thread, Det}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore)
open Silmaril.Games.Abstract.SessionTrap (TrapAbortsRound)
open Silmaril.Games.Abstract.StratSession (threadS NoPlainTrap)
open Silmaril.Games.Abstract.SessionCat (RetDet)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

universe u

/-- **Transport does not change the session**, from corresponding stores (proved). -/
theorem threadS_mapStore {E : Sig.{u}} {S S' A B : Type u} (e : S ≃ S')
    (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s : S) :
    threadS (mapStore e t) (e s) = threadS t s :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.threadS_mapStore e t s

namespace SimpleI

variable {P : Profile} {b : SimpleI} {wire : List Nat} {Ii : ScalarInstance}

/-- **Every round of the importer aborts at a trapped wired call** (proved, every profile). -/
theorem impTripleS_trapAbortsRound : TrapAbortsRound IsTrapS (b.impTripleS P wire Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.impTripleS_trapAbortsRound

/-- **The importer's traps keep its store** (proved). -/
theorem noPlainTrap_impTripleS : NoPlainTrap (b.impTripleS P wire Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.noPlainTrap_impTripleS

/-- **Every call prefix forced by the importer's triple is a pending call** (proved). -/
theorem satP_impTripleS_subset (u : Store Nat) (q : Nat × Payload) :
    StratObs.satP (b.impTripleS P wire Ii) u q ⊆ b.impPend P wire Ii u q :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.satP_impTripleS_subset u q

/-- **Returns of the importer's triple are deterministic** (proved, `profile o`). -/
theorem retDet_impTripleS (o : GrowOracle) : RetDet (b.impTripleS (profile o) wire Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.retDet_impTripleS

end SimpleI

namespace LinkedG

variable {P : Profile} {g : LinkedG} {Ii : ScalarInstance}

/-- **The triple of a linked component is the exporter's triple serving the importer's**, the
stores swapped (proved, `WireTy`). -/
theorem compTripleS_eq_linkS (hw : g.WireTy) :
    LinkedG.compTripleS P g Ii =
      mapStore (Equiv.prodComm g.exp.St (Store Nat))
        (linkS (g.exp.sessTripleS P) (SimpleI.impTripleS P g.imp g.wire Ii)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.compTripleS_eq_linkS hw

/-- **The session object of a linked component**, as the session of the transported linked
triple (proved). -/
theorem compSession_eq_mapStore (hI : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    LinkedG.compSession P g =
      threadS (mapStore (Equiv.prodComm g.exp.St (Store Nat))
          (linkS (g.exp.sessTripleS P) (SimpleI.impTripleS P g.imp g.wire Ii)))
        (Ii.store, g.exp.init) := by
  rw [compSession_eq hI, compTripleS_eq_linkS hw]

/-- **The session object of a linked component is the session of the linked triple** (proved). -/
theorem compSession_eq_threadS_linkS (hI : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    LinkedG.compSession P g =
      threadS (linkS (g.exp.sessTripleS P) (SimpleI.impTripleS P g.imp g.wire Ii))
        (g.exp.init, Ii.store) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.compSession_eq_threadS_linkS hI hw

/-- **One more importer on a linked component** (a link of a chain): the base exporter serving
the two importers linked together, along a store equivalence (proved). -/
theorem compTripleS_toExp_eq_linkS {b : SimpleI} {w : List Nat} {I : ScalarInstance}
    (hw : g.WireTy) (hw' : (LinkedG.mk (g.toExp Ii) b w).WireTy) :
    LinkedG.compTripleS P ⟨g.toExp Ii, b, w⟩ I =
      mapStore ((Equiv.prodAssoc g.exp.St (Store Nat) (Store Nat)).symm.trans
        ((Equiv.prodCongr (Equiv.prodComm g.exp.St (Store Nat)) (Equiv.refl (Store Nat))).trans
          (Equiv.prodComm (Store Nat × g.exp.St) (Store Nat))))
        (linkS (g.exp.sessTripleS P)
          (linkS (SimpleI.impTripleS P g.imp g.wire Ii) (SimpleI.impTripleS P b w I))) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.compTripleS_toExp_eq_linkS hw hw'

/-- **The session object of one more importer on a linked component** (proved). -/
theorem compSession_toExp_eq {b : SimpleI} {w : List Nat} {I : ScalarInstance}
    (hw : g.WireTy) (hw' : (LinkedG.mk (g.toExp Ii) b w).WireTy) (hI : b.mod.IsInst I) :
    LinkedG.compSession P ⟨g.toExp Ii, b, w⟩ =
      threadS (linkS (g.exp.sessTripleS P)
          (linkS (SimpleI.impTripleS P g.imp g.wire Ii) (SimpleI.impTripleS P b w I)))
        (g.exp.init, (Ii.store, I.store)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.compSession_toExp_eq hw hw' hI

end LinkedG

end Silmaril.Wasm.Component.Reference
