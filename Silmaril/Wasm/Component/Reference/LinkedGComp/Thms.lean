module

public import Silmaril.Wasm.Component.Reference.LinkedGComp.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGLink.Thms
public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Thms
public import Silmaril.Games.Abstract.SessionCat.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.Det
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.Chain

/-!
# The canonical object of a link as a composition of sessions: theorems

**Scope.** A linked component `g : LinkedG` (an abstract exporter `g.exp`, a simple importer
`g.imp` at a core instance `Ii`, the wiring `g.wire`) and chains `chainExp e bs Is` built on an
abstract exporter `e` (so `LinkedN.spec n Ib Is`, built on the simple base `n.base`). The
triple-level statements hold at every profile `P`; determinism and composition are at the
deterministic profiles `profile o`. Generic API used: `SessionLink.linkS`/`comp_threadS`,
`SessionLinkAssoc.linkS_assoc`, `SessionLinkCoh.linkS_mapStore_left`,
`SessionCat.retDet_linkS`/`storeDet_of_retDet`, `DStrategy.comp_assoc`.

**Hypotheses.** Wiring: `LinkedG.WireTy` for one link, `ChainWire e bs Is` for chains (implied by
`ChainOk`). Composition: the exporter (resp. the chain's base exporter) is deterministic,
`ExpSpec.Det (profile o)`; for `compSession`, `Ii` is an instance of the importer's core module.
Not needed: `Adeq`, `Good`, `AFun.Det` of the exporter (only `RetDet`, which `ExpSpec.Det` gives).

**Proved.**

1. **The importer's triple is deterministic given answers** (`SimpleI.det_impTripleS`):
   `AFun.Det (SimpleI.impTripleS (profile o) b wire Ii).1`, full determinism (finished rounds
   that return, trap or diverge host-free agree up to their first differing wired answer). The
   key step (`not_inf_of_nf`, local to this topic) is that at `profile o` a thread reaching a
   host-free normal form does not also run host-free forever; `Internal o` is only deterministic
   up to bubbling (`Det.Join`), so this uses the shrinking of the code under two different steps
   (`Internal.shrink`), as `Binaryen.DetLift.nf_not_div` does for configurations.
2. **The exporter's triple** (`ExpSpec.afunDet_sessTripleS_iff`):
   `AFun.Det (e.sessTripleS P).1 ↔ e.TDet P ∧ e.DivExcl P` (`TDet`: `ExpSpec.Det` on typed
   questions; `DivExcl`: a typed question that may diverge has no step). **`ExpSpec.Det` does not
   give `AFun.Det`**: `cexExp` meets `ExpSpec.Det` at every profile (`cexExp_det`) and its triple
   is not `AFun.Det` (`cexExp_not_det`): its one typed question both traps and diverges. Corrected
   statements: `ExpSpec.afunDet_sessTripleS` (from `Det` and `DivExcl`) and
   `ExpSpec.retDet_sessTripleS` (`RetDet` from `Det` alone, which is all composition needs).
3. **A link is the composition of its sides** (`ExpSpec.session_toExp_eq_comp`,
   `LinkedG.compSession_eq_comp`): at `profile o`, for a deterministic exporter,

   `LinkedG.compSession (profile o) g = (g.exp.session (profile o)).comp (g.imp.impSession (profile o) g.wire Ii)`,

   by `SessionLink.comp_threadS` on `LinkedG.compSession_eq_threadS_linkS`; the stores of the
   linked triple are deterministic since `RetDet` of the exporter and of the importer
   (`retDet_impTripleS`) is preserved by `linkS`. `comp_threadS_of_det` is not used: it needs
   `AFun.Det` of the exporter (item 2).
4. **Chains, linked triples** (every `P`, `ChainWire`): `ExpSpec.session_chainExp_eq_linkChain`,
   the session object of a chain is the session of the left-nested iterated link of the base
   exporter's triple with the importers' triples; `ExpSpec.session_chainExp_eq_linkS`, for a
   nonempty chain, the session of the base exporter's triple serving the right-nested link of
   the importers' triples (`impStackT`, by `linkS_assoc`):

   `(chainExp e ((b, w) :: bs) (I :: Is)).session P = threadS (linkS (e.sessTripleS P) (impStackT P b w I bs Is).2.1) (e.init, (impStackT P b w I bs Is).2.2)`.

   `LinkedN.session_spec_eq_linkChain`, `LinkedN.session_spec_eq_linkS`: the same for `n.spec`.
5. **Chains, compositions** (`profile o`, `ChainWire`, `e.Det`):
   `ExpSpec.session_chainExp_eq_sessChain` (left-nested `DStrategy.comp` of the sessions) and
   `ExpSpec.session_chainExp_eq_comp` (the base exporter's session composed with the right-nested
   composition `impStack` of the importers' sessions); `threadS_impStackT`: the right-nested link
   of the importers has `impStack` as its session. `LinkedN.session_spec_eq_sessChain`,
   `LinkedN.session_spec_eq_comp` for `n.spec` (`Simple.expSpec_det`).

**Not claimed.**

* `AFun.Det` of the exporter's triple from `ExpSpec.Det` (false, item 2); `ExpSpec.DivExcl` is not
  proved for `Simple.expSpec` or `LinkedG.toExp`.
* `AFun.Det` of linked triples (`linkS`), which the generic API notes is not preserved by linking.
* Host imports (`HLinked2`, `hostLinkS`); the relation of the importer's session to the IR or the
  reference machine beyond what `LinkedGSession` states for the linked component.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.{Det, Chain}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Games.Abstract.SessionCat (RetDet)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

/-! ## Determinism -/

/-- **The importer's triple is deterministic given answers** (proved, `profile o`). -/
theorem SimpleI.det_impTripleS (o : GrowOracle) {b : SimpleI} {wire : List Nat}
    {Ii : ScalarInstance} : AFun.Det (b.impTripleS (profile o) wire Ii).1 :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.det_impTripleS

namespace ExpSpec

variable {P : Profile} {e : ExpSpec}

/-- **`AFun.Det` of an exporter's triple is `TDet` and `DivExcl`** (proved). -/
theorem afunDet_sessTripleS_iff : AFun.Det (e.sessTripleS P).1 ↔ e.TDet P ∧ e.DivExcl P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.afunDet_sessTripleS_iff

/-- **A deterministic exporter whose divergences exclude steps has a triple deterministic given
answers** (proved). -/
theorem afunDet_sessTripleS (hd : e.Det P) (hx : e.DivExcl P) : AFun.Det (e.sessTripleS P).1 :=
  afunDet_sessTripleS_iff.mpr ⟨fun _ _ _ _ _ _ _ h₁ h₂ => hd h₁ h₂, hx⟩

/-- **A deterministic exporter has deterministic returns** (proved). -/
theorem retDet_sessTripleS (hd : e.Det P) : RetDet (e.sessTripleS P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.retDet_sessTripleS hd

end ExpSpec

/-- **`cexExp` is a deterministic exporter** (proved, every profile). -/
theorem cexExp_det (P : Profile) : cexExp.Det P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.cexExp_det P

/-- **The triple of the deterministic exporter `cexExp` is not `AFun.Det`** (proved): its typed
question both traps and diverges. -/
theorem cexExp_not_det (P : Profile) : ¬ AFun.Det (cexExp.sessTripleS P).1 :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.cexExp_not_det P

/-! ## One link -/

/-- **The exporter of a link is the composition of the exporter's and the importer's sessions**
(proved, `profile o`). -/
theorem ExpSpec.session_toExp_eq_comp {o : GrowOracle} {e : ExpSpec} {b : SimpleI}
    {w : List Nat} {I : ScalarInstance} (hd : e.Det (profile o)) (hw : (LinkedG.mk e b w).WireTy) :
    (LinkedG.toExp ⟨e, b, w⟩ I).session (profile o) =
      (e.session (profile o)).comp (b.impSession (profile o) w I) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.session_toExp_eq_comp hd hw

/-- **The canonical object of a link is the composition of the canonical objects of its two
components** (proved, `profile o`). -/
theorem LinkedG.compSession_eq_comp {o : GrowOracle} {g : LinkedG} {Ii : ScalarInstance}
    (hd : g.exp.Det (profile o)) (hI : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    LinkedG.compSession (profile o) g =
      (g.exp.session (profile o)).comp (g.imp.impSession (profile o) g.wire Ii) := by
  rw [LinkedG.compSession_eq hI]
  exact ExpSpec.session_toExp_eq_comp (I := Ii) hd hw

/-! ## Chains -/

/-- `ChainOk` gives the wiring of the chain (proved). -/
theorem ChainWire.of_chainOk :
    ∀ {e : ExpSpec} {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance},
      ChainOk e bs Is → ChainWire e bs Is
  | _, [], _, _ => trivial
  | _, (_, _) :: _, [], _ => trivial
  | _, (_, _) :: _, _ :: _, h => ⟨h.2.2.1, ChainWire.of_chainOk h.2.2.2⟩

namespace ExpSpec

/-- **The session object of a chain is the session of the left-nested iterated link** (proved,
every profile). -/
theorem session_chainExp_eq_linkChain (P : Profile) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (h : ChainWire e bs Is) :
    (chainExp e bs Is).session P = linkChain P (e.sessTripleS P) e.init bs Is :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.session_chainExp_eq_linkChain P e bs Is h

/-- **The session object of a chain is the base exporter serving the importers linked
right-nested** (proved, every profile). -/
theorem session_chainExp_eq_linkS (P : Profile) {e : ExpSpec} {b : SimpleI} {w : List Nat}
    {I : ScalarInstance} {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance}
    (h : ChainWire e ((b, w) :: bs) (I :: Is)) :
    (chainExp e ((b, w) :: bs) (I :: Is)).session P =
      threadS (linkS (e.sessTripleS P) (impStackT P b w I bs Is).2.1)
        (e.init, (impStackT P b w I bs Is).2.2) :=
  (session_chainExp_eq_linkChain P h).trans
    (Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.linkChain_cons_eq P b w I bs Is _ _)

/-- **The session object of a chain is the left-nested composition of the sessions** (proved,
`profile o`). -/
theorem session_chainExp_eq_sessChain {o : GrowOracle} {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (hd : e.Det (profile o))
    (h : ChainWire e bs Is) :
    (chainExp e bs Is).session (profile o) =
      sessChain (profile o) (e.session (profile o)) bs Is :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.session_chainExp_eq_sessChain e bs Is hd h

/-- **The session object of a chain is the base exporter's session composed with the
right-nested composition of the importers' sessions** (proved, `profile o`). -/
theorem session_chainExp_eq_comp {o : GrowOracle} {e : ExpSpec} {b : SimpleI} {w : List Nat}
    {I : ScalarInstance} {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance}
    (hd : e.Det (profile o)) (h : ChainWire e ((b, w) :: bs) (I :: Is)) :
    (chainExp e ((b, w) :: bs) (I :: Is)).session (profile o) =
      (e.session (profile o)).comp (impStack (profile o) b w I bs Is) :=
  (session_chainExp_eq_sessChain hd h).trans
    (Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.sessChain_cons_eq _ b w I bs Is _)

end ExpSpec

/-- **The right-nested link of the importers has the right-nested composition of their sessions
as its session** (proved, `profile o`). -/
theorem threadS_impStackT (o : GrowOracle) (b : SimpleI) (w : List Nat) (I : ScalarInstance)
    (bs : List (SimpleI × List Nat)) (Is : List ScalarInstance) :
    threadS (impStackT (profile o) b w I bs Is).2.1 (impStackT (profile o) b w I bs Is).2.2 =
      impStack (profile o) b w I bs Is :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.threadS_impStackT b w I bs Is

namespace LinkedN

variable {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}

/-- **The session object of a chain of simple modules, as a left-nested iterated link**
(proved, every profile). -/
theorem session_spec_eq_linkChain (P : Profile)
    (h : ChainWire (Simple.expSpec n.base Ib) n.links Is) :
    (n.spec Ib Is).session P =
      linkChain P ((Simple.expSpec n.base Ib).sessTripleS P) Ib.store n.links Is :=
  ExpSpec.session_chainExp_eq_linkChain P h

/-- **The session object of a chain of simple modules, as the base serving the importers linked
right-nested** (proved, every profile). -/
theorem session_spec_eq_linkS (P : Profile) {b : SimpleI} {w : List Nat}
    {bs : List (SimpleI × List Nat)} {I : ScalarInstance} (hl : n.links = (b, w) :: bs)
    (h : ChainWire (Simple.expSpec n.base Ib) n.links (I :: Is)) :
    (n.spec Ib (I :: Is)).session P =
      threadS (linkS ((Simple.expSpec n.base Ib).sessTripleS P) (impStackT P b w I bs Is).2.1)
        (Ib.store, (impStackT P b w I bs Is).2.2) := by
  rw [hl] at h
  unfold LinkedN.spec
  rw [hl]
  exact ExpSpec.session_chainExp_eq_linkS P h

/-- **The session object of a chain of simple modules is the left-nested composition of the
sessions** (proved, `profile o`). -/
theorem session_spec_eq_sessChain (o : GrowOracle)
    (h : ChainWire (Simple.expSpec n.base Ib) n.links Is) :
    (n.spec Ib Is).session (profile o) =
      sessChain (profile o) ((Simple.expSpec n.base Ib).session (profile o)) n.links Is :=
  ExpSpec.session_chainExp_eq_sessChain (Simple.expSpec_det o n.base Ib) h

/-- **The session object of a chain of simple modules is the base's session composed with the
right-nested composition of the importers' sessions** (proved, `profile o`). -/
theorem session_spec_eq_comp (o : GrowOracle) {b : SimpleI} {w : List Nat}
    {bs : List (SimpleI × List Nat)} {I : ScalarInstance} (hl : n.links = (b, w) :: bs)
    (h : ChainWire (Simple.expSpec n.base Ib) n.links (I :: Is)) :
    (n.spec Ib (I :: Is)).session (profile o) =
      ((Simple.expSpec n.base Ib).session (profile o)).comp (impStack (profile o) b w I bs Is) := by
  rw [hl] at h
  unfold LinkedN.spec
  rw [hl]
  exact ExpSpec.session_chainExp_eq_comp (Simple.expSpec_det o n.base Ib) h

end LinkedN

end Silmaril.Wasm.Component.Reference
