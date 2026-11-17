module

public import Silmaril.Wasm.Component.Reference.LinkedGDiv.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGChain.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Main

/-!
# Divergence through an abstract exporter: theorems

**Scope.** Every profile `P` and component choice profile `prof`; the reference machine over
`core3P P` under `linkHost impl` (any host state type and host functions); `LinkedG` with an
exporter meeting `ExpSpec.RefAdeqUXD` (`RefAdeqUX` and R7) and a link meeting
`LinkedG.LinkOk`; chains built on such an exporter (`ChainOkR`); typed calls and a typed pending
call. The IR side is the law `ExpSpec.AdeqD` for a simple exporter only.

**Proved (public, below).**

1. **The exporter interface with divergence, for `Simple`.**
   * `Simple.expSpec_adeqD`: the IR law (`Comp.denUD (impSemD P)`): after typed complete rounds,
     a typed question is an IR divergence iff a session of the rounds reaches a store from which
     the call diverges (`DivAt`), along one run, at every profile;
   * `Simple.expSpec_refAdeqUXD`: R1–R7 (`RefAdeqUXD`) under the hypotheses of
     `Simple.expSpec_refAdeqU`: R7 forward is `DivAt` mapped step for step to the shared core
     store (`link_inf`), R7 backward splits a divergence of the core activation into an
     infinite core run (`DivAt`, `link_inf_back`) or a return of values after which the machine
     diverges (`coreCfg_diverges_step`; a core trap does not diverge).
2. **`LinkedG.sessDivs = LinkedG.refDivs`** (`LinkedG.divSpecToRef`, `LinkedG.divRefToSpec`,
   `LinkedG.sessDivs_eq_refDivs`), the three sources being the importer diverging host-free
   (`Linked2.DivB`), the exporter's served call diverging (`LinkedG.DivA`, the exporter's
   `DivStep`) and chatter (`LinkedG.Chatter`):
   * spec → reference by forward runs: the session prefix by `linkCall_fwdB`, the round's prefix
     by `roundsPre_fwdB` (a prefix variant of `rounds_fwdB`), then (i) `link_inf`, (ii) the
     nested call to the exporter's activation (`nest_atX`) and R7 forward, (iii) a coinduction
     over non-empty served calls (`call_stepB'` now records that its run is non-empty);
   * reference → spec by classification: the session prefix by `linkCall_invB`; in the
     diverging call, from the importer's core activation, a round is (i) an infinite core run,
     (ii) a callout whose nested call diverges by R7 backward, (iii) a served call back to the
     invariant, or (iv) an exit of the importer, which does not diverge at a top-level call;
     classical case analysis and dependent choice give a finite chain followed by (i), (ii) or
     chatter.
3. **A linked component meets R7** (`LinkedG.toExp_refAdeqUXD`), its `DivStep` the linked
   `RoundDiv`, so by induction chains do (`chainExp_refAdeqUXD`), and divergence equality holds
   for one more importer on a chain (`chain_sessDivs_eq_refDivs`) and for `LinkedN` with a simple
   base (`LinkedN.sessDivs_eq_refDivs`). R7 backward for the linked component is the
   classification above in any frame, with the footprint tracked (`RelT`): case (iv), a return of
   the importer's activation after the chain of served calls, is R2's return (`EndsT`, a
   `SessRound` step), from which the machine diverges.

**Deviations.**

* **R7 is not an iff between `DivStep` and divergence from the exporter's activation**: the
  caller's continuation `K` may diverge after a returning call. R7 backward therefore splits a
  divergence at the first return of the activation (`RefData.Div`), as R3 splits finite runs.
* `call_stepB'`/`call_stepB` (`LinkedGRound`) gained a conjunct, the returning run is
  non-empty, for the productivity of chatter. Their callers were updated; no public statement
  changed.
* `ExpSpec` gained the field `DivStep`; `Simple.expSpec` and `LinkedG.toExp` define it
  (`DivAt`, the linked `RoundDiv`). No public statement changed.

**Not claimed.**

* The IR side for linked components: `LinkedG.toExp` meeting `ExpSpec.AdeqD` (the linked IR
  divergence iff `sessDivs`, #789–#825 generalised); only the simple exporter's IR law is
  proved. For `Linked2` the read-back of chatter needs a deterministic profile (`profile o`), so
  the general statement is expected to need it too.
* Infinite plays, ill-typed calls, host imports of the importer.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.{Simple, SimpleIR, Round, Call,
Back, Classify, CallBack, Exp, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Step 1: a simple exporter -/

/-- **The IR divergence law of a simple exporter** (proved, every profile). -/
theorem Simple.expSpec_adeqD (P : Profile) {c : Simple} (hc : c.Good) {I : ScalarInstance}
    (hI : c.mod.IsInst I) : (Simple.expSpec c I).AdeqD P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.simple_adeqD P hc hI

/-- **A simple exporter meets R1–R7** (proved, every profile), under the hypotheses of
`Simple.expSpec_refAdeqU`. -/
theorem Simple.expSpec_refAdeqUXD (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : ScalarInstance} (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqUXD P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.simple_refAdeqUXD P hc hi hI hS hN

/-- **`RefAdeqUXD` implies `RefAdeqUX`** (proved). -/
theorem ExpSpec.RefAdeqUXD.refAdeqUX {P : Profile} {e : ExpSpec} (h : e.RefAdeqUXD P) :
    e.RefAdeqUX P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.refAdeqUXD_refAdeqUX h

/-! ## Step 2: divergence of a linked component with an abstract exporter -/

namespace LinkedG

/-- **Specification divergence is reference divergence** (proved, every profile and component
choice profile, under every host). -/
theorem divSpecToRef (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) {Ii : ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessDivs P lg Ii calls j vs ⊆ LinkedG.refDivs P prof lg impl h₀ calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.divSpecToRefD P prof he hl impl h₀ calls j
    vs hI

/-- **Reference divergence is specification divergence** (proved, every profile and component
choice profile, under every host, typed calls and a typed pending call). -/
theorem divRefToSpec (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls lg.imp calls)
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.refDivs P prof lg impl h₀ calls j vs ⊆ LinkedG.sessDivs P lg Ii calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.divRefToSpecD P prof he hl impl h₀ calls j
    vs ht hvs hI

/-- **The diverging session calls of a linked component with an abstract exporter**: those of
the specification are those of the reference machine (proved). -/
theorem sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls lg.imp calls)
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessDivs P lg Ii calls j vs = LinkedG.refDivs P prof lg impl h₀ calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.sessDivs_eq_refDivsG P prof he hl impl h₀
    calls j vs ht hvs hI

/-! ## Step 3: a linked component meets R7; chains -/

/-- **A linked component is a reference exporter with divergence** (proved, every profile): its
`DivStep` is the linked `RoundDiv`. -/
theorem toExp_refAdeqUXD (P : Profile) {lg : LinkedG} {Ii : ScalarInstance}
    (he : lg.exp.RefAdeqUXD P) (hl : lg.LinkOk) (hI : lg.imp.mod.IsInst Ii) :
    (lg.toExp Ii).RefAdeqUXD P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.toExp_refAdeqUXD P lg Ii he hl hI

end LinkedG

/-- **Chains of reference exporters with divergence** (proved, by induction). -/
theorem chainExp_refAdeqUXD (P : Profile) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.RefAdeqUXD P) (h : ChainOkR e bs Is) :
    (chainExp e bs Is).RefAdeqUXD P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.chainExp_refAdeqUXD P e bs Is he h

/-- **The diverging session calls of one more importer on a chain** (proved, every profile and
component choice profile, under every host). -/
theorem chain_sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) {e : ExpSpec}
    {bs : List (SimpleI × List Nat)} {Is : List ScalarInstance} (he : e.RefAdeqUXD P)
    (h : ChainOkR e bs Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (chainExp e bs Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal)) (j : Fin b.exports.length)
    (vs : List IVal) (ht : SimpleI.TypedCalls b calls)
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : b.mod.IsInst Ii) :
    LinkedG.sessDivs P ⟨chainExp e bs Is, b, w⟩ Ii calls j vs =
      LinkedG.refDivs P prof ⟨chainExp e bs Is, b, w⟩ impl h₀ calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.chain_sessDivs_eq_refDivs P prof he h hl
    impl h₀ calls j vs ht hvs hI

/-- **The diverging session calls of a chain** (proved, every profile and component choice
profile, under every host): for the chain `n` (simple base under the hypotheses of
`Simple.expSpec_refAdeqU`, links meeting `ChainOkR`) with one more importer `b` meeting `LinkOk`,
the diverging session calls of the specification are those of the reference machine. -/
theorem LinkedN.sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) {n : LinkedN}
    {Ib : ScalarInstance} {Is : List ScalarInstance} (hb : n.base.Good) (hbi : n.base.Inst)
    (hIb : n.base.mod.IsInst Ib) (hbS : Linked2.ModSplitOk n.base.mod.mod)
    (hbN : ∀ x ∈ n.base.exports, ∀ m, x.name ≠ tag "t" m)
    (h : ChainOkR (Simple.expSpec n.base Ib) n.links Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (n.spec Ib Is) b w).LinkOk) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin b.exports.length × List IVal)) (j : Fin b.exports.length)
    (vs : List IVal) (ht : SimpleI.TypedCalls b calls)
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) {Ii : ScalarInstance}
    (hI : b.mod.IsInst Ii) :
    LinkedG.sessDivs P ⟨n.spec Ib Is, b, w⟩ Ii calls j vs =
      LinkedG.refDivs P prof ⟨n.spec Ib Is, b, w⟩ impl h₀ calls j vs :=
  chain_sessDivs_eq_refDivs P prof (Simple.expSpec_refAdeqUXD P hb hbi hIb hbS hbN) h hl impl h₀
    calls j vs ht hvs hI

end Silmaril.Wasm.Component.Reference
