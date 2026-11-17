module

public import Silmaril.Wasm.Component.Reference.LinkedGInst.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGInit.Thms
public import Silmaril.Wasm.Component.Reference.LinkedGInv.Thms
public import Silmaril.Wasm.Component.Reference.LinkedG.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Simple

/-!
# The instantiation of a linked component read back: theorems

**Scope.** Every profile `P` and component choice profile; the reference machine over `core3P P`
under `linkHost impl` (any host state type and host functions); `LinkedG.toRef` with an exporter
meeting `ExpSpec.RefAdeqU` (`Defs`: R1, R2, R3 as `BwdF`, R4 as `InitU`, R5, R6) and an importer
as in `Linked2.Adequate` (`Good`, `Inst`, within the flat arities, float-free, in the split
fragment, export names that are not generated type names, wired injectively and well typed);
typed calls.

**Proved (public, below).**

* `ExpSpec.RefData.InitU.initS`, `ExpSpec.RefAdeqU.refAdeqF`: `InitU` implies `InitS`, so
  `RefAdeqU` implies `RefAdeqF` of `LinkedGInv` (and `RefAdeqS` of `LinkedGInit`).
* `Simple.expSpec_refAdeqU`: a simple exporter meets `RefAdeqU`, under the hypotheses of
  `Simple.expSpec_refAdeqF`: its nested instantiation is a big-step run of a program without
  choices, hence a live deterministic run, and keeps the waiting threads.
* `LinkedG.instBehaviours_eqU`: **the instantiation results of `lg.toRef` are exactly one
  instance**, at a configuration with the host in control, not locked down and with no waiting
  thread, with the root instance `0` and the importer's exports at consecutive functions.
* `LinkedG.sess_refToSpecU`: **every session behaviour of typed calls of `lg.toRef` is the
  reference image of a `LinkedG.SessSpec` session** from the importer's instance store and the
  exporter's initial state.
* `LinkedG.sessObs_eqU`: with `LinkedG.sess_specToRefB`, the session observations of typed calls
  are exactly those images.
* `LinkedG.sessAdequacy_fullU`: for an exporter that also meets the IR interface
  (`ExpSpec.Adeq`), the session observations of typed calls are exactly the reference images of
  the outcome lists whose session play is a play of `lg.toComp.den (impSem P)`
  (`LinkedG.sessIR_iff`).
* `Linked2.sessObs_eq_viaG`, `Linked2.sessAdequacy_full_viaG`: `Linked2.sessObs_eq` and
  `Linked2.sessAdequacy_full` re-derived from the two previous items at `Linked2.toG l Ie` with
  `Simple.expSpec_refAdeqU`.

**Proved (proof-internal, in `Proofs.….LinkedGInst`).**

* `ReachL` (`ReachL`): `Reach` of `LinkedGInit` whose run is a live run of unique steps (`LRun`),
  with its monad laws and big-step runs; R4 with the read-back as a `ReachL` (`reach_initU`, its
  end `InitW`: `InitAt` and the waiting threads kept);
* `instG_lrun` (`Run`): **the parent's stages inverted**: the stages of `instG_run` as `ReachL`s,
  so the instantiation of `lg.toRef` after its host event is one live run to `afterG`;
* `instBehavioursG_toRef` (`Inst`): the instantiation results are exactly the instance at
  `afterG` (every host-free run after the host event that ends with the host in control or locked
  down is that live run, and a divergence would diverge from `afterG`); `afterG_waiting`: no
  waiting thread there. With `readyB_init` and `statB_init` of `LinkedGInit`, `afterG` is between
  calls (`ReadyB`) with an empty waiting list, from where `sessL_invB` of `LinkedGInv` reads the
  sessions back (`Sess`).

**Deviations.**

* **R4's read-back is a determinism law**, not a law over every run: `InitU` asks R4's run to be
  a live deterministic run (`LiveDet`). The alternative, every host-free run of the nested
  instantiation reaching an `InitAt` end, would not exclude divergence or a stop at a
  configuration that is not live but not an end either; determinism gives both (`LRun.inv`,
  `LRun.diverges`). An exporter whose instantiation makes a choice (`choose`) does not meet it.
* **The waiting threads** are part of `InitU` (`m.store.waiting = M.store.waiting`), not of
  `InitAt`, so that `InitS` and the forward theorems are unchanged.
* `sessAdequacy_fullU` takes the IR interface `ExpSpec.Adeq` separately: `RefAdeqU` speaks of the
  reference machine only.

**Any host code in the exporter's store (proved, public, below).** `InitUX`/`RefAdeqUX`
(`Defs`) are `InitU`/`RefAdeqU` without `InitAt.hostFree`; `InitU.initUX`, `InitUX.initSX`,
`RefAdeqU.refAdeqUX`; `LinkedG.instBehaviours_eqUX`, `sess_refToSpecUX`, `sessObs_eqUX`,
`sessAdequacy_fullUX` are the theorems above for `RefAdeqUX`, and the `RefAdeqU` ones are derived
from them. `StatB` (`ImpStatG.tramp`) asks only that the trampoline map invert the host-code
renaming on every host function of the shared store; `statB_init` meets it with `trX`/`gX`
(`LinkedGInit`), which send the exporter's host code above the importer's imports.

**Not claimed.** A linked component as an exporter on the reference side
(`Task.linkedG.toExpRefAdeqUX` of `LinkedGChain`, open) and so `LinkedN.sessAdequacy_full` only
conditionally (`LinkedGChain`); divergence and infinite plays; ill-typed calls.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **`InitU` implies `InitS`** (proved). -/
theorem ExpSpec.RefData.InitU.initS {P : Profile} {e : ExpSpec} {d : e.RefData P} (h : d.InitU) :
    d.InitS :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.initU_initS h

/-- **`RefAdeqU` implies `RefAdeqF`** (proved). -/
theorem ExpSpec.RefAdeqU.refAdeqF {P : Profile} {e : ExpSpec} (h : e.RefAdeqU P) :
    e.RefAdeqF P :=
  let ⟨d, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  ⟨d, h₁, h₂, h₃, h₄.initS, h₅, h₆⟩

/-- **A simple exporter meets `RefAdeqU`** (proved, every profile), under the hypotheses of
`Simple.expSpec_refAdeqF`. -/
theorem Simple.expSpec_refAdeqU (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : ScalarInstance} (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqU P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.simple_refAdeqU P hc hi hI hS hN

/-! ## Any host code in the exporter's core store

`InitUX`/`RefAdeqUX` (`Defs`) drop `InitAt.hostFree`: the importer's static facts read the host
code of the shared store through a renaming inverted on every host function present, so the
theorems below hold for exporters whose core store has host functions of their own (a linked
exporter's trampolines). The `RefAdeqU` theorems are their instances. -/

/-- **`InitU` implies `InitUX`** (proved). -/
theorem ExpSpec.RefData.InitU.initUX {P : Profile} {e : ExpSpec} {d : e.RefData P}
    (h : d.InitU) : d.InitUX :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.initU_initUX h

/-- **`InitUX` implies `InitSX`** (proved). -/
theorem ExpSpec.RefData.InitUX.initSX {P : Profile} {e : ExpSpec} {d : e.RefData P}
    (h : d.InitUX) : d.InitSX :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.initUX_initSX h

/-- **`RefAdeqU` implies `RefAdeqUX`** (proved). -/
theorem ExpSpec.RefAdeqU.refAdeqUX {P : Profile} {e : ExpSpec} (h : e.RefAdeqU P) :
    e.RefAdeqUX P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.refAdeqU_refAdeqUX h

namespace LinkedG

/-- **`instBehaviours_eqU` for `RefAdeqUX`** (proved, every profile, component choice profile
and host functions). -/
theorem instBehaviours_eqUX (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUX P) (hW : lg.WireTy) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) :
    ∃ (m : Machine.Config (core3P P) σ) (fb : Nat), m.ctl = [] ∧ m.store.lockdown = false ∧
      m.store.waiting = [] ∧
      instBehaviours prof (linkHost impl) (initConfig h₀) lg.toRef [] =
        {.instance m ⟨0⟩ (lg.imp.exports.mapIdx fun i x => (x.name, (⟨fb + i⟩ : FuncId)))} :=
  let ⟨_, hFr, _, _, hInit, _, _⟩ := he
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.instBehavioursG_eq hInit hFr hW hIg hIi
    hIa ⟨hS.data, hS.elems⟩ hNI prof impl h₀

/-- **`sess_refToSpecU` for `RefAdeqUX`** (proved, every profile and component choice
profile). -/
theorem sess_refToSpecUX (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUX P) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin lg.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls lg.imp calls)
    {Ii : ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {o : List (Option (List Silmaril.Wasm.Component.Reference.Val))}
    (ho : o ∈ LinkedG.sessObs prof lg impl h₀ calls) :
    ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
      LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s' ∧ o = refOuts outs :=
  let ⟨_, hFr, _, hBw, hInit, hRes, hB⟩ := he
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.sess_refToSpecU P prof hInit hFr hBw hRes
    hB hW hn hIg hIi hIa hff hS hNI impl h₀ ht hI ho

/-- **`sessObs_eqU` for `RefAdeqUX`** (proved, every profile and component choice profile,
typed calls). -/
theorem sessObs_eqUX (P : Profile) (prof : ProfileKind) {lg : LinkedG} (he : lg.exp.RefAdeqUX P)
    (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls lg.imp calls) {Ii : ScalarInstance} (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessObs prof lg impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
        LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s' ∧ o = refOuts outs} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.sessObs_eqU P prof he hW hn hIg hIi hIa
    hff hS hNI impl h₀ calls ht hI

/-- **`sessAdequacy_fullU` for `RefAdeqUX`** (proved, every profile and component choice
profile, typed calls). -/
theorem sessAdequacy_fullUX (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqUX P) (hA : lg.exp.Adeq P) (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hIg : lg.imp.Good) (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin lg.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls lg.imp calls) :
    LinkedG.sessObs prof lg impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        lg.sessMoves calls outs ∈ lg.toComp.den (impSem P)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.sessAdequacy_fullU P prof he hA hW hn hIg
    hIi hIa hff hS hNI impl h₀ calls ht

/-- **The instantiation results of a linked component are exactly one instance** (proved, every
profile, component choice profile and host functions): at a configuration with the host in
control, not locked down and with no waiting thread, with the root instance `0` and export `i`
of the importer at function `fb + i`. -/
theorem instBehaviours_eqU (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqU P) (hW : lg.WireTy) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) :
    ∃ (m : Machine.Config (core3P P) σ) (fb : Nat), m.ctl = [] ∧ m.store.lockdown = false ∧
      m.store.waiting = [] ∧
      instBehaviours prof (linkHost impl) (initConfig h₀) lg.toRef [] =
        {.instance m ⟨0⟩ (lg.imp.exports.mapIdx fun i x => (x.name, (⟨fb + i⟩ : FuncId)))} :=
  instBehaviours_eqUX P prof he.refAdeqUX hW hIg hIi hIa hS hNI impl h₀

/-- **Reference sessions of a linked component with an abstract exporter are specification
sessions** (proved, every profile and component choice profile): every session behaviour of
typed calls of `lg.toRef` is the reference image of the outcomes of a `LinkedG.SessSpec` session
from the importer's instance store and the exporter's initial state. -/
theorem sess_refToSpecU (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqU P) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin lg.imp.exports.length × List IVal)} (ht : SimpleI.TypedCalls lg.imp calls)
    {Ii : ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {o : List (Option (List Silmaril.Wasm.Component.Reference.Val))}
    (ho : o ∈ LinkedG.sessObs prof lg impl h₀ calls) :
    ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
      LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s' ∧ o = refOuts outs :=
  sess_refToSpecUX P prof he.refAdeqUX hW hn hIg hIi hIa hff hS hNI impl h₀ ht hI ho

/-- **The session observations of a linked component with an abstract exporter are exactly the
specification sessions'** (proved, every profile and component choice profile, typed calls). -/
theorem sessObs_eqU (P : Profile) (prof : ProfileKind) {lg : LinkedG} (he : lg.exp.RefAdeqU P)
    (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls lg.imp calls) {Ii : ScalarInstance} (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessObs prof lg impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
        LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s' ∧ o = refOuts outs} :=
  sessObs_eqUX P prof he.refAdeqUX hW hn hIg hIi hIa hff hS hNI impl h₀ calls ht hI

/-- **Finite session adequacy of a linked component with an abstract exporter** (proved, every
profile and component choice profile, typed calls): for an exporter meeting the reference
interface `RefAdeqU` and the IR interface `Adeq`, the session observations are exactly the
reference images of the outcome lists whose session play, continuing after traps, is a play of
`lg.toComp.den (impSem P)`. -/
theorem sessAdequacy_fullU (P : Profile) (prof : ProfileKind) {lg : LinkedG}
    (he : lg.exp.RefAdeqU P) (hA : lg.exp.Adeq P) (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hIg : lg.imp.Good) (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin lg.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls lg.imp calls) :
    LinkedG.sessObs prof lg impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        lg.sessMoves calls outs ∈ lg.toComp.den (impSem P)} :=
  sessAdequacy_fullUX P prof he.refAdeqUX hA hW hn hIg hIi hIa hff hS hNI impl h₀ calls ht

end LinkedG

namespace Linked2

/-- **`Linked2.sessObs_eq` through `LinkedG`** (proved): the same statement, derived from
`LinkedG.sessObs_eqU` at `Linked2.toG l Ie` with `Simple.expSpec_refAdeqU`. -/
theorem sessObs_eq_viaG (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {Ie Ii : ScalarInstance} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' π' : Store Nat),
        Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' ∧ o = refOuts outs} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.linked2_sessObs_eqU P prof l hl impl h₀
    calls ht hIe hIi

/-- **`Linked2.sessAdequacy_full` through `LinkedG`** (proved): the same statement, derived from
`LinkedG.sessAdequacy_fullU` at `Linked2.toG l Ie` with `Simple.expSpec_refAdeqU` and
`Linked2.toG_adeq`. -/
theorem sessAdequacy_full_viaG (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.linked2_sessAdequacy_fullU P prof l hl
    impl h₀ calls ht

end Linked2

end Silmaril.Wasm.Component.Reference
