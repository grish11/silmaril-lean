module

public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionObs.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Abstract.NodeTrap.Thms
public import Silmaril.Wasm.Component.DWiringMulti.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.Basic

/-!
# Linked sessions against the divergence-aware IR denotation: theorems

**Scope.** `Linked2` (the import-free exporter A answering every import of the importer B), at
every profile `P` unless stated; the IR is the divergence-aware denotation
`l.toComp.denD (impSemD P)` (`Silmaril.Wasm.Component.DWiring`), the reference component is
`l.toRef` under `linkHost impl`, every host.

**The core semantics** (`impSemD P`, `LinkedSessionD.Defs`):

* `forget_impSemD : (impSemD P).forget = impSem P`, hence for every component
  `toStrategy_denD_impSemD : (c.denD (impSemD P)).toStrategy = c.den (impSem P)` (and over
  `sigU`);
* a core node of `impSemD P` on a module with an instance is the core node of `core3SemD P` at
  that instance (`node_impSemD`), so it propagates traps (`trapPropagating_impSemD`, from
  `NodeTrap.trapPropagating_core3SemD`);
* hence a `SimpleI` component (the exporter `SimpleI.ofSimple l.exp` and the importer `l.imp`
  of a `Linked2`) diverges over `sigU` only by its core node's own divergence, with no chatter at
  `maskH` (`SimpleI.div_denUD_impSemD`).

**Finite plays of `Linked2`** (from `LinkedSessionAdeq`, `LinkedSessionEquiv`, under
`Linked2.Adequate`): finite session adequacy (`Linked2.sessAdequacy_fullD`) and the finite
injection (`Linked2.sessEquiv_iffD`) restated on the finite plays of the divergence-aware IR.

**Divergence and infinite plays of `Linked2`: what is proved.**

* **Sources** (`Linked2.div_denD_sources`, every `DCoreSem`, no hypothesis): the divergences of
  `l.toComp.denD C` (written `Comp.mk [] [l.expNode, l.impNode] l.compExports`, `toComp_eq`)
  are those of `Linked2.linkDiv C l`, the union of the exporter's environment
  diverging, routed through the importer's node (`EnvDiv`; A diverging inside a call of B, or
  on its own), the importer's node diverging (`NodeDiv`), and chatter between the two nodes
  (`NodeChatter`), seen through `exportsH`, `widenH 0` and `narrowH`. This is `div_denD_nodes`
  with the two nodes of `l.toComp` unfolded; it is the IR side of #730's `DivA`, `DivB` and
  `Chatter`.
* **The session prefix of a divergence is a reference session** (`Linked2.sessSpec_of_div`,
  `Linked2.sessObs_of_div`, under `Linked2.Adequate`, typed calls): if
  `sessMoves calls outs ++ r` is an IR divergence, then `calls` with `outs` is a specification
  session from the instances' stores, and `refOuts outs` a reference session outcome.
* **The same for infinite plays** (`Linked2.sessObs_of_inf`): every typed session prefix
  `sessMoves calls outs` of an IR infinite play gives a reference session outcome.
* **Productive executions are IR plays** (`Linked2.refSessProd_iff_plays`, at `profile o`):
  `Linked2.RefSessProd` of a typed stream of calls holds iff every finite session prefix of the
  stream is a finite play of `l.toComp.denD (impSemD (profile o))`.

**Not proved here** (the remaining targets).

* `sessDivs ⊆` IR divergences and its converse: relating `Linked2.linkDiv (impSemD P) l`, after
  the session prefix and the pending ask `(j, vs)`, to `Linked2.RoundDiv`. This needs the
  read-back of #724 (`LinkedSessionAdeq`) for **pending** rounds (B's instance `.running`), the
  divergence of a core node of `core3SemD` through the coercions `importH`, `spullD`,
  `exportH` (`instFinS`'s `.div` is `Diverges`, which is #730's `DivB`), and for chatter, the
  infinite plays of B's node within one round (`instInf`) against infinite plays of A's node.
* The infinite plays: that the limit of the session prefixes of a productive execution is in
  `(l.toComp.denD (impSemD P)).inf` (the `inf` of a composite needs runs of each component,
  `inf_comp_eq`), and conversely that an IR infinite play is such a limit.
* Hence the combined injection `RefSessEquivFull ↔ SameTypes ∧` equal divergence-aware IR
  denotations. The equality would be stated over `sigU` (`Comp.denUD`) or by a `pubPlays`-style
  projection, since `l.toComp.denD` and `l'.toComp.denD` have different types.

No counterexample was found: B's import calls go through `canon lower` (arguments that do not
lift trap without a call, and a trap answer aborts B's round, `NodeTrap`), A has no imports, and
the outer `maskH 0` sees no call, so every IR divergence after a typed prefix is expected to be
one of `DivB`, `DivA`, `Chatter`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component
open Silmaril.Wasm.Abstract.InstSession (core3SemD)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The core semantics -/

/-- `impSem P` on a module with an instance is `core3Sem P` at that instance. -/
theorem impSem_sem_of (P : Profile) {m : ImpModule} (h : ∃ I, m.IsInst I) :
    (impSem P).sem m = (core3Sem P).sem (m.numInst h) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.impSem_sem_of P h

/-- `impSemD P` on a module with an instance is `core3SemD P` at that instance. -/
theorem impSemD_sem_of (P : Profile) {m : ImpModule} (h : ∃ I, m.IsInst I) :
    (impSemD P).sem m = (core3SemD P).sem (m.numInst h) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.impSemD_sem_of P h

/-- **The finite plays of `impSemD P` are `impSem P`.** -/
theorem forget_impSemD (P : Profile) : (impSemD P).forget = impSem P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.forget_impSemD P

/-- **Finite agreement over `sigU`.** -/
theorem toStrategy_denUD_impSemD (P : Profile) (c : Comp ImpModule) :
    (c.denUD (impSemD P)).toStrategy = c.denU (impSem P) := by
  rw [toStrategy_denUD, forget_impSemD]

/-- **Finite agreement at the interface signatures**: the divergence-aware denotation of a
component over `impSemD P` has exactly the finite plays of `c.den (impSem P)`. -/
theorem toStrategy_denD_impSemD (P : Profile) (c : Comp ImpModule) :
    (c.denD (impSemD P)).toStrategy = c.den (impSem P) := by
  rw [toStrategy_denD, forget_impSemD]

/-- A core node of `impSemD P` on a module with an instance is the core node of `core3SemD P` at
that instance. -/
theorem node_impSemD (P : Profile) (e : Nat) {m : ImpModule} (h : ∃ I, m.IsInst I)
    (args : List Impl) :
    Node.denD (impSemD P) e (.core m args) =
      Node.denD (core3SemD P) e (.core (m.numInst h) args) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.node_impSemD P e h args

/-- **A core node of `impSemD P` propagates traps**, when its module has an instance. -/
theorem trapPropagating_impSemD (P : Profile) (e : Nat) {m : ImpModule}
    (h : ∃ I, m.IsInst I) (args : List Impl) :
    TrapPropagating (Node.denD (impSemD P) e (.core m args)) := by
  rw [node_impSemD P e h args]
  exact Silmaril.Wasm.Abstract.NodeTrap.trapPropagating_core3SemD P e _ args

/-- `SimpleI.toComp` with its core node and its exports named. -/
theorem SimpleI.toComp_eq (c : SimpleI) :
    c.toComp = .mk c.imports [c.coreNode] c.compExports := rfl

/-- **A simple component with imports diverges only where its core node does** (when its module
has an instance), stated on `c.toComp` written out (`SimpleI.toComp_eq`): the divergences over
`sigU` are the core node's own divergences above `maskH`, seen through the export handler. There
is no chatter between the node and `maskH`: the node propagates traps. -/
theorem SimpleI.div_denUD_impSemD (P : Profile) (c : SimpleI) (h : ∃ I, c.mod.IsInst I) :
    ((Comp.mk c.imports [c.coreNode] c.compExports).denUD (impSemD P)).div =
      {p | ∃ s t, Zip s t p ∧
        s ∈ NodeDiv c.imports.length (Strategy.ofHandler (maskH c.imports.length))
          (Node.denD (impSemD P) c.imports.length c.coreNode) ∧
        t ∈ Strategy.ofHandler
          (exportsH (envAfter c.imports.length [c.coreNode]) c.compExports)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.div_denUD_simpleI P c h

/-! ## Finite plays of linked components -/

namespace Linked2

/-- **The finite plays of the divergence-aware IR of a linked component** are those of
`l.toComp.den (impSem P)`. -/
theorem toStrategy_denD_impSemD (P : Profile) (l : Linked2) :
    (l.toComp.denD (impSemD P)).toStrategy = l.toComp.den (impSem P) :=
  Reference.toStrategy_denD_impSemD P l.toComp

/-- **Finite session adequacy on the divergence-aware IR** (every profile and component choice
profile, under `Linked2.Adequate`, typed calls): `Linked2.sessAdequacy_full` on
`(l.toComp.denD (impSemD P)).toStrategy`. -/
theorem sessAdequacy_fullD (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        Linked2.sessMoves l calls outs ∈ (l.toComp.denD (impSemD P)).toStrategy} := by
  rw [toStrategy_denD_impSemD]
  exact Linked2.sessAdequacy_full P prof l hl impl h₀ calls ht

/-- **The finite injection on the divergence-aware IR** (every profile and component choice
profile): `Linked2.sessEquiv_iff` on the finite plays of `l.toComp.denD (impSemD P)`. -/
theorem sessEquiv_iffD (P : Profile) (prof : ProfileKind) {l l' : Linked2} (hl : l.Adequate)
    (hl' : l'.Adequate) :
    Linked2.RefSessEquiv P prof l l' ↔ Linked2.SameTypes l l' ∧
      pubPlays (l.toComp.denD (impSemD P)).toStrategy =
        pubPlays (l'.toComp.denD (impSemD P)).toStrategy := by
  rw [toStrategy_denD_impSemD, toStrategy_denD_impSemD]
  exact Linked2.sessEquiv_iff P prof hl hl'

/-! ## Divergence and infinite plays -/

/-- `Linked2.toComp` with its two nodes and its exports named. -/
theorem toComp_eq (l : Linked2) :
    l.toComp = .mk [] [l.expNode, l.impNode] l.compExports := rfl

/-- **The divergences of a linked component, by source** (every core semantics, no hypothesis),
stated on `l.toComp` written out (`toComp_eq`): a divergence of `Linked2.linkDiv C l` (the
exporter's environment diverging, routed through the
importer's node; the importer's node diverging; chatter between them), seen through the export
handler and the interface handlers. -/
theorem div_denD_sources (C : DCoreSem ImpModule) (l : Linked2) :
    ((Comp.mk [] [l.expNode, l.impNode] l.compExports).denD C).div =
      {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
        u ∈ Strategy.ofHandler (widenH 0) ∧
          t ∈ Strategy.ofHandler (narrowH l.compExports.length) ∧ ∃ d x, Zip d x v ∧
            d ∈ l.linkDiv C ∧
            x ∈ Strategy.ofHandler
              (exportsH (envAfter 0 [l.expNode, l.impNode]) l.compExports)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.div_denD_sources C l

/-- **A finite play of the divergence-aware IR extending a typed session is a specification
session** (every profile, under `Linked2.Adequate`). -/
theorem sessSpec_of_mem (P : Profile) {l : Linked2} (hl : l.Adequate)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) {r}
    (h : Linked2.sessMoves l calls outs ++ r ∈ (l.toComp.denD (impSemD P)).toStrategy) :
    ∃ u' π' : Silmaril.Wasm.Execution.Core.Store Nat,
      Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' :=
  (Linked2.sessIR_iff P l hl hIe hIi calls outs ht hlen).1
    (toStrategy_denD_impSemD P l ▸ Strategy.of_prefix _ h (List.prefix_append _ _))

/-- **The session prefix of an IR divergence is a specification session** (every profile,
under `Linked2.Adequate`, typed calls). -/
theorem sessSpec_of_div (P : Profile) {l : Linked2} (hl : l.Adequate)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) {r}
    (h : Linked2.sessMoves l calls outs ++ r ∈ (l.toComp.denD (impSemD P)).div) :
    ∃ u' π' : Silmaril.Wasm.Execution.Core.Store Nat,
      Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' :=
  sessSpec_of_mem P hl hIe hIi ht hlen ((l.toComp.denD (impSemD P)).div_mem h)

/-- **The session prefix of an IR divergence is a reference session outcome** (every profile
and component choice profile, under `Linked2.Adequate`, typed calls, every host). -/
theorem sessObs_of_div (P : Profile) (prof : ProfileKind) {l : Linked2} (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length) {r}
    (h : Linked2.sessMoves l calls outs ++ r ∈ (l.toComp.denD (impSemD P)).div) :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls :=
  Linked2.sess_complete P prof l hl impl h₀ calls outs ht hlen
    (toStrategy_denD_impSemD P l ▸
      Strategy.of_prefix _ ((l.toComp.denD (impSemD P)).div_mem h) (List.prefix_append _ _))

/-- **Every typed session prefix of an IR infinite play is a reference session outcome** (every
profile and component choice profile, under `Linked2.Adequate`, every host). -/
theorem sessObs_of_inf (P : Profile) (prof : ProfileKind) {l : Linked2} (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    {J : Set (List (Move l.toComp.imports.sig (sigN l.toComp.exports.length)))}
    (hJ : J ∈ (l.toComp.denD (impSemD P)).inf)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    (h : Linked2.sessMoves l calls outs ∈ J) :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls :=
  Linked2.sess_complete P prof l hl impl h₀ calls outs ht hlen
    (toStrategy_denD_impSemD P l ▸ (l.toComp.denD (impSemD P)).inf_sub hJ h)

/-- **Productive executions are streams of IR plays** (deterministic profiles, every component
choice profile, under `Linked2.Adequate`, every host): a typed stream of calls `a` with outcomes
`out` is a productive execution of the reference machine iff every finite session prefix of it
is a finite play of the divergence-aware IR. -/
theorem refSessProd_iff_plays (o : GrowOracle) (prof : ProfileKind) {l : Linked2}
    (hl : l.Adequate) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      ∀ k, Linked2.sessMoves l (streamTake a k) (streamTake out k) ∈
        (l.toComp.denD (impSemD (profile o))).toStrategy := by
  rw [toStrategy_denD_impSemD]
  exact Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.refSessProd_iff_plays o prof hl
    a out ht impl h₀

end Linked2

end Silmaril.Wasm.Component.Reference
