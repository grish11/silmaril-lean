module

public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionObs.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Abstract.NodeTrap.Thms
public import Silmaril.Wasm.Component.DWiringMulti.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs
public import Silmaril.Wasm.Abstract.NodeDiv.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.Basic
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.Node

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
  `maskH` (`SimpleI.div_denUD_impSemD`);
* **no silent chatter from `implsN`** at a core node wired by `SimpleI.lowerArgs`
  (`div_dcoreNode_impSemD`): every wiring program of `canon lower` calls the environment, so
  `implsN` answers without a call only with a trap (`NodeTrap.trapSilent_implsN`), and the module
  seen through `widenH` propagates traps (`NodeTrap.trapPropagating_sem_widenH`). Hence the core
  node of a simple component diverges exactly at `DivB` states of its module's instance
  (`SimpleI.div_coreNode_impSemD`, with `div_impSemD_sem_of`).

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

**The modules' own divergences** (`Silmaril.Wasm.Abstract.NodeDiv`, every profile):

* `div_impSemD_sem_of`: the divergences of a module with an instance under `impSemD P` are the
  paths of its instance from the instantiation store to a running state `(s, t)` with
  `Linked2.DivB P s t` (host-free divergence), through `importH` and `exportH`: the coercions add
  no chatter (`NodeDiv.div_semOfSD`). For the importer this is #730's `DivB`; for the exporter,
  reached inside an import call of the importer, it is the divergence `DivAt` of `DivA`.
* On the read-back session of an instance (`spullD (instSession Ii P s₀)`):
  `Linked2.div_spullD_iff_divB` (its divergences are paths to a `DivB` state; the round's
  prefix `DivRound.instMoves` after a path to `.idle u` is one, `Linked2.div_spullD_of_divB`)
  and `Linked2.inf_spullD_of_chatter` (the importer's side of `Chatter`, after a path to
  `.idle u`, is the infinite play of a productive stream of the round, `NodeDiv.stream`).

**Proved downstream** (`Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Thms`).

* The divergences: `sessDivs` against the IR divergences, both directions, by source
  (`Linked2.div_denD_iff_profile` at `profile o`; at other profiles given
  `Linked2.Task.ChatterReadBack`).
* The infinite plays: the infinite play `Linked2.sessInfPlay l a out` of a typed stream is an
  infinite play of `l.toComp.denD (impSemD (profile o))` iff `Linked2.RefSessProd`
  (`Linked2.inf_denD_iff_profile`), and no infinite IR play ends inside a round
  (`Linked2.inf_denD_idle`).
* The combined injection (`Linked2.refSessEquivFull_iff_denD`), on the projections of the IR
  (`pubPlays`, `Linked2.IRDivEq`, `Linked2.IRInfEq`), since `l.toComp.denD` and
  `l'.toComp.denD` have different types.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component
open Silmaril.Wasm.Abstract.InstSession (core3SemD)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

open Silmaril.Wasm.Abstract.InstSession (spullD instSession)
open Silmaril.Wasm.Abstract.NodeDiv (stream prependStream)

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

/-- **The own divergences of a module with an instance under `impSemD P`**: a path of its
instance from the instantiation store to a running state that diverges host-free (`DivB`),
through the coercions `importH` and `exportH`, which add no chatter. -/
theorem div_impSemD_sem_of (P : Profile) {m : ImpModule} (h : ∃ I, m.IsInst I) :
    ((impSemD P).sem m).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (importH (m.numInst h)) ∧ ∃ a b, Zip a b v ∧
        (∃ f s t, (m.numInst h).inst.Path P (.idle (m.numInst h).inst.store) a (.running f s t) ∧
          Linked2.DivB P s t) ∧
        b ∈ Strategy.ofHandler (exportH (m.numInst h))} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.div_impSemD_sem_of P h

/-- **No silent chatter from `implsN` at a core node of a simple component** (when its module
has an instance): every wiring program of `SimpleI.lowerArgs` calls the environment, so `implsN`
answers without a call only with a trap, and the module seen through `widenH` propagates traps.
The node diverges exactly where its module does, through `implsN` and `widenH`. -/
theorem div_dcoreNode_impSemD (P : Profile) (e : Nat) {m : ImpModule} (h : ∃ I, m.IsInst I)
    (ims : Iface) :
    (Node.denD (impSemD P) e (.core m (SimpleI.lowerArgs ims))).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsN e (SimpleI.lowerArgs ims) m.imports.length) ∧
        ∃ a b, Zip a b v ∧ a ∈ ((impSemD P).sem m).div ∧
          b ∈ Strategy.ofHandler (widenH m.exports.length)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.div_dcoreNode_impSemD P e h ims

/-- **The divergences of the core node of a simple component are `DivB` states** of its
module's instance (`div_dcoreNode_impSemD` and `div_impSemD_sem_of`): a path of the instance from
its instantiation store to a running state that diverges host-free, seen through `importH`,
`exportH`, `implsN` below and `widenH` above. For the importer of a `Linked2` this is the node
side of `Linked2.DivB`; for the exporter, reached inside a call of the importer, of `DivA`. -/
theorem SimpleI.div_coreNode_impSemD (P : Profile) (e : Nat) (c : SimpleI)
    (h : ∃ I, c.mod.IsInst I) :
    (Node.denD (impSemD P) e c.coreNode).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsN e (SimpleI.lowerArgs c.imports) c.mod.imports.length) ∧
        ∃ a b, Zip a b v ∧ (∃ x y, Zip x y a ∧
          x ∈ Strategy.ofHandler (importH (c.mod.numInst h)) ∧ ∃ a' b', Zip a' b' y ∧
            (∃ f s t, (c.mod.numInst h).inst.Path P (.idle (c.mod.numInst h).inst.store) a'
              (.running f s t) ∧ Linked2.DivB P s t) ∧
            b' ∈ Strategy.ofHandler (exportH (c.mod.numInst h))) ∧
          b ∈ Strategy.ofHandler (widenH c.mod.exports.length)} := by
  rw [SimpleI.coreNode, div_dcoreNode_impSemD P e h, div_impSemD_sem_of P h]
  rfl

/-- **The divergences of an instance's read-back session are `DivB` states**: the paths from the
store `s₀` to a running state `(s, t)` with `Linked2.DivB P s t`. -/
theorem Linked2.div_spullD_iff_divB {P : Profile} {Ii : Silmaril.Wasm.Game.ScalarInstance}
    {s₀ : Silmaril.Wasm.Execution.Core.Store Nat} {p : List (Move Ii.E Ii.F)} :
    p ∈ (spullD (instSession Ii P s₀)).div ↔
      ∃ f s t, Ii.Path P (.idle s₀) p (.running f s t) ∧ Linked2.DivB P s t :=
  Silmaril.Wasm.Abstract.NodeDiv.mem_div_spullD_instSession

/-- **A round of the importer diverging host-free (`DivB`) is a divergence of its session**:
after a path of the instance from `s₀` to `.idle u`, the round's prefix `d.instMoves` to a
`DivB` state. -/
theorem Linked2.div_spullD_of_divB {P : Profile} {l : Linked2}
    {Ii : Silmaril.Wasm.Game.ScalarInstance} {d : Linked2.DivRound l Ii}
    {s₀ u s : Silmaril.Wasm.Execution.Core.Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {p₀ : List (Move Ii.E Ii.F)} (h₀ : Ii.Path P (.idle s₀) p₀ (.idle u))
    (hp : Ii.Path P (.idle u) d.instMoves (.running d.f s t)) (hB : Linked2.DivB P s t) :
    p₀ ++ d.instMoves ∈ (spullD (instSession Ii P s₀)).div :=
  Linked2.div_spullD_iff_divB.2 ⟨d.f, s, t, Silmaril.Wasm.Abstract.NodeDiv.path_append h₀ hp, hB⟩

/-- **The importer's side of chatter is an infinite play of its session**: after a path of the
instance from `s₀` to `.idle u` and the round's prefix `d.instMoves`, the import calls of
`Linked2.Chatter` are a productive stream of the round (`d.cs`, then the calls `c`). -/
theorem Linked2.inf_spullD_of_chatter {P : Profile} {l : Linked2}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {d : Linked2.DivRound l Ii}
    {s₀ u s π : Silmaril.Wasm.Execution.Core.Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {p₀ : List (Move Ii.E Ii.F)} (h₀ : Ii.Path P (.idle s₀) p₀ (.idle u))
    (hp : Ii.Path P (.idle u) d.instMoves (.running d.f s t))
    (hC : Linked2.Chatter P l Ie Ii d.f s t π) :
    ∃ c, (stream p₀ d.f (prependStream d.cs c)).lim ∈ (spullD (instSession Ii P s₀)).inf :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionD.inf_spullD_of_chatter h₀ hp hC

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
