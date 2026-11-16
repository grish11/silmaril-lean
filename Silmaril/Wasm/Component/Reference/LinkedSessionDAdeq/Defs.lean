module

public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs

/-!
# Divergences of linked sessions against the divergence-aware IR: definitions

**Scope.** `Linked2`, the IR `l.toComp.denD C` (`Silmaril.Wasm.Component.DWiring`) at a core
semantics `C` (for the theorems, `impSemD P`).

* `Linked2.topQ l j vs`: the question of the linked component calling the importer's export `j`
  on `vs` (as in `Linked2.sessMoves`).
* `Linked2.irDiv C l S`: the IR divergences built from the environment divergences `S` through the
  outer handlers (`exportsH`, `widenH 0`, `narrowH`), as in `Linked2.div_denD_sources`, which says
  that the IR divergences are `irDiv C l (linkDiv C l)`.
* The three sources of `Linked2.linkDiv` named: `Linked2.envDivSrc` (the exporter's environment
  diverging, routed through the importer's node), `Linked2.nodeDivSrc` (the importer's node
  diverging) and `Linked2.chatterSrc` (chatter between the two nodes).
* `Linked2.RoundDivB`, `Linked2.sessDivsB`: `Linked2.RoundDiv` and `Linked2.sessDivs` with the
  first source of divergence only, the importer diverging host-free (`Linked2.DivB`).
* `Linked2.RoundDivA`, `Linked2.sessDivsA`: the same with the second source only, the exporter
  diverging inside an import call of the importer (`Linked2.DivA`).
* `Linked2.RoundDivC`, `Linked2.sessDivsC`: the same with the third source only, chatter between
  the importer and the exporter (`Linked2.Chatter`).
* `Linked2.Task.ChatterReadBack`: the read-back of the third source (`chatterSrc`), as a named
  proposition; the full left-to-right direction is stated conditionally on it. It is proved at
  the deterministic profiles `profile o` and open at nondeterministic ones.
* `Linked2.Task.ChatterBuild`: the converse for the third source (a round of chatter is an IR
  divergence), as a named proposition; the full right-to-left direction, hence the iff, is stated
  conditionally on it. It is open.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

/-- The question of the linked component calling the importer's export `j` on `vs`. -/
def topQ (l : Linked2) (j : Fin l.imp.exports.length) (vs : List IVal) :
    (sigN l.toComp.exports.length).Op :=
  (⟨j, by simp [exports_length_toComp]⟩, .vals vs)

/-- **The IR divergences from environment divergences `S`**, through the export handler and the
interface handlers (the set of `Linked2.div_denD_sources`). -/
def irDiv (_C : DCoreSem ImpModule) (l : Linked2) (S : Set (List (Move sigU sigU))) :
    Set (List (Move l.toComp.imports.sig (sigN l.toComp.exports.length))) :=
  {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
    u ∈ Strategy.ofHandler (widenH 0) ∧
      t ∈ Strategy.ofHandler (narrowH l.compExports.length) ∧ ∃ d x, Zip d x v ∧
        d ∈ S ∧ x ∈ Strategy.ofHandler (exportsH (envAfter 0 [l.expNode, l.impNode]) l.compExports)}

/-- The environment of the exporter's node (above `maskH 0`), as observations. -/
def expObs (C : DCoreSem ImpModule) (l : Linked2) : DObs sigU :=
  (DObs.of (DStrategy.ofHandler (maskH 0))).ext 0 (Node.denD C 0 l.expNode)

/-- **The exporter diverges**, on its own or inside an import call of the importer. -/
def envDivSrc (C : DCoreSem ImpModule) (l : Linked2) : Set (List (Move sigU sigU)) :=
  EnvDiv l.expNode.width (expObs C l).div (Node.denD C l.expNode.width l.impNode)

/-- **The importer's node diverges.** -/
def nodeDivSrc (C : DCoreSem ImpModule) (l : Linked2) : Set (List (Move sigU sigU)) :=
  NodeDiv l.expNode.width (expObs C l).plays (Node.denD C l.expNode.width l.impNode)

/-- **Chatter between the importer's node and the exporter's environment.** -/
def chatterSrc (C : DCoreSem ImpModule) (l : Linked2) : Set (List (Move sigU sigU)) :=
  NodeChatter l.expNode.width (expObs C l).inf (Node.denD C l.expNode.width l.impNode)

section Spec

/-- **A round of the importer diverging host-free**: `Linked2.RoundDiv` with `Linked2.DivB`. -/
def RoundDivB (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) (u π : Store Nat)
    (j : Fin l.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound l Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunT P l Ie π d.dss.flatten π₁ ∧ DivB P s t

/-- **The session outcomes after which the call of export `j` on `vs` diverges in the
importer** (`Linked2.sessDivs` with `Linked2.DivB` only). -/
def sessDivsB (P : Profile) (l : Linked2) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | ∃ (Ie Ii : ScalarInstance) (u π : Store Nat), l.exp.mod.IsInst Ie ∧
    l.imp.mod.IsInst Ii ∧ SessSpec P l Ie Ii Ii.store Ie.store calls outs u π ∧
    RoundDivB P l Ie Ii u π j vs}

/-- **A round of the exporter diverging inside an import call of the importer**:
`Linked2.RoundDiv` with `Linked2.DivA`. -/
def RoundDivA (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) (u π : Store Nat)
    (j : Fin l.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound l Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunT P l Ie π d.dss.flatten π₁ ∧ DivA P l Ie Ii d.f s t π₁

/-- **The session outcomes after which the call of export `j` on `vs` diverges in the
exporter, inside an import call of the importer** (`Linked2.sessDivs` with `Linked2.DivA`
only). -/
def sessDivsA (P : Profile) (l : Linked2) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | ∃ (Ie Ii : ScalarInstance) (u π : Store Nat), l.exp.mod.IsInst Ie ∧
    l.imp.mod.IsInst Ii ∧ SessSpec P l Ie Ii Ii.store Ie.store calls outs u π ∧
    RoundDivA P l Ie Ii u π j vs}

/-- **A round of chatter**: `Linked2.RoundDiv` with `Linked2.Chatter`. -/
def RoundDivC (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) (u π : Store Nat)
    (j : Fin l.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound l Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunT P l Ie π d.dss.flatten π₁ ∧ Chatter P l Ie Ii d.f s t π₁

/-- **The session outcomes after which the call of export `j` on `vs` chatters forever**
between the importer and the exporter (`Linked2.sessDivs` with `Linked2.Chatter` only). -/
def sessDivsC (P : Profile) (l : Linked2) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | ∃ (Ie Ii : ScalarInstance) (u π : Store Nat), l.exp.mod.IsInst Ie ∧
    l.imp.mod.IsInst Ii ∧ SessSpec P l Ie Ii Ii.store Ie.store calls outs u π ∧
    RoundDivC P l Ie Ii u π j vs}

/-- **The chatter source, read back** (a named proposition): for typed calls and a typed pending
call, an IR divergence coming from chatter between the importer's node and the exporter's
environment (`chatterSrc`) after the session `sessMoves calls outs` is one of `Linked2.sessDivs`
(via `Linked2.Chatter`). `Linked2.sessDivs_of_div_denD_of` gives the full left-to-right direction
from it. **Proved at the deterministic profiles** `profile o` for adequate components
(`Linked2.chatterReadBack_profile`). **Open at nondeterministic profiles**: there the stages of
the chatter need not be read back along one run of either instance; the expected route is
König's lemma on the finitely branching trees of Core step prefixes (see
`Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Thms`). -/
def Task.ChatterReadBack (P : Profile) (l : Linked2) : Prop :=
  ∀ (Ie Ii : ScalarInstance), l.exp.mod.IsInst Ie → l.imp.mod.IsInst Ii →
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      SimpleI.TypedCalls l.imp calls → calls.length = outs.length →
    ∀ (j : Fin l.imp.exports.length) (vs : List IVal),
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
      sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
        l.irDiv (impSemD P) (l.chatterSrc (impSemD P)) →
      outs ∈ sessDivs P l calls j vs

/-- **Chatter, built** (a named proposition): the right-to-left direction for the third source.
For typed calls and a typed pending call, a specification session of `calls` with the outcomes
`outs` followed by a round of chatter (`Linked2.sessDivsC`: the importer makes infinitely many
core import calls, each answered by the exporter along one run) is an IR divergence after
`sessMoves calls outs` on the pending call. The other two sources are proved
(`Linked2.div_denD_of_sessDivsB`, `Linked2.div_denD_of_sessDivsA`); this one is **open**: it
needs the infinite plays of the importer's node (its IR read back to the instance's productive
stream, `Linked2.inf_spullD_of_chatter`, then through every handler layer) and of the exporter's
environment (`ExtInf`), interleaved as `ExtChatter`. -/
def Task.ChatterBuild (P : Profile) (l : Linked2) : Prop :=
  ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
    SimpleI.TypedCalls l.imp calls → calls.length = outs.length →
  ∀ (j : Fin l.imp.exports.length) (vs : List IVal),
    ValTy.checkList l.imp.exports[j].ty.params vs = true →
    outs ∈ sessDivsC P l calls j vs →
    sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈ (l.toComp.denD (impSemD P)).div

end Spec

end Linked2

end Silmaril.Wasm.Component.Reference
