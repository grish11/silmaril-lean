module

public import Silmaril.Wasm.Component.Reference.LinkedGDiv.Defs
public import Silmaril.Wasm.Component.DWiringMulti.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# IR divergence of a linked component with an abstract exporter: definitions

**Scope.** `LinkedG` (an exporter `ExpSpec` linked with a simple importer), the IR
`g.toComp.denUD C` over `sigU` (`Silmaril.Wasm.Component.DWiring`) at a core semantics `C` (for
the theorems, `impSemD P`). This is the IR side of `LinkedGDiv`: the law `ExpSpec.AdeqD` for
`LinkedG.toExp`.

## The infinite-play law of an exporter (forward half)

`ExpSpec.AdeqI P e`: a stream of calls `r 0, r 1, …` served one after another along **one** run
of `Step`s from the initial state is an infinite play of `e.comp.denUD (impSemD P)` (the limit
of the plays `uMoves` of its finite prefixes). Only this half is stated: its converse (an infinite
play is served along one run) is the read-back that `Linked2` proves at the deterministic
profiles only.

## The two nodes and the sources of divergence

`g.toComp` is `Comp.mk [] [g.expNode, g.impNode] _` (`linkComp`): the exporter's component
instance with no arguments (`LinkedG.expNode`), then the importer's, its import `k` wired to
environment function `wire[k]` (`LinkedG.impNode`). As for `Linked2` (`Linked2.linkDiv`,
`Linked2.irDiv`), its divergences over `sigU` come from three sources, seen through the linked
export handler (`LinkedG.irDivU`):

* `LinkedG.envDivSrc`: the exporter's environment (`LinkedG.expObs`, the exporter's node above
  `maskH 0`) diverges, on its own or inside an import call of the importer;
* `LinkedG.nodeDivSrc`: the importer's node diverges;
* `LinkedG.chatterSrc`: chatter between the importer's node and the exporter's environment.

## Rounds that never answer, by source

`LinkedG.RoundDivB`, `RoundDivA`, `RoundDivC`: `LinkedG.RoundDiv` with the importer diverging
host-free (`Linked2.DivB`), the exporter's served call diverging (`LinkedG.DivA`) or chatter
(`LinkedG.Chatter`) only.

## The read-back of chatter, as a named proposition

The construction of chatter is proved (from `ExpSpec.AdeqI`); its read-back is not, for an
abstract exporter. It is a named proposition (`Task`), and the IR law of `LinkedG.toExp` is
stated conditionally on it:

* `LinkedG.Task.ChatterReadBack P g Ii`: after typed rounds of `g.toExp Ii` and a typed question,
  an IR divergence from `chatterSrc` is a session of `g.toExp Ii` reaching a state from which
  the question diverges (`DivStep`, the linked `RoundDiv`);
* `Task.ChainChatter P e bs Is`: the same, for every link of the chain `chainExp e bs Is`.

`LinkedG.sessU g calls outs`: the rounds of a session of `calls` with outcomes `outs` at the
untyped interface (the rounds of `g.toExp Ii`), for comparing the IR law with
`LinkedG.sessDivs`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The infinite-play law of an exporter (forward half) -/

open Silmaril.Games.Abstract (streamTake) in
/-- **Infinite sessions are infinite plays**: a stream of calls `r` served one after another
along one run `S` of the exporter's steps from its initial state is an infinite play of its IR
component. -/
def ExpSpec.AdeqI (P : Profile) (e : ExpSpec) : Prop :=
  ∀ (r : ℕ → URound) (S : ℕ → e.St), S 0 = e.init →
    (∀ k, e.Step P (S k) (r k) (S (k + 1))) →
    Silmaril.Games.Chain.lim (fun n => uMoves (streamTake r n)) ∈ (e.comp.denUD (impSemD P)).inf

namespace LinkedG

/-! ## The two nodes and the sources of divergence -/

/-- The exporter's node of `LinkedG.toComp`: the exporter's component, with no arguments. -/
def expNode (g : LinkedG) : Node ImpModule := .inst g.exp.comp []

/-- The importer's node of `LinkedG.toComp`: the importer, its import `k` wired to environment
function `wire[k]` (the exporter's export `wire[k]`). -/
def impNode (g : LinkedG) : Node ImpModule :=
  .inst g.imp.toComp (g.wire.map fun w => ⟨[], .call w⟩)

/-- The environment of the exporter's node (above `maskH 0`), as observations. -/
def expObs (C : DCoreSem ImpModule) (g : LinkedG) : DObs sigU :=
  (DObs.of (DStrategy.ofHandler (maskH 0))).ext 0 (Node.denD C 0 g.expNode)

/-- **The exporter diverges**, on its own or inside an import call of the importer. -/
def envDivSrc (C : DCoreSem ImpModule) (g : LinkedG) : Set (List (Move sigU sigU)) :=
  EnvDiv g.expNode.width (expObs C g).div (Node.denD C g.expNode.width g.impNode)

/-- **The importer's node diverges.** -/
def nodeDivSrc (C : DCoreSem ImpModule) (g : LinkedG) : Set (List (Move sigU sigU)) :=
  NodeDiv g.expNode.width (expObs C g).plays (Node.denD C g.expNode.width g.impNode)

/-- **Chatter between the importer's node and the exporter's environment.** -/
def chatterSrc (C : DCoreSem ImpModule) (g : LinkedG) : Set (List (Move sigU sigU)) :=
  NodeChatter g.expNode.width (expObs C g).inf (Node.denD C g.expNode.width g.impNode)

/-- **The IR divergences over `sigU` from environment divergences `S`**, through the linked
export handler. -/
def irDivU (_C : DCoreSem ImpModule) (g : LinkedG) (S : Set (List (Move sigU sigU))) :
    Set (List (Move sigU sigU)) :=
  {p | ∃ d x, Zip d x p ∧ d ∈ S ∧
    x ∈ Strategy.ofHandler (exportsH (envAfter 0 [g.expNode, g.impNode]) g.toComp.exports)}

/-- **The rounds of a session at the untyped interface**: the calls of the importer's exports
with their outcomes, as rounds of `g.toExp Ii` (one `URound` per call). -/
def sessU (g : LinkedG) (calls : List (Fin g.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) : List URound :=
  (calls.zip outs).map fun co => ⟨(co.1.1.val, .vals co.1.2), co.2.map .vals⟩

/-! ## Rounds that never answer, by source -/

/-- **A round of the importer diverging host-free**: `LinkedG.RoundDiv` with `Linked2.DivB`. -/
def RoundDivB (P : Profile) (g : LinkedG) (Ii : ScalarInstance) (u : Store Nat) (π : g.exp.St)
    (j : Fin g.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound g Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : g.exp.St),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRun P g π d.dss.flatten π₁ ∧ Linked2.DivB P s t

/-- **A round of the exporter's served call diverging**: `LinkedG.RoundDiv` with
`LinkedG.DivA`. -/
def RoundDivA (P : Profile) (g : LinkedG) (Ii : ScalarInstance) (u : Store Nat) (π : g.exp.St)
    (j : Fin g.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound g Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : g.exp.St),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRun P g π d.dss.flatten π₁ ∧ DivA P g Ii d.f s t π₁

/-- **A round of chatter**: `LinkedG.RoundDiv` with `LinkedG.Chatter`. -/
def RoundDivC (P : Profile) (g : LinkedG) (Ii : ScalarInstance) (u : Store Nat) (π : g.exp.St)
    (j : Fin g.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound g Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : g.exp.St),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRun P g π d.dss.flatten π₁ ∧ Chatter P g Ii d.f s t π₁

/-! ## The read-back of chatter, as a named proposition -/

/-- **The chatter source, read back** (a named proposition, not proved): after typed rounds `L`
of `g.toExp Ii` and a typed question `q`, an IR divergence coming from chatter between the
importer's node and the exporter's environment is a session of `g.toExp Ii` from its initial
state reaching a state from which `q` diverges. -/
def Task.ChatterReadBack (P : Profile) (g : LinkedG) (Ii : ScalarInstance) : Prop :=
  ∀ (L : List URound) (q : sigU.Op), (∀ r ∈ L, (g.toExp Ii).Typed r) →
    (g.toExp Ii).TypedQ q →
    uMoves L ++ [.inr (.ask q)] ∈ g.irDivU (impSemD P) (g.chatterSrc (impSemD P)) →
    ∃ s, (g.toExp Ii).Run P (g.toExp Ii).init L s ∧ (g.toExp Ii).DivStep P s q

end LinkedG

/-- **The read-back of chatter for every link of a chain** (a named proposition):
`LinkedG.Task.ChatterReadBack` for each link of the chain built on `e`. -/
def Task.ChainChatter (P : Profile) : ExpSpec → List (SimpleI × List Nat) →
    List ScalarInstance → Prop
  | e, (b, w) :: bs, I :: Is =>
    LinkedG.Task.ChatterReadBack P ⟨e, b, w⟩ I ∧
      Task.ChainChatter P (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
  | _, _, _ => True

end Silmaril.Wasm.Component.Reference
