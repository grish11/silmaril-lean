module

public import Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Linked

/-!
# Divergences of linked sessions against the divergence-aware IR: theorems

**Scope.** `Linked2`, the IR `l.toComp.denD (impSemD P)` at every profile `P`, under
`Linked2.Adequate` for the read-back; the target is #730's `Linked2.sessDivs`:

  `sessMoves calls outs ++ [ask (topQ j vs)] ∈ (l.toComp.denD (impSemD P)).div ↔
    outs ∈ Linked2.sessDivs P l calls j vs`

for typed calls and a typed pending call. This module proves the part of the left-to-right
direction where the importer diverges (#730's source (i), `Linked2.DivB`).

**What is proved.**

* **The sources, as IR divergences** (`Linked2.div_denD_eq_sources`, every core semantics, no
  hypothesis): the IR divergences are those built through the outer handlers (`Linked2.irDiv`)
  from the exporter's environment diverging (`envDivSrc`), the importer's node diverging
  (`nodeDivSrc`), or chatter between the two (`chatterSrc`); `Linked2.div_denD_sources` with
  the union distributed.
* **No silent chatter at the importer's node** (`Linked2.not_silentChatter_impNode`,
  `Linked2.div_impNode`, every core semantics, under `WireTy`): the node's wiring forwards every
  import call in range (`⟨[], .call w⟩`, `w` an export of the exporter), and the nested importer
  only calls in range (its import mask), so the handler answers no call without calling: the
  node diverges exactly where the nested importer does.
* **The importer's source is (i)** (`Linked2.sessDivsB_of_nodeDiv`, under `Linked2.Adequate`,
  typed calls, typed pending call): an IR divergence from the importer's node after the session
  `sessMoves calls outs` and the pending call `topQ j vs` gives a specification session from the
  instances' stores, then a well-formed round of the importer (`DivRound`) whose import calls so
  far are answered by the exporter (`ExpRunT`) and whose running state diverges host-free
  (`DivB`): `outs ∈ sessDivsB`, hence `outs ∈ sessDivs` (`Linked2.sessDivsB_subset`).

**How.** The read-back of #724 (`LinkedSessionAdeq`) inverts complete rounds; a divergence is a
play at a running position. The proofs (`Silmaril.Proofs.Wasm.Component.Reference.
LinkedSessionDAdeq`) generalise the inversions to plays that end inside a round, complete rounds
`cl` then a pending question after answered lower calls (`Games`: `exists_rplay`, `hc_zip_run`,
`hb_zip_run`, `serve_run`, `serve_wait`, `halves_rplay_inr`), stated on the `Zip` witnesses of
`DivComp.mem_div_comp` (and of `div_ext_sources`, `div_node_inst`). The importer's IR is read
back on its divergence witnesses down to its instance (`Imp.imp_div_readback`, through
`SimpleI.div_denUD_impSemD` and `SimpleI.div_coreNode_impSemD`); the importer's node, the
exporter's environment and the outer handlers on top (`Linked`).

**Not proved here** (the remaining targets towards `Linked2.div_denD_iff`).

* **(ii) `DivA`, left to right**: the source `envDivSrc` (the exporter diverging inside an import
  call of the importer). The game-level inversions at a waiting position are proved
  (`hc_zip_wait`, `hb_zip_wait`, `halves_wplay_inr`, `serve_wait`); what remains is the
  importer's read-back to `.waiting f s' t' e` with the lifted arguments (on plays, not
  divergences: the importer only waits), and the exporter's pending read-back to `DivAt` (its
  node: `implsH 0 []` answers no call, so it has no chatter at `maskH 0`). The latter must read
  the exporter's complete rounds (`ExpRunT`) and its diverging call **along the same run** of its
  instance: the profile need not be deterministic, so `expEnv_specRoundsT` (which reads the
  complete rounds from some run) does not give the store at which `DivAt` holds.
* **(iii) `Chatter`, left to right**: the source `chatterSrc` (`NodeChatter`, `ExtChatter`), from
  the infinite plays of both nodes; the importer's side is `Linked2.inf_spullD_of_chatter`.
* **Right to left**, for each source: building the IR divergence from a `RoundDiv`, the
  converses of these inversions (pending versions of `cplay_comp_ofHandler`,
  `cplay_ofHandler_comp`, `cplay_comp_serve`), with `div_impSemD_sem_of` at the instance.
* Hence `Linked2.div_denD_iff`. Note that its right-hand side is `outs ∈ sessDivs P l calls j vs`
  (the outcomes of the session prefix), not `[] ∈ sessDivs …`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

/-- **The divergences of a linked component, by source** (every core semantics): those of the
exporter's environment, of the importer's node, and of their chatter, each through the outer
handlers. -/
theorem div_denD_eq_sources (C : DCoreSem ImpModule) (l : Linked2) :
    (l.toComp.denD C).div =
      l.irDiv C (l.envDivSrc C) ∪ l.irDiv C (l.nodeDivSrc C) ∪ l.irDiv C (l.chatterSrc C) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.div_denD_eq_sources C l

/-- **No silent chatter at the importer's node** (every core semantics, under `WireTy`): its
wiring forwards every import call of the nested importer. -/
theorem not_silentChatter_impNode (C : DCoreSem ImpModule) {l : Linked2} (hw : l.WireTy)
    {p : List (Move sigU sigU)} :
    ¬ SilentChatter (implsH l.expNode.width (l.wire.map fun w => ⟨[], .call w⟩))
      (l.imp.toComp.denUD C) p :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.not_silentChatter_impNode C hw

/-- **The importer's node diverges exactly where the nested importer does** (every core
semantics, under `WireTy`). -/
theorem div_impNode (C : DCoreSem ImpModule) {l : Linked2} (hw : l.WireTy) :
    (Node.denD C l.expNode.width l.impNode).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsH l.expNode.width (l.wire.map fun w => ⟨[], .call w⟩)) ∧
        v ∈ (l.imp.toComp.denUD C).div} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.div_impNode C hw

/-- **A divergence of the importer's node is (i), `DivB`** (every profile, under
`Linked2.Adequate`, typed calls, typed pending call): after the session `sessMoves calls outs`,
an IR divergence on the call of export `j` on `vs` coming from the importer's node gives a
specification session of `calls` with the outcomes `outs`, followed by a round of the importer
diverging host-free. -/
theorem sessDivsB_of_nodeDiv (P : Profile) {l : Linked2} (hl : l.Adequate)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      l.irDiv (impSemD P) (l.nodeDivSrc (impSemD P))) :
    outs ∈ sessDivsB P l calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.sessDivsB_of_nodeDiv P hl hIe hIi
    ht hlen hck h

/-- The divergences of the importer are divergences of the specification. -/
theorem sessDivsB_subset (P : Profile) (l : Linked2)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : sessDivsB P l calls j vs ⊆ sessDivs P l calls j vs :=
  fun _ ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, hB⟩ =>
    ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, .inl hB⟩

end Linked2

end Silmaril.Wasm.Component.Reference
