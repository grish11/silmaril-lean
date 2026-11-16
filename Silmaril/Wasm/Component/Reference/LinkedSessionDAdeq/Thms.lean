module

public import Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.EnvDiv
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Coherent
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Chatter

/-!
# Divergences of linked sessions against the divergence-aware IR: theorems

**Scope.** `Linked2`, the IR `l.toComp.denD (impSemD P)` at every profile `P`, under
`Linked2.Adequate` for the read-back; the target is #730's `Linked2.sessDivs`:

  `sessMoves calls outs ++ [ask (topQ j vs)] ∈ (l.toComp.denD (impSemD P)).div ↔
    outs ∈ Linked2.sessDivs P l calls j vs`

for typed calls and a typed pending call. This module proves the parts of the left-to-right
direction where the importer diverges (#730's source (i), `Linked2.DivB`) and where the exporter
diverges inside an import call of the importer (source (ii), `Linked2.DivA`), states the whole
left-to-right direction conditionally on the read-back of chatter (source (iii)), and proves that
read-back, hence the whole left-to-right direction, at the deterministic profiles `profile o`.

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
* **The exporter's source is (ii)** (`Linked2.sessDivsA_of_envDiv`, same hypotheses): an IR
  divergence from the exporter's environment (`envDivSrc`) after the session and the pending call
  gives a specification session from the instances' stores, then a well-formed round of the
  importer whose import calls so far are answered by the exporter, followed by an import call on
  arguments that lift at the import's type, on which the wired export diverges (`DivA`):
  `outs ∈ sessDivsA`, hence `outs ∈ sessDivs` (`Linked2.sessDivsA_subset`). The exporter's
  served rounds and its diverging call are read **along one run** of its instance: the store at
  which `DivAt` holds is the one the exporter's `ExpRunT` reaches (the profile need not be
  deterministic).
* **Left to right, given chatter** (`Linked2.sessDivs_of_div_denD_of`): every IR divergence after
  a typed session on a typed pending call is in `sessDivs`, assuming
  `Linked2.Task.ChatterReadBack` (the third source).
* **The exporter's served rounds along one run, at deterministic profiles**
  (`Linked2.expRunT_functional`, `Linked2.exists_expRunT_stream`): at `profile o` the store an
  `ExpRunT` reaches is unique, so if every finite prefix of a stream of import calls is served from
  `π₀`, one store sequence serves the whole stream (the exporter's half of `Linked2.Chatter`).
  The proof module also reads this back from plays of the exporter's environment
  (`LinkedSessionDAdeq.exp_plays_stream`: typed served rounds after a prefix, any number of them).
* **Chatter, at deterministic profiles** (`Linked2.chatterReadBack_profile`, under
  `Linked2.Adequate`): `Linked2.Task.ChatterReadBack (profile o) l`, hence the unconditional
  left-to-right direction at `profile o` (`Linked2.sessDivs_of_div_denD_profile`).

**How.** The read-back of #724 (`LinkedSessionAdeq`) inverts complete rounds; a divergence is a
play at a running position. The proofs (`Silmaril.Proofs.Wasm.Component.Reference.
LinkedSessionDAdeq`) generalise the inversions to plays that end inside a round, complete rounds
`cl` then a pending question after answered lower calls (`Games`: `exists_rplay`, `hc_zip_run`,
`hb_zip_run`, `serve_run`, `serve_wait`, `halves_rplay_inr`), stated on the `Zip` witnesses of
`DivComp.mem_div_comp` (and of `div_ext_sources`, `div_node_inst`). The importer's IR is read
back on its divergence witnesses down to its instance (`Imp.imp_div_readback`, through
`SimpleI.div_denUD_impSemD` and `SimpleI.div_coreNode_impSemD`); the importer's node, the
exporter's environment and the outer handlers on top (`Linked`).

**How (ii).** The exporter's environment diverges at a pending question (its node's own
divergence: `maskH 0` does not diverge, and the node makes no lower move, so it has no chatter
with `maskH 0`); the importer's node above waits on it (`ZipCompat`). The importer's IR is read
back at its waiting position (`Wait.imp_wait_readback`), and the exporter's IR divergence by
`imp_div_readback` at `SimpleI.ofSimple l.exp`, its complete rounds on the path that reaches the
diverging call (`Exp.exp_div_readback`).

**How (iii), at `profile o`** (`Chatter`). Chatter (`ExtChatter`) is a finite prefix `c₀` above
the exporter's environment, then shared moves exchanged forever; they form one stream, since the
environment's infinite play is a chain. Cutting the stream just after one of the node's calls (it
calls at least every other move) gives finite **stages**: a play of the node layer `extTop` at a
waiting position (`chatter_stage`, from the routing positions `path_route` and
`Split.halves_path`), interacting with a play of the exporter's environment. Each stage is read
back as in (ii) (`stage_readback`, with `Wait.imp_wait_readback`). The stages cohere: the node's
complete rounds are the same and its calls grow (`rplay_ext_inl`); at `profile o` the importer's
core plays are determined by the component answers (`ImpCoherent`: `rounds_eq`, `pend_prefix`,
from `ScalarInstance.Trans.player_unique`, `Trans.functional` and `Path.functional` of the header
`Silmaril.Wasm.Game.Determinism.Thms`, and the functionality of `ImpRel` in the answers), so the
core calls have a limit stream (`exists_limit`), and the exporter serves it along one run
(`exp_plays_stream`).

**Not proved here** (the remaining targets towards `Linked2.div_denD_iff`).

* **(iii) `Chatter`, left to right, at nondeterministic profiles** (`Linked2.Task.ChatterReadBack P l`
  for general `P`). The proof at `profile o` uses determinism twice: the importer's read-backs of
  the stages cohere (its core plays are determined by the component answers), and so do the
  exporter's runs of the prefixes of the served calls (`exists_expRunT_stream`). At a
  nondeterministic profile neither need hold (the environment's infinite play is a trace limit of
  `threadS`, `StratThread.not_coherent`). This is not a counterexample: the trees of the Core step
  prefixes of the two instances are finitely branching (NaN result sets of fixed width, grow
  success or failure, relaxed choices), so by König's lemma they have infinite branches, which
  either serve every call (`Chatter`) or run forever inside one call (`DivA`, `DivB`), all in
  `sessDivs`. The library has neither König's lemma for these runs nor finite branching of
  `InternalP P`. Alternatively, for the importer's side at every profile: the node's infinite play
  read back through `implsH` and the importer's IR (`ext`/`splitH`, `implsN`/`widenH`,
  `importH`/`exportH`, `spullD`) to a productive stream (`mem_inf_spullD_instSession_stream`,
  `instInf_of_calls`).
* **Right to left**, for each source: building the IR divergence from a `RoundDiv`, the
  converses of these inversions (pending versions of `cplay_comp_ofHandler`,
  `cplay_ofHandler_comp`, `cplay_comp_serve`), with `div_impSemD_sem_of` at the instance.
* Hence `Linked2.div_denD_iff`. Note that its right-hand side is `outs ∈ sessDivs P l calls j vs`
  (the outcomes of the session prefix), not `[] ∈ sessDivs …`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

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

/-- **A divergence of the exporter's environment is (ii), `DivA`** (every profile, under
`Linked2.Adequate`, typed calls, typed pending call): after the session `sessMoves calls outs`,
an IR divergence on the call of export `j` on `vs` coming from the exporter's environment gives a
specification session of `calls` with the outcomes `outs`, followed by a round of the importer
calling out on lifted arguments, on which the wired export of the exporter diverges from the
store its run reached. -/
theorem sessDivsA_of_envDiv (P : Profile) {l : Linked2} (hl : l.Adequate)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {calls : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      l.irDiv (impSemD P) (l.envDivSrc (impSemD P))) :
    outs ∈ sessDivsA P l calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.sessDivsA_of_envDiv P hl hIe hIi
    ht hlen hck h

/-- The divergences of the exporter inside an import call are divergences of the
specification. -/
theorem sessDivsA_subset (P : Profile) (l : Linked2)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : sessDivsA P l calls j vs ⊆ sessDivs P l calls j vs :=
  fun _ ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, hA⟩ =>
    ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, hj, hv, hOk, hp, hr, .inr (.inl hA)⟩

/-- **Left to right, given the chatter read-back** (every profile, under `Linked2.Adequate`,
typed calls, typed pending call): an IR divergence after the session `sessMoves calls outs` on
the call of export `j` on `vs` is a diverging session call of the specification, assuming
`Linked2.Task.ChatterReadBack` for the third source. -/
theorem sessDivs_of_div_denD_of (P : Profile) {l : Linked2} (hl : l.Adequate)
    (hC : Task.ChatterReadBack P l) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      (l.toComp.denD (impSemD P)).div) :
    outs ∈ sessDivs P l calls j vs := by
  rw [div_denD_eq_sources] at h
  rcases h with (hA | hB) | hX
  · exact sessDivsA_subset P l calls j vs (sessDivsA_of_envDiv P hl hIe hIi ht hlen hck hA)
  · exact sessDivsB_subset P l calls j vs (sessDivsB_of_nodeDiv P hl hIe hIi ht hlen hck hB)
  · exact hC Ie Ii hIe hIi calls outs ht hlen j vs hck hX

/-- **Chatter, read back at deterministic profiles** (under `Linked2.Adequate`): at `profile o`,
an IR divergence from chatter between the importer's node and the exporter's environment after a
typed session, on a typed pending call, is a round of the importer making infinitely many core
import calls, served by the exporter along one run (`Linked2.Chatter`). -/
theorem chatterReadBack_profile (o : GrowOracle) {l : Linked2} (hl : l.Adequate) :
    Task.ChatterReadBack (profile o) l :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.chatterReadBack_profile o hl

/-- **Left to right at deterministic profiles** (under `Linked2.Adequate`, typed calls, typed
pending call): an IR divergence after the session `sessMoves calls outs` on the call of export
`j` on `vs` is a diverging session call of the specification. -/
theorem sessDivs_of_div_denD_profile (o : GrowOracle) {l : Linked2} (hl : l.Adequate)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (h : sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      (l.toComp.denD (impSemD (profile o))).div) :
    outs ∈ sessDivs (profile o) l calls j vs :=
  sessDivs_of_div_denD_of (profile o) hl (chatterReadBack_profile o hl) hIe hIi ht hlen hck h

/-! ## The exporter's served rounds along one run -/

/-- **The exporter's run is determined** at a deterministic profile: the store reached by serving
the import calls `ds` from `s` is unique. -/
theorem expRunT_functional {o : GrowOracle} {l : Linked2}
    {I : Silmaril.Wasm.Game.ScalarInstance} {s s₁ s₂ : Silmaril.Wasm.Execution.Core.Store Nat}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h₁ : ExpRunT (profile o) l I s ds s₁) (h₂ : ExpRunT (profile o) l I s ds s₂) : s₁ = s₂ :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.expRunT_functional h₁ h₂

/-- **One run for a whole stream of served calls** (deterministic profiles): if every finite
prefix of the stream of import-call lists `ds` is served by the exporter from `π₀`, then one store
sequence threads all of them, as `Linked2.Chatter` requires of the exporter. At a
nondeterministic profile the runs of the prefixes need not extend one another
(`StratThread.not_coherent` for the abstract phenomenon). -/
theorem exists_expRunT_stream {o : GrowOracle} {l : Linked2}
    {I : Silmaril.Wasm.Game.ScalarInstance} {π₀ : Silmaril.Wasm.Execution.Core.Store Nat}
    (ds : ℕ → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))
    (h : ∀ n, ∃ π, ExpRunT (profile o) l I π₀ (streamTake ds n).flatten π) :
    ∃ st : ℕ → Silmaril.Wasm.Execution.Core.Store Nat, st 0 = π₀ ∧
      ∀ k, ExpRunT (profile o) l I (st k) (ds k) (st (k + 1)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.exists_expRunT_stream ds h

end Linked2

end Silmaril.Wasm.Component.Reference
