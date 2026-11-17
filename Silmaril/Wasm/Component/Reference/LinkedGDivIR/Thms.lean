module

public import Silmaril.Wasm.Component.Reference.LinkedGDivIR.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGDiv.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Main

/-!
# IR divergence of a linked component with an abstract exporter: theorems

**Scope.** Every profile `P`; `LinkedG` with an exporter meeting `ExpSpec.Adeq P` (finite plays),
`ExpSpec.AdeqD P` (divergence) and, for chatter, `ExpSpec.AdeqI P` (infinite sessions are
infinite plays), the importer `Good` at a core instance `Ii`, the wiring `WireTy`; the IR
`g.toComp.denUD (impSemD P)` over `sigU`; typed rounds and a typed pending question for the
read-back. Chains (`chainExp`, `LinkedN`) built on such an exporter (`ChainOk`, `ChainOkR`).

**Proved (public, below).**

1. **The sources** (`LinkedG.div_toComp_sources`, every core semantics): the IR divergences
   over `sigU` are those of the exporter's environment (`envDivSrc`), of the importer's node
   (`nodeDivSrc`) and of chatter between them (`chatterSrc`), through the linked export handler.
2. **The importer diverging host-free (`DivB`), both ways**: an IR divergence from the importer's
   node after typed rounds on a typed pending call is a session of `g.toExp Ii` followed by a
   `RoundDivB` round (`LinkedG.roundDivB_of_nodeDiv`), and conversely
   (`LinkedG.div_of_roundDivB`, no typing hypothesis).
3. **The exporter's served call diverging (`DivA`), both ways**: an IR divergence from the
   exporter's environment is a session followed by a `RoundDivA` round
   (`LinkedG.roundDivA_of_envDiv`), the exporter's served rounds and its diverging call read
   **along one run** of its specification by `AdeqD`; conversely `LinkedG.div_of_roundDivA`
   (by `AdeqD` right to left).
4. **Infinite sessions are infinite plays** (`ExpSpec.AdeqI`): for a simple exporter
   (`Simple.expSpec_adeqI`), for a linked component (`LinkedG.toExp_adeqI`, `Linked2`'s
   `inf_denD_build` with an abstract exporter, over `sigU`, at every profile: the exporter's
   chunks of served calls are re-chunked into single calls along one run without determinism),
   and so for chains (`chainExp_adeqI`).
5. **Chatter, right to left** (`LinkedG.div_of_roundDivC`, from `AdeqI`, every profile): a
   session followed by a round of chatter (`RoundDivC`) is an IR divergence from `chatterSrc`.
   Hence **right to left, every source** (`LinkedG.toExp_div_of_divStep`).
6. **Left to right outside chatter** (`LinkedG.toExp_div_cases`): every IR divergence after
   typed rounds on a typed question is a session reaching a `DivStep` of `g.toExp Ii`, or comes
   from `chatterSrc`.
7. **The IR law, given the read-back of chatter** (`LinkedG.toExp_adeqD_of`):
   `(g.toExp Ii).AdeqD P`, assuming `LinkedG.Task.ChatterReadBack P g Ii`; by induction, chains
   (`chainExp_adeqD`, given `Task.ChainChatter`), and `LinkedN.adeqD` for a simple base.
8. **At a session** (`LinkedG.div_iff_sessDivs`): for an exporter whose `toExp` meets `AdeqD`,
   the IR divergence after the session play of typed `calls` with `outs` on a typed pending call
   is `outs ∈ LinkedG.sessDivs`. **Chains** (`LinkedN.div_iff`): for one more importer on a
   chain with a simple base, IR divergence ↔ specification divergence (`sessDivs`) ↔ reference
   divergence (`refDivs`, `LinkedN.sessDivs_eq_refDivs`), given the read-back of chatter for
   every link.

**Not proved here: the read-back of chatter** (`LinkedG.Task.ChatterReadBack`, the
abstract-exporter form of `Linked2.Task.ChatterReadBack`). It needs the converse of `AdeqI` for
the exporter: an infinite play of the exporter's environment is served along **one** run of its
`Step`s. At the deterministic profiles `profile o` it is proved in `LinkedGChatter`
(`ExpSpec.AdeqIC`, `LinkedG.chatterReadBack_profile`, `LinkedG.toExp_adeqD_profile`,
`LinkedN.div_iff_profile`); at nondeterministic profiles it is open for `Linked2` already
(König's lemma, see `LinkedSessionDAdeq.Thms`). Ill-typed calls and the infinite plays of the
linked IR beyond `AdeqI`'s forward half are not covered.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.{Layers, Back, Build, Inf,
Chatter, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Canon (HostImpl)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace LinkedG

variable {P : Profile} {g : LinkedG} {Ii : ScalarInstance}

/-- **The divergences of a linked component over `sigU`, by source** (proved, every core
semantics). -/
theorem div_toComp_sources (C : DCoreSem ImpModule) (g : LinkedG) :
    (g.toComp.denUD C).div =
      g.irDivU C (g.envDivSrc C) ∪ g.irDivU C (g.nodeDivSrc C) ∪ g.irDivU C (g.chatterSrc C) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.div_toComp_eq_sources C g

/-- **The importer's node, read back** (proved, every profile): after typed rounds `M` and a
typed pending call, an IR divergence from the importer's node is a session of `g.toExp Ii`
followed by a round of the importer diverging host-free. -/
theorem roundDivB_of_nodeDiv (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) {M : List URound} (hM : ∀ r ∈ M, (g.toExp Ii).Typed r)
    {j : Fin g.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList g.imp.exports[j].ty.params vs = true)
    (h : uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈
      g.irDivU (impSemD P) (g.nodeDivSrc (impSemD P))) :
    ∃ s, (g.toExp Ii).Run P (g.toExp Ii).init M s ∧ RoundDivB P g Ii s.1 s.2 j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.roundDivB_of_nodeDiv he hi hIi hw
    (fun r hr => Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.typedG_of (hM r hr)) hck h

/-- **The exporter's environment, read back** (proved, every profile): after typed rounds `M`
and a typed pending call, an IR divergence from the exporter's environment is a session of
`g.toExp Ii` followed by a round whose served call diverges, along one run of the exporter. -/
theorem roundDivA_of_envDiv (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {M : List URound}
    (hM : ∀ r ∈ M, (g.toExp Ii).Typed r) {j : Fin g.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList g.imp.exports[j].ty.params vs = true)
    (h : uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈
      g.irDivU (impSemD P) (g.envDivSrc (impSemD P))) :
    ∃ s, (g.toExp Ii).Run P (g.toExp Ii).init M s ∧ RoundDivA P g Ii s.1 s.2 j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.roundDivA_of_envDiv he hD hi hIi hw
    (fun r hr => Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.typedG_of (hM r hr)) hck h

/-- **Left to right, outside chatter** (proved, every profile). -/
theorem toExp_div_cases (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {L : List URound} {q : sigU.Op}
    (hL : ∀ r ∈ L, (g.toExp Ii).Typed r) (hq : (g.toExp Ii).TypedQ q)
    (h : uMoves L ++ [.inr (.ask q)] ∈ (g.toComp.denUD (impSemD P)).div) :
    (∃ s, (g.toExp Ii).Run P (g.toExp Ii).init L s ∧ (g.toExp Ii).DivStep P s q) ∨
      uMoves L ++ [.inr (.ask q)] ∈ g.irDivU (impSemD P) (g.chatterSrc (impSemD P)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.toExp_div_cases he hD hi hIi hw hL hq h

/-- **A round of the importer diverging host-free is an IR divergence** (proved, every
profile). -/
theorem div_of_roundDivB (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) {M : List URound} {s : (g.toExp Ii).St}
    (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s) {j : Fin g.imp.exports.length}
    {vs : List IVal} (hB : RoundDivB P g Ii s.1 s.2 j vs) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈ (g.toComp.denUD (impSemD P)).div :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.div_of_roundDivB he hi hIi hw hR hB

/-- **A round whose served call diverges is an IR divergence** (proved, every profile). -/
theorem div_of_roundDivA (hD : g.exp.AdeqD P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) {M : List URound} {s : (g.toExp Ii).St}
    (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s) {j : Fin g.imp.exports.length}
    {vs : List IVal} (hA : RoundDivA P g Ii s.1 s.2 j vs) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈ (g.toComp.denUD (impSemD P)).div :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.div_of_roundDivA hD hi hIi hw hR hA

/-- **A round of chatter is an IR divergence** (proved, every profile), from `AdeqI`. -/
theorem div_of_roundDivC (hI : g.exp.AdeqI P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    {M : List URound} {s : (g.toExp Ii).St} (hR : (g.toExp Ii).Run P (g.toExp Ii).init M s)
    {j : Fin g.imp.exports.length} {vs : List IVal} (hC : RoundDivC P g Ii s.1 s.2 j vs) :
    uMoves M ++ [.inr (.ask (j.val, .vals vs))] ∈ (g.toComp.denUD (impSemD P)).div :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.chatter_build hI hi hIi M s j vs hR hC

/-- **Right to left, every source** (proved, every profile): a session of `g.toExp Ii` reaching
a state from which `q` diverges is an IR divergence after the session on `q`. -/
theorem toExp_div_of_divStep (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hI : g.exp.AdeqI P)
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {L : List URound}
    {s : (g.toExp Ii).St} (hs : (g.toExp Ii).Run P (g.toExp Ii).init L s) {q : sigU.Op}
    (h : (g.toExp Ii).DivStep P s q) :
    uMoves L ++ [.inr (.ask q)] ∈ (g.toComp.denUD (impSemD P)).div :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.toExp_div_of_divStep he hD hI hi hIi hw
    hs h

/-- **A linked component meets `AdeqI`** (proved, every profile). -/
theorem toExp_adeqI (he : g.exp.Adeq P) (hI : g.exp.AdeqI P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) : (g.toExp Ii).AdeqI P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.toExp_adeqI he hI hi hIi

/-- **The IR divergence law of a linked component, given the read-back of chatter** (proved,
every profile). -/
theorem toExp_adeqD_of (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hI : g.exp.AdeqI P)
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy)
    (hR : Task.ChatterReadBack P g Ii) : (g.toExp Ii).AdeqD P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.toExp_adeqD_of he hD hI hi hIi hw hR

/-- **The IR law at a session is `sessDivs`** (proved, every profile): for typed calls with
outcomes and a typed pending call. -/
theorem div_iff_sessDivs (hA : (g.toExp Ii).AdeqD P)
    {calls : List (Fin g.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls g.imp calls) (hlen : calls.length = outs.length)
    {j : Fin g.imp.exports.length} {vs : List IVal}
    (hvs : ValTy.checkList g.imp.exports[j].ty.params vs = true) :
    uMoves (g.sessU calls outs) ++ [.inr (.ask (j.val, .vals vs))] ∈
        (g.toComp.denUD (impSemD P)).div ↔
      outs ∈ sessDivs P g Ii calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.div_iff_sessDivs hA ht hlen hvs

end LinkedG

/-- **A simple exporter meets `AdeqI`** (proved, every profile). -/
theorem Simple.expSpec_adeqI (P : Profile) {c : Simple} (hc : c.Good) {I : ScalarInstance}
    (hI : c.mod.IsInst I) : (Simple.expSpec c I).AdeqI P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.simple_adeqI P hc hI

/-- **Chains meet `AdeqI`** (proved, by induction). -/
theorem chainExp_adeqI (P : Profile) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.Adeq P) (hI : e.AdeqI P) (h : ChainOk e bs Is) :
    (chainExp e bs Is).AdeqI P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.chain_adeqI P e bs Is he hI h

/-- **Chains, given the read-back of chatter** (proved, by induction). -/
theorem chainExp_adeqD (P : Profile) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.Adeq P) (hD : e.AdeqD P) (hI : e.AdeqI P)
    (h : ChainOk e bs Is) (hc : Task.ChainChatter P e bs Is) : (chainExp e bs Is).AdeqD P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.chain_adeqD P e bs Is he hD hI h hc

namespace LinkedN

variable {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}

/-- **A chain with a simple base meets the IR divergence law, given the read-back of chatter**
(proved). -/
theorem adeqD (P : Profile) (hb : n.base.Good) (hIb : n.base.mod.IsInst Ib)
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is)
    (hc : Task.ChainChatter P (Simple.expSpec n.base Ib) n.links Is) : (n.spec Ib Is).AdeqD P :=
  chainExp_adeqD P (Simple.expSpec_adeq P hb hIb) (Simple.expSpec_adeqD P hb hIb)
    (Simple.expSpec_adeqI P hb hIb) h hc

/-- **Divergence of one more importer on a chain: IR, specification and reference** (proved,
every profile and component choice profile, under every host, given the read-back of chatter
for every link):
for the chain `n` (simple base under the hypotheses of `Simple.expSpec_refAdeqU`, links meeting
`ChainOkR`) with one more importer `b` meeting `LinkOk`, after typed `calls` with `outs` on a
typed pending call, the IR divergence of `linkComp n.toComp b w` is `LinkedG.sessDivs`, which
is `LinkedG.refDivs`. -/
theorem div_iff (P : Profile) (prof : ProfileKind) (hb : n.base.Good) (hbi : n.base.Inst)
    (hIb : n.base.mod.IsInst Ib) (hbS : Linked2.ModSplitOk n.base.mod.mod)
    (hbN : ∀ x ∈ n.base.exports, ∀ m, x.name ≠ tag "t" m)
    (h : ChainOkR (Simple.expSpec n.base Ib) n.links Is)
    (hc : Task.ChainChatter P (Simple.expSpec n.base Ib) n.links Is) {b : SimpleI}
    {w : List Nat} (hl : (LinkedG.mk (n.spec Ib Is) b w).LinkOk) {Ii : ScalarInstance}
    (hI : b.mod.IsInst Ii) (hcR : LinkedG.Task.ChatterReadBack P ⟨n.spec Ib Is, b, w⟩ Ii)
    {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin b.exports.length × List IVal))
    (outs : List (Option (List IVal))) (ht : SimpleI.TypedCalls b calls)
    (hlen : calls.length = outs.length) (j : Fin b.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) :
    (uMoves ((LinkedG.mk (n.spec Ib Is) b w).sessU calls outs) ++
        [.inr (.ask (j.val, .vals vs))] ∈ ((linkComp n.toComp b w).denUD (impSemD P)).div ↔
      outs ∈ LinkedG.sessDivs P ⟨n.spec Ib Is, b, w⟩ Ii calls j vs) ∧
    LinkedG.sessDivs P ⟨n.spec Ib Is, b, w⟩ Ii calls j vs =
      LinkedG.refDivs P prof ⟨n.spec Ib Is, b, w⟩ impl h₀ calls j vs :=
  ⟨Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.chain_div_iff P hb hIb h.chainOk hc
      hl.wireTy hl.good hI hcR ht hlen hvs,
    LinkedN.sessDivs_eq_refDivs P prof hb hbi hIb hbS hbN h hl impl h₀ calls j vs ht hvs hI⟩

end LinkedN

end Silmaril.Wasm.Component.Reference
