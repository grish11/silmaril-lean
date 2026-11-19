module

public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGDivIR.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.Main

/-!
# The read-back of chatter for an abstract exporter, at deterministic profiles: theorems

**Scope.** The deterministic profiles `profile o`. `LinkedG` with an exporter meeting
`ExpSpec.Adeq`, `ExpSpec.AdeqD`, `ExpSpec.AdeqI` and, for the read-back of chatter,
`ExpSpec.AdeqIC` (infinite plays are served along one run); the importer `Good` at a core
instance `Ii`, the wiring `WireTy`. Chains (`chainExp`, `LinkedN`) built on a deterministic
exporter (`ExpSpec.Det`), in particular on a simple base.

**Proved (public, below).**

1. **Determinism** (`ExpSpec.Det`): a simple exporter (`Simple.expSpec_det`), a linked component
   on a deterministic exporter (`LinkedG.toExp_det`: the importer's Proponent moves are unique
   and the exporter answers its import calls uniquely, so a round is a function of the state and
   the call) and so chains (`chainExp_det`).
2. **Infinite plays are served along one run** (`ExpSpec.AdeqIC`) for every deterministic
   exporter meeting `Adeq` (`ExpSpec.adeqIC_of_det`: the runs of the prefixes given by
   `Adeq.bwd` extend one another), so for a linked component on a deterministic exporter
   (`LinkedG.toExp_adeqIC`).
3. **The read-back of chatter** (`LinkedG.chatterReadBack_profile`): `LinkedG.Task.ChatterReadBack
   (profile o) g Ii` for an exporter meeting `Adeq` and `AdeqIC`. This is #813's
   `Linked2.chatterReadBack_profile` over the exporter interface: the stages of the chatter are
   read back and cohere at `profile o` on the importer's side, and the exporter's served calls
   are read back along one run by `AdeqIC`.
4. **The IR divergence law** (`LinkedG.toExp_adeqD_profile`): `(g.toExp Ii).AdeqD (profile o)`
   without the read-back hypothesis. **Chains** on a deterministic exporter
   (`chainExp_adeqD_profile`, `chainChatter_profile`), `LinkedN.adeqD_profile` for a simple base,
   and **one more importer on a chain** (`LinkedN.div_iff_profile`): IR divergence ↔
   specification divergence (`sessDivs`) ↔ reference divergence (`refDivs`), with no `Task`
   hypothesis.

**Not proved.** Nondeterministic profiles: there the runs of the finite prefixes of an infinite
play need not cohere, and `AdeqIC` is open already for `Simple` (König's lemma over finitely
branching core steps, as for `Linked2.Task.ChatterReadBack`). `AdeqIC` for `LinkedG.toExp` is
derived from determinism, not from the exporter's `AdeqIC` alone. Ill-typed calls are not
covered.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.{Det, Coherent, Chatter,
Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Canon (HostImpl)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Determinism -/

/-- **A deterministic exporter meets `AdeqIC`** (proved, every profile). -/
theorem ExpSpec.adeqIC_of_det {P : Profile} {e : ExpSpec} (he : e.Adeq P) (hd : e.Det P) :
    e.AdeqIC P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.adeqIC_of_det he hd

/-- **A simple exporter is deterministic** at `profile o` (proved). -/
theorem Simple.expSpec_det (o : GrowOracle) (c : Simple) (I : ScalarInstance) :
    (Simple.expSpec c I).Det (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.simple_det o c I

/-- **A linked component on a deterministic exporter is deterministic** at `profile o`
(proved). -/
theorem LinkedG.toExp_det {o : GrowOracle} {g : LinkedG} {Ii : ScalarInstance}
    (hd : g.exp.Det (profile o)) : (g.toExp Ii).Det (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.toExp_det hd

/-- **Chains on a deterministic exporter are deterministic** at `profile o` (proved). -/
theorem chainExp_det (o : GrowOracle) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (hd : e.Det (profile o)) : (chainExp e bs Is).Det (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.chain_det o e bs Is hd

namespace LinkedG

variable {o : GrowOracle} {g : LinkedG} {Ii : ScalarInstance}

/-- **A linked component on a deterministic exporter meets `AdeqIC`** at `profile o`
(proved). -/
theorem toExp_adeqIC (he : g.exp.Adeq (profile o)) (hd : g.exp.Det (profile o))
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    (g.toExp Ii).AdeqIC (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.toExp_adeqIC he hd hi hIi hw

/-! ## The read-back of chatter -/

/-- **Chatter read back at a deterministic profile** (proved): for an exporter meeting `Adeq` and
`AdeqIC`, an IR divergence from chatter after typed rounds on a typed question is a session of
`g.toExp Ii` reaching a state from which the question diverges. -/
theorem chatterReadBack_profile (o : GrowOracle) (he : g.exp.Adeq (profile o))
    (hIC : g.exp.AdeqIC (profile o)) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii)
    (hw : g.WireTy) : Task.ChatterReadBack (profile o) g Ii :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.chatterReadBack_profileG o he hIC hi
    hIi hw

/-- **The IR divergence law of a linked component** at `profile o` (proved). -/
theorem toExp_adeqD_profile (he : g.exp.Adeq (profile o)) (hD : g.exp.AdeqD (profile o))
    (hI : g.exp.AdeqI (profile o)) (hIC : g.exp.AdeqIC (profile o)) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) : (g.toExp Ii).AdeqD (profile o) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.toExp_adeqD_profile he hD hI hIC hi
    hIi hw

end LinkedG

/-! ## Chains -/

/-- **The read-back of chatter for every link of a chain** on a deterministic exporter, at
`profile o` (proved). -/
theorem chainChatter_profile (o : GrowOracle) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.Adeq (profile o)) (hd : e.Det (profile o))
    (h : ChainOk e bs Is) : Task.ChainChatter (profile o) e bs Is :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.chainChatter_profile o e bs Is he hd h

/-- **Chains on a deterministic exporter meet the IR divergence law** at `profile o`
(proved). -/
theorem chainExp_adeqD_profile (o : GrowOracle) {e : ExpSpec} {bs : List (SimpleI × List Nat)}
    {Is : List ScalarInstance} (he : e.Adeq (profile o)) (hD : e.AdeqD (profile o))
    (hI : e.AdeqI (profile o)) (hd : e.Det (profile o)) (h : ChainOk e bs Is) :
    (chainExp e bs Is).AdeqD (profile o) :=
  chainExp_adeqD (profile o) he hD hI h (chainChatter_profile o he hd h)

namespace LinkedN

variable {n : LinkedN} {Ib : ScalarInstance} {Is : List ScalarInstance}

/-- **A chain with a simple base meets the IR divergence law** at `profile o` (proved). -/
theorem adeqD_profile (o : GrowOracle) (hb : n.base.Good) (hIb : n.base.mod.IsInst Ib)
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) : (n.spec Ib Is).AdeqD (profile o) :=
  adeqD (profile o) hb hIb h
    (chainChatter_profile o (Simple.expSpec_adeq _ hb hIb) (Simple.expSpec_det o _ _) h)

/-- **Divergence of one more importer on a chain: IR, specification and reference** (proved, at
`profile o`, every component choice profile, under every host, with no `Task` hypothesis):
`LinkedN.div_iff` with the read-back of chatter discharged. -/
theorem div_iff_profile (o : GrowOracle) (prof : ProfileKind) (hb : n.base.Good)
    (hbi : n.base.Inst) (hIb : n.base.mod.IsInst Ib) (hbS : Linked2.ModSplitOk n.base.mod.mod)
    (hbN : ∀ x ∈ n.base.exports, ∀ m, x.name ≠ tag "t" m)
    (h : ChainOkR (Simple.expSpec n.base Ib) n.links Is) {b : SimpleI} {w : List Nat}
    (hl : (LinkedG.mk (n.spec Ib Is) b w).LinkOk) {Ii : ScalarInstance} (hI : b.mod.IsInst Ii)
    {σ : Type} (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ)
    (calls : List (Fin b.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : SimpleI.TypedCalls b calls) (hlen : calls.length = outs.length)
    (j : Fin b.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) :
    (uMoves ((LinkedG.mk (n.spec Ib Is) b w).sessU calls outs) ++
        [.inr (.ask (j.val, .vals vs))] ∈
          ((linkComp n.toComp b w).denUD (impSemD (profile o))).div ↔
      outs ∈ LinkedG.sessDivs (profile o) ⟨n.spec Ib Is, b, w⟩ Ii calls j vs) ∧
    LinkedG.sessDivs (profile o) ⟨n.spec Ib Is, b, w⟩ Ii calls j vs =
      LinkedG.refDivs (profile o) prof ⟨n.spec Ib Is, b, w⟩ impl h₀ calls j vs :=
  ⟨Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.chain_div_iff_profile o hb hIb
      h.chainOk hl.wireTy hl.good hI ht hlen hvs,
    LinkedN.sessDivs_eq_refDivs (profile o) prof hb hbi hIb hbS hbN h hl impl h₀ calls j vs ht
      hvs hI⟩

end LinkedN

end Silmaril.Wasm.Component.Reference
