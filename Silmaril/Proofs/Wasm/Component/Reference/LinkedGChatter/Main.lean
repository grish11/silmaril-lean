module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.Chatter

/-!
# The IR divergence law of linked components and chains, at deterministic profiles

* `toExp_adeqIC`: a linked component on a deterministic exporter meets `AdeqIC`
  (`adeqIC_of_det`, `toExp_det`), so the read-back of chatter recurses along chains;
* `toExp_adeqD_profile`: `LinkedGDivIR.toExp_adeqD_of` with the read-back of chatter
  `chatterReadBack_profileG`;
* `chainChatter_profile`, `chain_adeqD_profile`: chains on a deterministic exporter;
* `chain_div_iff_profile`: `LinkedGDivIR.chain_div_iff` without the read-back hypotheses.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

section Linked

variable {o : GrowOracle} {g : LinkedG} {Ii : SInst}

/-- **A linked component on a deterministic exporter meets `AdeqIC`.** -/
theorem toExp_adeqIC (he : g.exp.Adeq (profile o)) (hd : g.exp.Det (profile o))
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    (g.toExp Ii).AdeqIC (profile o) :=
  adeqIC_of_det (toExp_adeq he hi hIi hw) (toExp_det hd)

/-- **The IR divergence law of a linked component** at `profile o`. -/
theorem toExp_adeqD_profile (he : g.exp.Adeq (profile o)) (hD : g.exp.AdeqD (profile o))
    (hI : g.exp.AdeqI (profile o)) (hIC : g.exp.AdeqIC (profile o)) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) : (g.toExp Ii).AdeqD (profile o) :=
  toExp_adeqD_of he hD hI hi hIi hw (chatterReadBack_profileG o he hIC hi hIi hw)

end Linked

/-- **The read-back of chatter for every link of a chain** on a deterministic exporter. -/
theorem chainChatter_profile (o : GrowOracle) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst), e.Adeq (profile o) →
      e.Det (profile o) → ChainOk e bs Is → Task.ChainChatter (profile o) e bs Is
  | _, [], _, _, _, _ => trivial
  | _, (_, _) :: _, [], _, _, _ => trivial
  | _, (_, _) :: bs, _ :: Is, he, hd, ⟨hb, hIb, hw, h⟩ =>
    ⟨chatterReadBack_profileG o he (adeqIC_of_det he hd) hb hIb hw,
      chainChatter_profile o _ bs Is (toExp_adeq he hb hIb hw) (toExp_det hd) h⟩

/-- **Chains on a deterministic exporter meet the IR divergence law** at `profile o`. -/
theorem chain_adeqD_profile (o : GrowOracle) (e : ExpSpec) (bs : List (SimpleI × List Nat))
    (Is : List SInst) (he : e.Adeq (profile o)) (hD : e.AdeqD (profile o))
    (hI : e.AdeqI (profile o)) (hd : e.Det (profile o)) (h : ChainOk e bs Is) :
    (chainExp e bs Is).AdeqD (profile o) :=
  chain_adeqD (profile o) e bs Is he hD hI h (chainChatter_profile o e bs Is he hd h)

/-- **One more importer on a chain with a simple base**, at `profile o`: the IR law at a
session, without the read-back hypotheses. -/
theorem chain_div_iff_profile (o : GrowOracle) {n : LinkedN} {Ib Ii : SInst}
    {Is : List SInst} (hb : n.base.Good) (hIb : n.base.mod.IsInst Ib)
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is) {b : SimpleI} {w : List Nat}
    (hw : (LinkedG.mk (n.spec Ib Is) b w).WireTy) (hbg : b.Good) (hI : b.mod.IsInst Ii)
    {calls : List (Fin b.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls b calls) (hlen : calls.length = outs.length)
    {j : Fin b.exports.length} {vs : List IVal}
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) :
    uMoves ((LinkedG.mk (n.spec Ib Is) b w).sessU calls outs) ++
        [.inr (.ask (j.val, .vals vs))] ∈
          ((linkComp n.toComp b w).denUD (impSemD (profile o))).div ↔
      outs ∈ LinkedG.sessDivs (profile o) ⟨n.spec Ib Is, b, w⟩ Ii calls j vs := by
  have hs := simple_adeq (profile o) hb hIb
  have hsd := simple_det o n.base Ib
  have he : (n.spec Ib Is).Adeq (profile o) := chain_adeq (profile o) _ _ _ hs h
  have hd : (n.spec Ib Is).Det (profile o) := chain_det o _ n.links Is hsd
  exact chain_div_iff (profile o) hb hIb h (chainChatter_profile o _ _ _ hs hsd h) hw hbg hI
    (chatterReadBack_profileG (g := ⟨n.spec Ib Is, b, w⟩) o he (adeqIC_of_det he hd) hbg hI hw)
    ht hlen hvs

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter
