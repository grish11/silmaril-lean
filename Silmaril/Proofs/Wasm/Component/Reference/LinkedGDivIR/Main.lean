module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR.Chatter

/-!
# The IR divergence law of a linked component with an abstract exporter

* `typedG_of`, `typedQ_of`: the typed rounds and questions of `g.toExp Ii`;
* `toExp_div_cases`: left to right, every IR divergence after typed rounds on a typed question
  is a session reaching a `DivStep` (`RoundDiv` via `DivB` or `DivA`), or comes from chatter;
* `toExp_div_of_divStep`: right to left, all three sources (chatter by `chatter_build`);
* `toExp_adeqD_of`: `AdeqD` for `g.toExp Ii`, given the read-back of chatter;
* `chain_adeqD`: by induction along a chain;
* `sessDivs_iff_run`, `div_iff_sessDivs`: the IR law at a session (`sessU`) is `sessDivs`;
* `chain_div_iff`: for one more importer on a chain with a simple base, the IR divergences of
  `linkComp n.toComp b w` after a typed session on a typed pending call are `sessDivs`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {g : LinkedG} {Ii : SInst}

theorem typedG_of {r : URound} (h : (g.toExp Ii).Typed r) : TopG g r := by
  obtain ⟨w, ws, hq, hck⟩ := h
  have hw' : w.val < g.imp.exports.length := (LinkedG.exports_length_toComp g) ▸ w.isLt
  refine ⟨⟨w.val, hw'⟩, ws, hq, ?_⟩
  have e : g.toComp.exports[w.val].ty = g.imp.exports[w.val].ty := toComp_ty g w.isLt hw'
  show ValTy.checkList g.imp.exports[w.val].ty.params ws = true
  rw [← e]
  exact hck

theorem typedQ_of {q : sigU.Op} (h : (g.toExp Ii).TypedQ q) :
    ∃ (j : Fin g.imp.exports.length) (vs : List IVal), q = (j.val, .vals vs) ∧
      ValTy.checkList g.imp.exports[j].ty.params vs = true := by
  obtain ⟨j, vs, hq, hck⟩ := typedG_of (g := g) (Ii := Ii) (r := ⟨q, none⟩) h
  exact ⟨j, vs, hq, hck⟩

theorem roundDiv_of_B {u : Store Nat} {π : g.exp.St} {j : Fin g.imp.exports.length}
    {vs : List IVal} (h : LinkedG.RoundDivB P g Ii u π j vs) : LinkedG.RoundDiv P g Ii u π j vs :=
  let ⟨d, s, t, π₁, hj, hv, hOk, hp, hr, hB⟩ := h
  ⟨d, s, t, π₁, hj, hv, hOk, hp, hr, .inl hB⟩

theorem roundDiv_of_A {u : Store Nat} {π : g.exp.St} {j : Fin g.imp.exports.length}
    {vs : List IVal} (h : LinkedG.RoundDivA P g Ii u π j vs) : LinkedG.RoundDiv P g Ii u π j vs :=
  let ⟨d, s, t, π₁, hj, hv, hOk, hp, hr, hA⟩ := h
  ⟨d, s, t, π₁, hj, hv, hOk, hp, hr, .inr (.inl hA)⟩

/-- **Left to right, outside chatter.** -/
theorem toExp_div_cases (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hi : g.imp.Good)
    (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {L : List URound} {q : sigU.Op}
    (hL : ∀ r ∈ L, (g.toExp Ii).Typed r) (hq : (g.toExp Ii).TypedQ q)
    (h : uMoves L ++ [.inr (.ask q)] ∈ (g.toComp.denUD (impSemD P)).div) :
    (∃ s, (g.toExp Ii).Run P (g.toExp Ii).init L s ∧ (g.toExp Ii).DivStep P s q) ∨
      uMoves L ++ [.inr (.ask q)] ∈ g.irDivU (impSemD P) (g.chatterSrc (impSemD P)) := by
  obtain ⟨j, vs, rfl, hck⟩ := typedQ_of hq
  have hM : ∀ m ∈ L, TopG g m := fun m hm => typedG_of (hL m hm)
  rw [div_toComp_eq_sources] at h
  rcases h with (hA | hN) | hC
  · obtain ⟨s, hs, hA'⟩ := roundDivA_of_envDiv he hD hi hIi hw hM hck hA
    exact .inl ⟨s, hs, j, vs, rfl, roundDiv_of_A hA'⟩
  · obtain ⟨s, hs, hB'⟩ := roundDivB_of_nodeDiv he hi hIi hw hM hck hN
    exact .inl ⟨s, hs, j, vs, rfl, roundDiv_of_B hB'⟩
  · exact .inr hC

/-- **Right to left, every source** (`Adeq`, `AdeqD` and `AdeqI` exporter). -/
theorem toExp_div_of_divStep (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hI : g.exp.AdeqI P)
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) {L : List URound}
    {s : (g.toExp Ii).St} (hs : (g.toExp Ii).Run P (g.toExp Ii).init L s) {q : sigU.Op}
    (h : (g.toExp Ii).DivStep P s q) :
    uMoves L ++ [.inr (.ask q)] ∈ (g.toComp.denUD (impSemD P)).div := by
  obtain ⟨j, vs, rfl, d, sB, t, π₁, hj, hv, hOk, hp, hr, hB' | hA' | hC'⟩ := h
  · exact div_of_roundDivB he hi hIi hw hs ⟨d, sB, t, π₁, hj, hv, hOk, hp, hr, hB'⟩
  · exact div_of_roundDivA hD hi hIi hw hs ⟨d, sB, t, π₁, hj, hv, hOk, hp, hr, hA'⟩
  · exact chatter_build hI hi hIi L s j vs hs ⟨d, sB, t, π₁, hj, hv, hOk, hp, hr, hC'⟩

/-- **The IR law of a linked component, given the read-back of chatter.** -/
theorem toExp_adeqD_of (he : g.exp.Adeq P) (hD : g.exp.AdeqD P) (hI : g.exp.AdeqI P)
    (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy)
    (hR : LinkedG.Task.ChatterReadBack P g Ii) : (g.toExp Ii).AdeqD P := by
  intro L q hL hq
  constructor
  · intro h
    rcases toExp_div_cases he hD hi hIi hw hL hq h with h' | hC
    · exact h'
    · exact hR L q hL hq hC
  · rintro ⟨s, hs, h⟩
    exact toExp_div_of_divStep he hD hI hi hIi hw hs h

/-- **Chains**, by induction. -/
theorem chain_adeqD (P : Profile) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst), e.Adeq P →
      e.AdeqD P → e.AdeqI P → ChainOk e bs Is → Task.ChainChatter P e bs Is →
        (chainExp e bs Is).AdeqD P
  | _, [], [], _, hD, _, _, _ => hD
  | _, (_, _) :: _, _ :: Is, he, hD, hI, ⟨hb, hIb, hw, h⟩, ⟨hR, hc⟩ =>
    chain_adeqD P _ _ Is (toExp_adeq he hb hIb hw) (toExp_adeqD_of he hD hI hb hIb hw hR)
      (toExp_adeqI he hI hb hIb) h hc
  | _, [], _ :: _, _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, _, h, _ => h.elim

/-! ## At a session -/

/-- `sessSpec_ofG`, ending at the idle state the importer's path reaches. -/
theorem sessSpec_of_idleG :
    ∀ (ds : List (LinkedG.SessRound g Ii)) (calls : List (Fin g.imp.exports.length × List IVal))
      (outs : List (Option (List IVal))) {u u' : Store Nat} {π π' : g.exp.St},
      ds.map LinkedG.SessRound.toU = g.sessU calls outs →
      calls.length = outs.length → (∀ d ∈ ds, d.Ok) →
      Ii.Path P (.idle u) (ds.flatMap LinkedG.SessRound.instMoves) (.idle u') →
      LinkedG.ExpRun P g π (ds.flatMap fun d => d.dss.flatten) π' →
      g.SessSpec P Ii u π calls outs u' π'
  | [], calls, outs, u, u', π, π', hF, hlen, _, hp, hrun => by
    cases hrun
    cases hp
    have hz : calls.zip outs = [] := List.map_eq_nil_iff.mp hF.symm
    rcases List.zip_eq_nil_iff.mp hz with rfl | rfl
    · have : outs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst this
      exact .nil u π
    · have : calls = [] := List.length_eq_zero_iff.mp hlen
      subst this
      exact .nil u π
  | d :: ds, calls, outs, u, u', π, π', hF, hlen, hOk, hp, hrun => by
    rcases calls with _ | ⟨⟨j, vs⟩, cs⟩
    · cases hF
    rcases outs with _ | ⟨o, os⟩
    · cases hF
    rw [LinkedG.sessU, List.zip_cons_cons, List.map_cons, List.map_cons, List.cons.injEq] at hF
    obtain ⟨hd, hF'⟩ := hF
    have hq : (d.j.val, Payload.vals d.vs) = (j.val, Payload.vals vs) := congrArg Sigma.fst hd
    simp only [Prod.mk.injEq, Payload.vals.injEq] at hq
    obtain ⟨hj, hvs⟩ := hq
    have hans : d.ans = o.map .vals := eq_of_heq (Sigma.mk.inj hd).2
    rw [List.flatMap_cons] at hp hrun
    obtain ⟨q₁, hp₁, hp₂⟩ := path_split_inst hp
    obtain ⟨u₁, rfl⟩ := path_ans_idle hp₁
    obtain ⟨π₁, hr₁, hr₂⟩ := expRunG_split _ _ hrun
    have hS := sessSpec_of_idleG ds cs os hF' (by simpa using hlen)
      (fun d' hd' => hOk d' (List.mem_cons_of_mem _ hd')) hp₂ hr₂
    have hjv : (d.j, d.vs) = (j, vs) := by rw [Fin.ext hj, hvs]
    rw [← hjv]
    exact .round d (hOk d List.mem_cons_self) hp₁ hr₁ hans hS

/-- **`sessDivs` as a session of `g.toExp Ii` reaching a `DivStep`.** -/
theorem sessDivs_iff_run {calls : List (Fin g.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} (hlen : calls.length = outs.length)
    {j : Fin g.imp.exports.length} {vs : List IVal} :
    outs ∈ LinkedG.sessDivs P g Ii calls j vs ↔
      ∃ s, (g.toExp Ii).Run P (g.toExp Ii).init (g.sessU calls outs) s ∧
        (g.toExp Ii).DivStep P s (j.val, .vals vs) := by
  constructor
  · rintro ⟨u, π, hS, hD⟩
    obtain ⟨L, hL, hp, hr, hm⟩ := sessSpec_roundsG hS
    have hR := run_of_rounds_idle L hL hp hr
    rw [hm] at hR
    exact ⟨(u, π), hR, j, vs, rfl, hD⟩
  · rintro ⟨s, hs, j', vs', hq, hD⟩
    obtain ⟨hj, hv⟩ := Prod.mk.inj hq
    obtain rfl : j = j' := Fin.ext hj
    obtain rfl : vs = vs' := Payload.vals.inj hv
    obtain ⟨ds, hOk, hp, hr, hm⟩ := rounds_of_run hs
    exact ⟨s.1, s.2, sessSpec_of_idleG ds calls outs hm hlen hOk hp hr, hD⟩

/-- **The IR law at a session is `sessDivs`.** -/
theorem div_iff_sessDivs (hA : (g.toExp Ii).AdeqD P)
    {calls : List (Fin g.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls g.imp calls) (hlen : calls.length = outs.length)
    {j : Fin g.imp.exports.length} {vs : List IVal}
    (hvs : ValTy.checkList g.imp.exports[j].ty.params vs = true) :
    uMoves (g.sessU calls outs) ++ [.inr (.ask (j.val, .vals vs))] ∈
        (g.toComp.denUD (impSemD P)).div ↔
      outs ∈ LinkedG.sessDivs P g Ii calls j vs := by
  have hj' : j.val < g.toComp.exports.length := (LinkedG.exports_length_toComp g).symm ▸ j.isLt
  have hty : ∀ {w : Nat} (h₁ : w < g.toComp.exports.length) (h₂ : w < g.imp.exports.length),
      g.toComp.exports[w].ty = g.imp.exports[w].ty := fun h₁ h₂ => toComp_ty g h₁ h₂
  have hL : ∀ r ∈ g.sessU calls outs, (g.toExp Ii).Typed r := by
    intro r hr
    obtain ⟨co, hco, rfl⟩ := List.mem_map.mp hr
    have hlt : co.1.1.val < g.toComp.exports.length :=
      (LinkedG.exports_length_toComp g).symm ▸ co.1.1.isLt
    refine ⟨⟨co.1.1.val, hlt⟩, co.1.2, rfl, ?_⟩
    show ValTy.checkList g.toComp.exports[co.1.1.val].ty.params co.1.2 = true
    rw [hty hlt co.1.1.isLt]
    exact ht _ (List.of_mem_zip hco).1
  have hq : (g.toExp Ii).TypedQ (j.val, .vals vs) := by
    refine ⟨⟨j.val, hj'⟩, vs, rfl, ?_⟩
    show ValTy.checkList g.toComp.exports[j.val].ty.params vs = true
    rw [hty hj' j.isLt]
    exact hvs
  rw [sessDivs_iff_run hlen]
  exact hA _ _ hL hq

/-- **One more importer on a chain with a simple base**: the IR law at a session. -/
theorem chain_div_iff (P : Profile) {n : LinkedN} {Ib : SInst} {Is : List SInst}
    (hb : n.base.Good) (hIb : n.base.mod.IsInst Ib)
    (h : ChainOk (Simple.expSpec n.base Ib) n.links Is)
    (hc : Task.ChainChatter P (Simple.expSpec n.base Ib) n.links Is) {b : SimpleI} {w : List Nat}
    (hw : (LinkedG.mk (n.spec Ib Is) b w).WireTy) (hbg : b.Good) (hI : b.mod.IsInst Ii)
    (hcR : LinkedG.Task.ChatterReadBack P ⟨n.spec Ib Is, b, w⟩ Ii)
    {calls : List (Fin b.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls b calls) (hlen : calls.length = outs.length)
    {j : Fin b.exports.length} {vs : List IVal}
    (hvs : ValTy.checkList b.exports[j].ty.params vs = true) :
    uMoves ((LinkedG.mk (n.spec Ib Is) b w).sessU calls outs) ++
        [.inr (.ask (j.val, .vals vs))] ∈ ((linkComp n.toComp b w).denUD (impSemD P)).div ↔
      outs ∈ LinkedG.sessDivs P ⟨n.spec Ib Is, b, w⟩ Ii calls j vs := by
  have he : (n.spec Ib Is).Adeq P := chain_adeq P _ _ _ (simple_adeq P hb hIb) h
  have hI' : (n.spec Ib Is).AdeqI P := chain_adeqI P _ _ _ (simple_adeq P hb hIb)
    (simple_adeqI P hb hIb) h
  have hD : (n.spec Ib Is).AdeqD P := chain_adeqD P _ _ _ (simple_adeq P hb hIb)
    (Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.simple_adeqD P hb hIb)
    (simple_adeqI P hb hIb) h hc
  have hA := toExp_adeqD_of (g := ⟨n.spec Ib Is, b, w⟩) he hD hI' hbg hI hw hcR
  have e : (n.spec Ib Is).comp = n.toComp := chain_comp _ _ _ h
  rw [← e]
  exact div_iff_sessDivs hA ht hlen hvs

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDivIR
