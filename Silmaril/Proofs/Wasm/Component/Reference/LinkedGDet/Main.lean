module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp.Det
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.Det
public import Silmaril.Wasm.Component.ABI.Thms

/-!
# Divergence excludes a step, for simple and linked exporters (proofs)

* `simple_divExcl`: a simple exporter at `profile o`: a returned or trapped call reaches a
  host-free normal form (`ResultAt`), so the lowered activation does not also run host-free
  forever (`LinkedGComp.not_divB_of_reach`).
* `toExp_divExcl`: a linked component at `profile o`, for an exporter meeting `ExpSpec.Det` and
  `ExpSpec.DivExcl`, with `WireTy`: a diverging round and a finished round of the same question
  from the same state agree on their common prefix (Proponent moves are unique, the exporter
  answers uniquely, as in `LinkedGChatter.calls_detG`); where the diverging round stops,
  (i) `DivB` excludes every move (`not_trans_of_divB`), (ii) under `DivA` the finished round calls
  the same export on the same typed arguments from the same exporter state, which `DivExcl` of the
  exporter excludes, (iii) chatter agrees with the finished round's remaining calls one by one,
  but the finished round answers (`chatter_no_end`).
* `chain_divExcl`: chains, by induction.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedG (expRunG_split)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter (impRel_detG)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGComp (not_divB_of_reach not_trans_of_divB)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "RImpRel" => Silmaril.Wasm.Component.Reference.ImpRel

/-! ## A simple exporter -/

/-- **A simple exporter: divergence excludes a step** (`profile o`). -/
theorem simple_divExcl (o : GrowOracle) (c : Simple) (I : SInst) :
    (Simple.expSpec c I).DivExcl (profile o) := by
  rintro s s' q R - ⟨j, vs, rfl, hdv⟩ hst
  obtain ⟨g, hg0, hg⟩ := hdv.run
  cases hst with
  | ret hj hr =>
    obtain ⟨t', cvs, ys, hreach, hres, -, -⟩ := hr.run
    exact not_divB_of_reach ⟨g, hg0, hg⟩ hreach (Silmaril.Wasm.Game.resultAt_no_internal hres)
  | trap hj ht =>
    obtain ⟨t', res, hreach, hres, -⟩ := ht.run
    exact not_divB_of_reach ⟨g, hg0, hg⟩ hreach (Silmaril.Wasm.Game.resultAt_no_internal hres)

/-! ## A linked component -/

variable {o : GrowOracle} {g : LinkedG} {Ii : SInst}

theorem callMoves_single {E F : Sig.{0}} (x : Σ m : E.Op, E.Ar m) :
    (callMoves [x] : List (Move E F)) = [.inl (.ask x.1), .inl (.ans x.1 x.2)] := by
  cases x
  rfl

/-- **Chatter does not end**: chatter from `q` and the exporter state `π` excludes a run of import
calls served from `π` followed by an answer. -/
theorem chatter_no_end (hd : g.exp.Det (profile o)) {f : Ii.F.Op} :
    ∀ {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
      {dss : List (List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))}
      {q z : Ii.HState} {w : Ii.F.Ar f} {π π' : g.exp.St} (Q : ℕ → Ii.HState)
      (c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e)
      (ds : ℕ → List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))
      (st : ℕ → g.exp.St), Q 0 = q → st 0 = π →
      (∀ k, Ii.Path (profile o) (Q k) (callMoves [c k]) (Q (k + 1)) ∧
        RImpRel g.imp Ii (c k) (ds k) ∧ LinkedG.ExpRun (profile o) g (st k) (ds k) (st (k + 1))) →
      Ii.Path (profile o) q (callMoves cs ++ [.inr (.ans f w)]) z →
      List.Forall₂ (RImpRel g.imp Ii) cs dss →
      LinkedG.ExpRun (profile o) g π dss.flatten π' → False
  | [], _, _, _, _, _, _, Q, c, _, _, hQ, _, H, hp, _, _ => by
    have h0 := (H 0).1
    rw [callMoves_single, hQ] at h0
    cases h0 with
    | cons t _ =>
      cases hp with
      | cons t' _ =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t t' (by simp [Move.IsP])
        cases e
  | ⟨m', n'⟩ :: cs, _ :: _, _, _, _, _, _, Q, c, ds, st, hQ, hst, H, hp, .cons hc F, r => by
    rw [List.flatten_cons] at r
    obtain ⟨πa, ra, rb⟩ := expRunG_split _ _ r
    obtain ⟨h0, hc0, hr0⟩ := H 0
    rw [callMoves_single, hQ] at h0
    rw [hst] at hr0
    cases h0 with
    | cons t₁ h₁ =>
      cases h₁ with
      | cons t₂ h₂ =>
        cases h₂
        cases hp with
        | cons t₁' hp₁ =>
          cases hp₁ with
          | cons t₂' hp₂ =>
            have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₁ t₁'
              (by simp [Move.IsP])
            simp only [Sum.inl.injEq, Ev.ask.injEq] at e
            subst e
            obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₁ t₁'
            obtain ⟨hc₁, -, hπ⟩ :=
              impRel_detG (c := c 0) (c' := ⟨(c 0).1, n'⟩) hd rfl hc0 hc hr0 ra
            have hn : (c 0).2 = n' := eq_of_heq (Sigma.ext_iff.mp hc₁).2
            rw [hn] at t₂
            obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₂' t₂
            exact chatter_no_end hd (fun k => Q (k + 1)) (fun k => c (k + 1))
              (fun k => ds (k + 1)) (fun k => st (k + 1)) rfl hπ (fun k => H (k + 1)) hp₂ F rb

/-- **The tail of a diverging round excludes an answer**: from the running export call `f` at
`(s, t)` and the exporter state `π`, a host-free divergence, a diverging served call or chatter
excludes a run of import calls served from `π` followed by an answer. -/
theorem tail_no_end (hd : g.exp.Det (profile o)) (hx : g.exp.DivExcl (profile o))
    (hw : g.WireTy) {f : Ii.F.Op} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {π π' : g.exp.St} {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
    {dss : List (List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))}
    {z : Ii.HState} {w : Ii.F.Ar f}
    (htail : Linked2.DivB (profile o) s t ∨ LinkedG.DivA (profile o) g Ii f s t π ∨
      LinkedG.Chatter (profile o) g Ii f s t π)
    (hp : Ii.Path (profile o) (.running f s t) (callMoves cs ++ [.inr (.ans f w)]) z)
    (hrel : List.Forall₂ (RImpRel g.imp Ii) cs dss)
    (hr : LinkedG.ExpRun (profile o) g π dss.flatten π') : False := by
  rcases htail with hdv | ⟨e, s', t', nm, ft, ws, w', hpa, hi, hl, hwr, hdiv⟩ |
      ⟨Q, c, ds, st, hQ, hst, H⟩
  · cases cs with
    | nil =>
      cases hp with
      | cons t₁ _ => exact not_trans_of_divB hdv t₁
    | cons x cs =>
      obtain ⟨m, n⟩ := x
      cases hp with
      | cons t₁ _ => exact not_trans_of_divB hdv t₁
  · cases hpa with
    | cons ta _ =>
      cases cs with
      | nil =>
        cases hp with
        | cons tb _ =>
          have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique ta tb
            (by simp [Move.IsP])
          cases e
      | cons x cs =>
        obtain ⟨m', n'⟩ := x
        cases hp with
        | cons tb _ =>
          have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique ta tb
            (by simp [Move.IsP])
          simp only [Sum.inl.injEq, Ev.ask.injEq] at e
          subst e
          obtain _ | ⟨hc, -⟩ := hrel
          rw [List.flatten_cons] at hr
          obtain ⟨πa, ra, -⟩ := expRunG_split _ _ hr
          obtain ⟨nm₂, ft₂, A, hi₂, -, hm⟩ := hc
          rw [hi] at hi₂
          cases hi₂
          simp only at hm
          rw [hl] at hm
          obtain ⟨hk, R, rfl, -⟩ := hm
          cases ra with
          | step w'' hw'' hs hr' =>
            obtain rfl : w' = w'' := Fin.ext (Option.some.inj (hwr.symm.trans hw''))
            refine hx ⟨w', ws, rfl, ?_⟩ hdiv hs
            obtain ⟨x, hx₁, hx₂⟩ := hw.ty _ _ hwr
            rw [hi] at hx₂
            simp only [Option.map_some, Option.some.injEq] at hx₂
            obtain ⟨hlt, hxe⟩ := List.getElem?_eq_some_iff.mp hx₁
            show ValTy.checkList g.exp.comp.exports[w'.val].ty.params ws = true
            rw [hxe, ← hx₂]
            exact Silmaril.Wasm.Component.checkList_of_liftArgs hl
  · exact chatter_no_end hd Q c ds st hQ hst H hp hrel hr

/-- **A diverging round's prefix and a finished round agree, so the finished round reaches the
diverging round's tail.** -/
theorem div_no_end (hd : g.exp.Det (profile o)) (hx : g.exp.DivExcl (profile o))
    (hw : g.WireTy) {f : Ii.F.Op} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread} :
    ∀ {cs cs' : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
      {dss dss' : List (List (Σ _ : (sigN g.imp.imports.length).Op, Option Payload))}
      {q z : Ii.HState} {w : Ii.F.Ar f} {π π₁ π' : g.exp.St},
      Ii.Path (profile o) q (callMoves cs) (.running f s t) →
      List.Forall₂ (RImpRel g.imp Ii) cs dss →
      LinkedG.ExpRun (profile o) g π dss.flatten π₁ →
      Ii.Path (profile o) q (callMoves cs' ++ [.inr (.ans f w)]) z →
      List.Forall₂ (RImpRel g.imp Ii) cs' dss' →
      LinkedG.ExpRun (profile o) g π dss'.flatten π' →
      (Linked2.DivB (profile o) s t ∨ LinkedG.DivA (profile o) g Ii f s t π₁ ∨
        LinkedG.Chatter (profile o) g Ii f s t π₁) → False
  | [], _, _, _, _, _, _, _, _, _, hp, .nil, r, hp', hrel', r', htail => by
    cases hp
    cases r
    exact tail_no_end hd hx hw htail hp' hrel' r'
  | ⟨m, n⟩ :: cs, [], _, _, _, _, _, _, _, _, hp, _, _, hp', _, _, _ => by
    exfalso
    cases hp with
    | cons t₁ _ =>
      cases hp' with
      | cons t₁' _ =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₁ t₁'
          (by simp [Move.IsP])
        cases e
  | ⟨m, n⟩ :: cs, ⟨m', n'⟩ :: cs', _, _, _, _, _, _, _, _, hp, .cons hc F, r, hp',
      .cons hc' F', r', htail => by
    rw [List.flatten_cons] at r r'
    obtain ⟨πa, ra, rb⟩ := expRunG_split _ _ r
    obtain ⟨πb, ra', rb'⟩ := expRunG_split _ _ r'
    cases hp with
    | cons t₁ hp₁ =>
      cases hp' with
      | cons t₁' hp₁' =>
        have e := Silmaril.Wasm.Game.ScalarInstance.Trans.player_unique t₁ t₁'
          (by simp [Move.IsP])
        simp only [Sum.inl.injEq, Ev.ask.injEq] at e
        subst e
        obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₁ t₁'
        obtain ⟨hc₁, rfl, rfl⟩ :=
          impRel_detG (c := ⟨m, n⟩) (c' := ⟨m, n'⟩) hd rfl hc hc' ra ra'
        obtain rfl : n = n' := eq_of_heq (Sigma.mk.inj hc₁).2
        cases hp₁ with
        | cons t₂ hp₂ =>
          cases hp₁' with
          | cons t₂' hp₂' =>
            obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₂ t₂'
            exact div_no_end hd hx hw hp₂ F rb hp₂' F' rb' htail

/-- **A linked component: divergence excludes a step** (`profile o`), for an exporter meeting
`ExpSpec.Det` and `ExpSpec.DivExcl`, with `WireTy`. -/
theorem toExp_divExcl (hd : g.exp.Det (profile o)) (hx : g.exp.DivExcl (profile o))
    (hw : g.WireTy) : (g.toExp Ii).DivExcl (profile o) := by
  rintro ⟨u, π⟩ ⟨u', π'⟩ q R - ⟨j, vs, rfl, ⟨j₀, vs₀, f, cs, dss⟩, s, t, π₁, hj, hvs,
    ⟨xs, hck, hf₁, hf₂, hrel⟩, hp, hr, htail⟩ ⟨⟨j', vs', f', cs', w', dss'⟩,
    ⟨xs', hck', hf₁', hf₂', hrel'⟩, hp', hr', hq⟩
  simp only at hj hvs
  subst hj hvs
  obtain ⟨hq₁, -⟩ := Sigma.mk.inj hq
  simp only [Prod.mk.injEq, Payload.vals.injEq] at hq₁
  obtain ⟨hjj, rfl⟩ := hq₁
  obtain rfl : j₀ = j' := Fin.ext hjj
  simp only at hck hf₁ hf₂ hrel hp hr hck' hf₁' hf₂' hrel' hp' hr'
  rw [hck] at hck'
  cases hck'
  obtain rfl : f = f' :=
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.fOp_ext (hf₁.trans hf₁'.symm)
      (hf₂.trans hf₂'.symm)
  simp only [LinkedG.DivRound.instMoves, LinkedG.SessRound.instMoves] at hp hp'
  cases hp with
  | cons t₀ hp₁ =>
    cases hp' with
    | cons t₀' hp₁' =>
      obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Trans.functional t₀ t₀'
      exact div_no_end hd hx hw hp₁ hrel hr hp₁' hrel' hr' htail

/-- **Chains: divergence excludes a step** (`profile o`). -/
theorem chain_divExcl (o : GrowOracle) :
    ∀ (e : ExpSpec) (bs : List (SimpleI × List Nat)) (Is : List SInst),
      e.Det (profile o) → e.DivExcl (profile o) → ChainWire e bs Is →
      (chainExp e bs Is).DivExcl (profile o)
  | _, [], _, _, hx, _ => hx
  | _, (_, _) :: _, [], _, hx, _ => hx
  | e, (b, w) :: bs, I :: Is, hd, hx, h =>
    chain_divExcl o (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
      (Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.toExp_det hd)
      (toExp_divExcl hd hx h.1) h.2

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDet
