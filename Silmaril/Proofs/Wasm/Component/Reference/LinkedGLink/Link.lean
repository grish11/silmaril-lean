module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink.Basic
public import Silmaril.Games.Abstract.SessionLink.Defs

/-!
# The linked triple is the exporter's triple serving the importer's (proofs)

* **The exporter's triple** `ExpSpec.sessTripleS`: its logs are empty, so it forces no call
  prefix (`satP_sessTripleS`); its rounds on well-typed wired calls are the exporter's runs
  (`rounds_of_expRun`, `expRun_of_rounds`); infinite services (`SessionLink.InfServe`) split
  into a finite run and a tail (`rounds_of_infServe`) and are built from runs
  (`infServe_rounds`, `infServe_of_steps`).
* **Wired calls are typed** (`typedQ_wired`, `good_of_impRel`): under `LinkedG.WireTy`, a
  component import call on lifted arguments is a typed question of the wired export.
* `fin_eq`: the finished behaviours of `LinkedG.compTripleS` are those of `linkS`, the stores
  swapped; `compTripleS_eq_linkS`: the triples are equal.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore mapEnd)
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance Answer)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile}

/-! ## The exporter's triple -/

section Exp

variable {e : ExpSpec}

theorem satP_sessTripleS (s : e.St) (q : Nat × Payload) :
    StratObs.satP (e.sessTripleS P) s q = ∅ := by
  ext ⟨c, m⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro (h | ⟨d, m', h, -⟩ | ⟨d, e', h, n, c', hc⟩ | ⟨ω, h, -⟩)
  · exact h
  · exact h
  · have h1 : d = [] := h.1
    subst h1
    simp at hc
  · exact h

theorem servedLog_nil {s s' : e.St} {rs : List ((Nat × Payload) × List (Call (sigN 0)) ×
    (Payload ⊕ PUnit.{1}))} (h : Rounds (e.sessTripleS P) s rs s') : servedLog rs = [] := by
  induction h with
  | nil => rfl
  | @cons s s₁ s₂ a c b rs h _ ih =>
    have hc : c = [] := h.1
    subst hc
    simpa [servedLog] using ih

theorem infServe_log {s : e.St} {ω : ℕ → Call sigS} {l : ℕ → List (Call (sigN 0))}
    {st : ℕ → e.St} (h : InfServe (e.sessTripleS P) s ω l st) (k : ℕ) : l k = [] :=
  (h.step k).1

theorem logTake_nil {l : ℕ → List (Call (sigN 0))} (hl : ∀ k, l k = []) (n : ℕ) :
    logTake l n = [] := by
  simp [logTake, streamTake, hl]

end Exp

theorem rounds_append {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A B} {s s₁ s₂ : S}
    {rs rs' : List (A × List (Call E) × B)} (h₁ : Rounds t s rs s₁) (h₂ : Rounds t s₁ rs' s₂) :
    Rounds t s (rs ++ rs') s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

section Serve

variable {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A (B ⊕ PUnit.{1})}

/-- The first `n` rounds of an infinite service. -/
theorem rounds_of_infServe {s : S} {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)}
    {st : ℕ → S} (h : InfServe t s ω l st) (n : ℕ) :
    Rounds t s (List.ofFn fun i : Fin n => ((ω i).1, l i, (ω i).2)) (st n) := by
  induction n with
  | zero => rw [List.ofFn_zero, h.zero]; exact .nil s
  | succ n ih =>
    rw [List.ofFn_succ_last]
    exact rounds_append ih (.cons (h.step n) (.nil _))

theorem served_ofFn {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)} (n : ℕ) :
    served (List.ofFn fun i : Fin n => ((ω i).1, l i, (ω i).2)) = streamTake ω n := by
  simp [served, streamTake, List.map_ofFn, Function.comp_def]

theorem streamAppend_cons_zero {α : Type} (x : α) (L : List α) (ω : ℕ → α) :
    Shape.streamAppend (x :: L) ω 0 = x := by
  simp [Shape.streamAppend]

theorem streamAppend_cons_succ {α : Type} (x : α) (L : List α) (ω : ℕ → α) (k : ℕ) :
    Shape.streamAppend (x :: L) ω (k + 1) = Shape.streamAppend L ω k := by
  by_cases h : k < L.length
  · simp [Shape.streamAppend, h]
  · simp [Shape.streamAppend, h]

/-- **Finitely many rounds in front of an infinite service.** -/
theorem infServe_rounds {s s₁ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{1}))}
    (hR : Rounds t s rs s₁) {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)} {st : ℕ → S}
    (h : InfServe t s₁ ω l st) :
    ∃ l' st', InfServe t s (Shape.streamAppend (served rs) ω) l' st' := by
  induction hR with
  | nil s => exact ⟨l, st, by simpa [served, Shape.streamAppend_nil] using h⟩
  | @cons s s₁' s₂ a c bb rs hr _ ih =>
    obtain ⟨l', st', h'⟩ := ih h
    refine ⟨fun i => match i with | 0 => c | i + 1 => l' i,
      fun i => match i with | 0 => s | i + 1 => st' i, ⟨rfl, ?_⟩⟩
    intro k
    cases k with
    | zero =>
      have e0 : Shape.streamAppend (served ((a, c, bb) :: rs)) ω 0 = ⟨a, bb⟩ :=
        streamAppend_cons_zero _ _ _
      show (c, End.ret _ (st' 0)) ∈ t.1 s _
      rw [e0, h'.zero]
      exact hr
    | succ k =>
      have ek : Shape.streamAppend (served ((a, c, bb) :: rs)) ω (k + 1) =
          Shape.streamAppend (served rs) ω k :=
        streamAppend_cons_succ _ _ _ _
      show (l' k, End.ret _ (st' (k + 1))) ∈ t.1 (st' k) _
      rw [ek]
      exact h'.step k

end Serve

/-! ## Wired calls -/

section Wired

variable {g : LinkedG} {Ii : ScalarInstance}

/-- A component import call of the importer is **well wired**: its import has a wire, to an
export at which its payload is a typed question. -/
def Good (g : LinkedG) (z : g.imp.ICall) : Prop :=
  ∃ w : Fin g.exp.comp.exports.length, g.wire[z.1.1.val]? = some w.val ∧
    g.exp.TypedQ (w.val, z.1.2)

theorem getD_of_getElem? {l : List Nat} {k w : Nat} (h : l[k]? = some w) : l.getD k 0 = w := by
  show (l[k]?).getD 0 = w
  rw [h]
  rfl

theorem lt_of_getElem? {α : Type} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) :
    k < l.length := by
  by_contra hk
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

/-- **A call on lifted arguments is typed at the wired export.** -/
theorem typedQ_wired (hw : g.WireTy) {k : Nat} {nm : String} {ft : FuncTy} {xs : List Flat}
    {ws : List IVal} (himp : g.imp.imports[k]? = some (nm, ft))
    (hl : liftArgs ft.params xs = some ws) :
    ∃ w : Fin g.exp.comp.exports.length, g.wire[k]? = some w.val ∧
      g.exp.TypedQ (w.val, .vals ws) := by
  have hk : k < g.wire.length := hw.length ▸ lt_of_getElem? himp
  have hwk : g.wire[k]? = some g.wire[k] := List.getElem?_eq_getElem hk
  obtain ⟨x, hx, hty⟩ := hw.ty k g.wire[k] hwk
  have hwl : g.wire[k] < g.exp.comp.exports.length := lt_of_getElem? hx
  refine ⟨⟨g.wire[k], hwl⟩, hwk, ⟨g.wire[k], hwl⟩, ws, rfl, ?_⟩
  have hx' : g.exp.comp.exports[g.wire[k]] = x := by
    rw [List.getElem?_eq_getElem hwl] at hx
    exact Option.some.inj hx
  rw [himp] at hty
  simp only [Option.map_some, Option.some.injEq] at hty
  show ValTy.checkList (g.exp.comp.exports[g.wire[k]]).ty.params ws = true
  rw [hx', ← hty]
  exact checkList_of_liftArgs hl

theorem good_of_impRel (hw : g.WireTy) {x : Σ e : Ii.E.Op, Ii.E.Ar e} {z : g.imp.ICall}
    (h : ImpRel g.imp Ii x [z]) : Good g z := by
  rcases impRel_cases h with ⟨h, -⟩ | ⟨nm, ft, ws, hk, R, himp, hl, hz, -⟩
  · cases h
  · simp only [List.cons.injEq, and_true] at hz
    subst hz
    exact typedQ_wired hw himp hl

theorem good_flatten (hw : g.WireTy) {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
    {dss : List (List g.imp.ICall)} (h : List.Forall₂ (ImpRel g.imp Ii) cs dss) :
    ∀ z ∈ dss.flatten, Good g z := by
  induction h with
  | nil => simp
  | @cons x ds cs dss hx _ ih =>
    intro z hz
    rw [List.flatten_cons, List.mem_append] at hz
    rcases hz with hz | hz
    · rcases impRel_len hx with rfl | ⟨z', rfl⟩
      · cases hz
      · rw [List.mem_singleton] at hz
        subst hz
        exact good_of_impRel hw hx
    · exact ih z hz

theorem wireCall_of_good {z : g.imp.ICall} {w : Fin g.exp.comp.exports.length}
    (hw : g.wire[z.1.1.val]? = some w.val) :
    g.imp.wireCall g.wire z = ⟨(w.val, z.1.2), ExpSpec.sumAns z.2⟩ := by
  simp [SimpleI.wireCall, hw]

/-- **The exporter's runs on wired calls are rounds of its triple.** -/
theorem rounds_of_expRun {π π₁ : g.exp.St} {ds : List g.imp.ICall}
    (hg : ∀ z ∈ ds, Good g z) (h : LinkedG.ExpRun P g π ds π₁) :
    ∃ rs, Rounds (g.exp.sessTripleS P) π rs π₁ ∧ served rs = g.imp.wireLog g.wire ds := by
  induction h with
  | nil s => exact ⟨[], .nil s, rfl⟩
  | @step s s₁ s' k p R ds w hw hs _ ih =>
    obtain ⟨rs, hR, hsv⟩ := ih (fun z hz => hg z (List.mem_cons_of_mem _ hz))
    obtain ⟨w', hw', hty⟩ := hg ⟨(k, p), R⟩ (by simp)
    have hww : w'.val = w.val := by
      rw [hw] at hw'
      exact (Option.some.inj hw').symm
    refine ⟨((w.val, p), [], ExpSpec.sumAns R) :: rs,
      .cons ⟨rfl, .inr ⟨hww ▸ hty, .inl ⟨R, s₁, hs, rfl⟩⟩⟩ hR, ?_⟩
    simp only [served, List.map_cons, SimpleI.wireLog] at hsv ⊢
    rw [hsv, wireCall_of_good (z := ⟨(k, p), R⟩) hw]

/-- **Rounds of the exporter's triple serving wired calls are runs of the exporter.** -/
theorem expRun_of_rounds {π π₁ : g.exp.St}
    {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1}))}
    (h : Rounds (g.exp.sessTripleS P) π rs π₁) :
    ∀ ds : List g.imp.ICall, (∀ z ∈ ds, Good g z) → served rs = g.imp.wireLog g.wire ds →
      LinkedG.ExpRun P g π ds π₁ := by
  induction h with
  | nil s =>
    intro ds _ hs
    cases ds with
    | nil => exact .nil s
    | cons => simp [served, SimpleI.wireLog] at hs
  | @cons s s₁ s₂ a c bb rs hr _ ih =>
    intro ds hg hs
    cases ds with
    | nil => simp [served, SimpleI.wireLog] at hs
    | cons z ds =>
      simp only [served, SimpleI.wireLog, List.map_cons, List.cons.injEq] at hs
      obtain ⟨h1, h2⟩ := hs
      obtain ⟨w, hw, hty⟩ := hg z (by simp)
      rw [wireCall_of_good hw] at h1
      obtain ⟨⟨k, p⟩, R⟩ := z
      simp only [Sigma.mk.injEq, heq_eq_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨-, hr⟩ := hr
      rcases hr with ⟨hnt, -⟩ | ⟨-, ⟨R', s', hst, he⟩ | ⟨-, he⟩⟩
      · exact (hnt hty).elim
      · simp only [End.ret.injEq] at he
        obtain ⟨hR, rfl⟩ := he
        rw [← sumAns_inj hR] at hst
        exact .step w hw hst (ih ds (fun z hz => hg z (List.mem_cons_of_mem _ hz)) h2)
      · cases he

/-- One wired call answered by the exporter is a round of its triple. -/
theorem round_of_expRun_single {s s' : g.exp.St} {z : g.imp.ICall} (hg : Good g z)
    (h : LinkedG.ExpRun P g s [z] s') :
    ([], End.ret (g.imp.wireCall g.wire z).2 s') ∈
      (g.exp.sessTripleS P).1 s (g.imp.wireCall g.wire z).1 := by
  obtain ⟨rs, hR, hsv⟩ := rounds_of_expRun (fun z' hz' => by
    rw [List.mem_singleton] at hz'; subst hz'; exact hg) h
  cases hR with
  | nil => simp [served, SimpleI.wireLog] at hsv
  | @cons _ s₁ _ a c bb rs hr hR =>
    simp only [served, SimpleI.wireLog, List.map_cons, List.map_nil, List.cons.injEq] at hsv
    obtain ⟨h1, h2⟩ := hsv
    have hc : c = [] := hr.1
    subst hc
    cases rs with
    | cons => simp at h2
    | nil =>
      cases hR
      rw [← h1]
      exact hr

/-- Steps of the exporter along wired calls are an infinite service. -/
theorem infServe_of_steps {st : ℕ → g.exp.St} {y : ℕ → g.imp.ICall} (hg : ∀ k, Good g (y k))
    (h : ∀ k, LinkedG.ExpRun P g (st k) [y k] (st (k + 1))) :
    InfServe (g.exp.sessTripleS P) (st 0) (fun k => g.imp.wireCall g.wire (y k))
      (fun _ => []) st :=
  ⟨rfl, fun k => round_of_expRun_single (hg k) (h k)⟩

/-! ## Typed questions -/

theorem typedQ_toExp_iff {q : Nat × Payload} : (g.toExp Ii).TypedQ q ↔ g.imp.TypedQ q := by
  have hlen : g.toComp.exports.length = g.imp.exports.length := LinkedG.exports_length_toComp g
  have hty : ∀ (i : Nat) (h : i < g.toComp.exports.length),
      g.toComp.exports[i].ty = (g.imp.exports[i]'(hlen ▸ h)).ty := by
    intro i h
    simp [LinkedG.toComp, linkComp]
  constructor
  · rintro ⟨w, ws, rfl, hc⟩
    refine ⟨⟨w.val, lt_of_lt_of_eq w.isLt hlen⟩, ws, rfl, ?_⟩
    show ValTy.checkList (g.imp.exports[w.val]'(lt_of_lt_of_eq w.isLt hlen)).ty.params ws = true
    rw [← hty w.val w.isLt]
    exact hc
  · rintro ⟨j, ws, rfl, hc⟩
    have hj : j.val < g.toComp.exports.length := lt_of_lt_of_eq j.isLt hlen.symm
    refine ⟨⟨j.val, hj⟩, ws, rfl, ?_⟩
    show ValTy.checkList g.toComp.exports[j.val].ty.params ws = true
    rw [hty j.val hj]
    exact hc

theorem typedQ_of_lowered {b : SimpleI} {j : Fin b.exports.length} {vs : List IVal}
    {f : Ii.F.Op} {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)} {dss : List (List b.ICall)}
    (h : b.Lowered Ii j vs f cs dss) : b.TypedQ (j.val, .vals vs) := by
  obtain ⟨xs, hc, -⟩ := h
  refine ⟨j, vs, rfl, ?_⟩
  cases hcl : ValTy.checkList (b.exports[j.val]).ty.params vs with
  | true => rfl
  | false => simp [checkLower, hcl] at hc

end Wired

/-! ## The finished behaviours -/

variable {g : LinkedG} {Ii : ScalarInstance}

/-- **The finished behaviours of the linked component are those of `linkS`**, the stores
swapped. -/
theorem fin_eq (hw : g.WireTy) (u : Store Nat) (π : g.exp.St) (q : Nat × Payload) :
    (LinkedG.compTripleS P g Ii).1 (u, π) q =
      (fun x => (x.1, mapEnd (Equiv.prodComm g.exp.St (Store Nat)) x.2)) ''
        (linkS (g.exp.sessTripleS P) (g.imp.impTripleS P g.wire Ii)).1 (π, u) q := by
  ext ⟨c, e⟩
  constructor
  · rintro ⟨hc, hx⟩
    simp only at hc
    subst hc
    rcases hx with ⟨hnt, rfl⟩ | ⟨ht, hx⟩
    · -- an ill-typed question
      refine ⟨([], .ret (.inr PUnit.unit) (π, u)),
        .inl ⟨[], π, .ret (.inr PUnit.unit) u, .nil π,
          .inl ⟨fun h => hnt (typedQ_toExp_iff.2 h), rfl⟩, rfl⟩, rfl⟩
    rcases hx with ⟨R, ⟨u₁, π₁⟩, ⟨d, hok, hp, hrun, hr⟩, rfl⟩ |
      ⟨⟨j, vs, rfl, d, s, t, π₁, rfl, rfl, hok, hp, hrun, hdiv⟩, rfl⟩
    · -- a returning round
      simp only [LinkedG.SessRound.toU, Sigma.mk.injEq] at hr
      obtain ⟨rfl, hR⟩ := hr
      cases eq_of_heq hR
      obtain ⟨rs, hR, hsv⟩ := rounds_of_expRun (good_flatten hw (lowered_forall₂ hok)) hrun
      refine ⟨(servedLog rs, linkEnd π₁ (.ret (ExpSpec.sumAns d.ans) u₁)),
        .inl ⟨rs, π₁, _, hR, ?_, rfl⟩, ?_⟩
      · rw [hsv]
        exact .inr ⟨d.j, d.vs, d.f, d.cs, d.dss, rfl, hok, rfl, .inl ⟨d.w, u₁, hp, rfl⟩⟩
      · simp [servedLog_nil hR, linkEnd, mapEnd]
    · obtain ⟨rs, hR, hsv⟩ := rounds_of_expRun (good_flatten hw (lowered_forall₂ hok)) hrun
      rcases hdiv with hB | ⟨e', s', t', nm, ft, ws, w, hpe, himp, hlift, hwire, hds⟩ |
        ⟨qs, cc, ds, st, hq0, hst0, hall⟩
      · -- the importer diverges
        refine ⟨(servedLog rs, linkEnd π₁ .div), .inl ⟨rs, π₁, .div, hR, ?_, rfl⟩, ?_⟩
        · rw [hsv]
          exact .inr ⟨d.j, d.vs, d.f, d.cs, d.dss, rfl, hok, rfl, .inr ⟨s, t, hp, hB, rfl⟩⟩
        · simp [servedLog_nil hR, linkEnd, mapEnd]
      · -- the exporter diverges inside a wired call
        obtain ⟨w', hw', hty⟩ := typedQ_wired hw himp hlift
        have hww : w'.val = w.val := by
          rw [hwire] at hw'
          exact (Option.some.inj hw').symm
        refine ⟨(servedLog rs ++ [], .div),
          .inr (.inl ⟨rs, π₁, (w.val, .vals ws), [], hR, .inl ?_, ⟨rfl, .inr ⟨hww ▸ hty,
            .inr ⟨hds, rfl⟩⟩⟩, rfl⟩), ?_⟩
        · rw [hsv]
          refine ⟨d.j, d.vs, d.f, d.cs, d.dss, s, t, e', s', t', nm, ft, ws, rfl, hok, hp, hpe,
            himp, hlift, ?_⟩
          rw [getD_of_getElem? hwire]
        · simp [servedLog_nil hR, mapEnd]
      · -- chatter
        have hr : ∀ k, Ii.Path P (qs k) (callMoves [cc k]) (qs (k + 1)) := fun k => (hall k).1
        have hp' : Ii.Path P (.idle u) (.inr (.ask d.f) :: callMoves d.cs) (qs 0) := by
          rw [hq0]; exact hp
        have hsing : ∀ k, ∃ y, ds k = [y] := by
          intro k
          rcases impRel_cases (hall k).2.1 with ⟨-, htr⟩ | ⟨_, _, _, _, _, -, -, h, -⟩
          · exact (chain_trap_false hp' hr k htr).elim
          · exact ⟨_, h⟩
        choose y hy using hsing
        have hrel : ∀ k, ImpRel g.imp Ii (cc k) [y k] := fun k => hy k ▸ (hall k).2.1
        have hinf₀ := infServe_of_steps (P := P) (st := st) (y := y)
          (fun k => good_of_impRel hw (hrel k)) (fun k => hy k ▸ (hall k).2.2)
        rw [hst0] at hinf₀
        obtain ⟨l', st', hinf⟩ := infServe_rounds hR hinf₀
        rw [hsv] at hinf
        refine ⟨(logTake l' 0, .div), .inr (.inr ⟨_, ⟨d.j, d.vs, d.f, d.cs, d.dss, s, t, qs, cc, y,
          rfl, hok, hp, hq0, fun k => ⟨hr k, hrel k⟩, rfl⟩, l', st', 0, hinf,
          fun k _ => infServe_log hinf k, rfl⟩), ?_⟩
        simp [logTake, streamTake, mapEnd]
  · rintro ⟨x', hx', hx⟩
    rcases hx' with ⟨rs, s₁, e', hR, hc, rfl⟩ | ⟨rs, s₁, a, c', hR, hsat, hsrv, rfl⟩ |
      ⟨ω, hω, l, st, n, hinf, -, rfl⟩
    · rcases hc with ⟨hnt, hc⟩ | ⟨j, vs, f, cs, dss, rfl, hlow, hlog, hend⟩
      · -- an ill-typed question
        simp only [Prod.mk.injEq] at hc
        obtain ⟨hc, rfl⟩ := hc
        have hrs : rs = [] := List.map_eq_nil_iff.1 hc
        subst hrs
        cases hR
        simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨rfl, .inl ⟨fun h => hnt (typedQ_toExp_iff.1 h), rfl⟩⟩
      simp only at hlog hend
      have hrun := expRun_of_rounds hR dss.flatten (good_flatten hw (lowered_forall₂ hlow)) hlog
      have hty : (g.toExp Ii).TypedQ (j.val, .vals vs) :=
        typedQ_toExp_iff.2 (typedQ_of_lowered hlow)
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      refine ⟨servedLog_nil hR, .inr ⟨hty, ?_⟩⟩
      rcases hend with ⟨w, u₁, hp, rfl⟩ | ⟨s, t, hp, hB, rfl⟩
      · -- a returning round
        exact .inl ⟨g.imp.liftAns j w, (u₁, s₁), ⟨⟨j, vs, f, cs, w, dss⟩, hlow, hp, hrun, rfl⟩, rfl⟩
      · -- the importer diverges
        exact .inr ⟨⟨j, vs, rfl, ⟨j, vs, f, cs, dss⟩, s, t, s₁, rfl, rfl, hlow, hp, hrun,
          .inl hB⟩, rfl⟩
    · -- the exporter diverges inside a wired call
      obtain ⟨j, vs, f, cs, dss, s, t, e'', s', t', nm, ft, ws, rfl, hlow, hp, hpe, himp, hlift,
        hxa⟩ := satP_impTripleS_subset _ _ hsat
      simp only [Prod.mk.injEq] at hxa
      obtain ⟨hlog, rfl⟩ := hxa
      obtain ⟨hc0, hsrv⟩ := hsrv
      rcases hsrv with ⟨-, he⟩ | ⟨-, ⟨R, s'', -, he⟩ | ⟨hds, -⟩⟩
      · cases he
      · cases he
      have hrun := expRun_of_rounds hR dss.flatten (good_flatten hw (lowered_forall₂ hlow)) hlog
      obtain ⟨w, hwire, -⟩ := typedQ_wired hw himp hlift
      rw [getD_of_getElem? hwire] at hds
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only at hc0
      refine ⟨by simp [servedLog_nil hR, hc0], .inr ⟨typedQ_toExp_iff.2 (typedQ_of_lowered hlow),
        .inr ⟨⟨j, vs, rfl, ⟨j, vs, f, cs, dss⟩, s, t, s₁, rfl, rfl, hlow, hp, hrun,
          .inr (.inl ⟨e'', s', t', nm, ft, ws, w, hpe, himp, hlift, hwire, hds⟩)⟩, rfl⟩⟩⟩
    · -- chatter
      obtain ⟨j, vs, f, cs, dss, s, t, r, cc, y, rfl, hlow, hp, hr0, hall, rfl⟩ := hω
      have hL := rounds_of_infServe hinf (g.imp.wireLog g.wire dss.flatten).length
      have hsv : served (List.ofFn fun i : Fin (g.imp.wireLog g.wire dss.flatten).length =>
          ((Shape.streamAppend (g.imp.wireLog g.wire dss.flatten)
              (fun k => g.imp.wireCall g.wire (y k)) i).1, l i,
            (Shape.streamAppend (g.imp.wireLog g.wire dss.flatten)
              (fun k => g.imp.wireCall g.wire (y k)) i).2)) =
          g.imp.wireLog g.wire dss.flatten := by
        rw [served_ofFn, streamTake_streamAppend_lt _ _ le_rfl, List.take_length]
      have hrun := expRun_of_rounds hL dss.flatten (good_flatten hw (lowered_forall₂ hlow)) hsv
      have hstep : ∀ k, LinkedG.ExpRun P g (st ((g.imp.wireLog g.wire dss.flatten).length + k))
          [y k] (st ((g.imp.wireLog g.wire dss.flatten).length + k + 1)) := by
        intro k
        have hm : Shape.streamAppend (g.imp.wireLog g.wire dss.flatten)
            (fun k => g.imp.wireCall g.wire (y k))
            ((g.imp.wireLog g.wire dss.flatten).length + k) = g.imp.wireCall g.wire (y k) := by
          rw [Shape.streamAppend_ge (by omega)]
          simp
        have h1 := hinf.step ((g.imp.wireLog g.wire dss.flatten).length + k)
        rw [hm] at h1
        exact expRun_of_rounds (.cons h1 (.nil _)) [y k]
          (fun z hz => by
            rw [List.mem_singleton] at hz; subst hz; exact good_of_impRel hw (hall k).2)
          (by simp [served, SimpleI.wireLog])
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨logTake_nil (infServe_log hinf) n,
        .inr ⟨typedQ_toExp_iff.2 (typedQ_of_lowered hlow),
          .inr ⟨⟨j, vs, rfl, ⟨j, vs, f, cs, dss⟩, s, t, st (g.imp.wireLog g.wire dss.flatten).length,
            rfl, rfl, hlow, hp, hrun,
            .inr (.inr ⟨r, cc, fun k => [y k],
              fun k => st ((g.imp.wireLog g.wire dss.flatten).length + k), hr0, rfl,
              fun k => ⟨(hall k).1, (hall k).2, hstep k⟩⟩)⟩, rfl⟩⟩⟩

/-! ## The triples -/

/-- **The linked triple is the exporter's triple serving the importer's**, the stores
swapped. -/
theorem compTripleS_eq_linkS (hw : g.WireTy) :
    LinkedG.compTripleS P g Ii =
      mapStore (Equiv.prodComm g.exp.St (Store Nat))
        (linkS (g.exp.sessTripleS P) (g.imp.impTripleS P g.wire Ii)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext σ q
    obtain ⟨u, π⟩ := σ
    exact fin_eq hw u π q
  · funext σ q
    obtain ⟨u, π⟩ := σ
    show ∅ = (linkS (g.exp.sessTripleS P) (g.imp.impTripleS P g.wire Ii)).2.1 (π, u) q
    ext x
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨rs, s₁, a, c, -, -, hc, -⟩
    rw [satP_sessTripleS] at hc
    exact hc
  · funext σ q
    obtain ⟨u, π⟩ := σ
    show ∅ = (linkS (g.exp.sessTripleS P) (g.imp.impTripleS P g.wire Ii)).2.2 (π, u) q
    ext ω
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro (⟨rs, s₁, a, ω', -, -, hω', -⟩ | ⟨ω', -, l, st, hinf, hunb, -⟩)
    · exact hω'
    · obtain ⟨k, hk⟩ := hunb 1
      rw [logTake_nil (infServe_log hinf)] at hk
      simp at hk

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGLink
