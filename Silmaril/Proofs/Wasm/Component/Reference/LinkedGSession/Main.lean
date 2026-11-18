module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.Exp
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.Main
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Filter
public import Silmaril.Wasm.Component.Reference.LinkedGInf.Thms

/-!
# The session object of a linked component, and its injection

* `compSession_eq`: the session object is the session of `g.toExp Ii`, for the instance `Ii`
  of the importer's core module (`ImpModule.IsInst.unique`);
* `sameQ_of_sameTypes`: links with the same export types have the same typed questions;
* `ans_form_of_run`, `sessU_of_typed`: the rounds of a session of `g.toExp Ii` answer results
  or traps (`up_lift_form`), so typed sessions are the plays `g.sessU calls outs` of typed calls;
* `runEq_iff_irFinEq`, `divEq_iff_irDivEq`, `irInfEq_of_runEq`: the typed sessions and
  divergences of `g.toExp Ii` and `g'.toExp Ii'` agree iff the typed IR projections do
  (`ExpSpec.Adeq`, `ExpSpec.AdeqD` of `g.toExp Ii`), and the infinite ones follow
  (`LinkedG.inf_iff_run`, determinism);
* `compSession_inj_full`: through `LinkedG.refSessEquivFull_iff` and `session_eq_iff`;
* `mem_inf_compSession`: the infinite play of a typed stream is one of the session object iff
  it is a productive execution (`mem_inf_session_iff`, `LinkedG.refSessProd_iff_run`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (StoreDet)
open Silmaril.Games.Abstract.StratSession (threadS sroundsPlay)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Canon (HostImpl)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {g g' : LinkedG} {Ii Ii' : SInst}

/-! ## The session object -/

theorem compSession_eq (hI : g.imp.mod.IsInst Ii) :
    LinkedG.compSession P g = threadS (LinkedG.compTripleS P g Ii) (Ii.store, g.exp.init) := by
  unfold LinkedG.compSession
  split
  · rename_i h
    rw [ImpModule.IsInst.unique h.choose_spec hI]
  · rename_i h
    exact absurd ⟨Ii, hI⟩ h

theorem compSession_eq_session (hI : g.imp.mod.IsInst Ii) :
    LinkedG.compSession P g = (g.toExp Ii).session P :=
  compSession_eq hI

/-! ## Typed questions -/

theorem length_toComp_of_sameTypes (h : LinkedG.SameTypes g g') :
    g.toComp.exports.length = g'.toComp.exports.length := by
  have e := congrArg List.length h
  simp only [List.length_map] at e
  rw [LinkedG.exports_length_toComp, LinkedG.exports_length_toComp]
  exact e

theorem ty_of_sameTypes (h : LinkedG.SameTypes g g') {w : Nat}
    (h₁ : w < g.toComp.exports.length) (h₂ : w < g'.toComp.exports.length) :
    g'.toComp.exports[w].ty = g.toComp.exports[w].ty := by
  have h₁' : w < g.imp.exports.length := LinkedG.exports_length_toComp g ▸ h₁
  have h₂' : w < g'.imp.exports.length := LinkedG.exports_length_toComp g' ▸ h₂
  rw [LinkedG.toComp_ty g' h₂ h₂', LinkedG.toComp_ty g h₁ h₁']
  have e := congrArg (fun x => x[w]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem h₁', List.getElem?_eq_getElem h₂',
    Option.map_some, Option.some.injEq] at e
  exact e.symm

theorem typedQ_of_sameTypes (h : LinkedG.SameTypes g g') {q : Nat × Payload}
    (hq : (g.toExp Ii).TypedQ q) : (g'.toExp Ii').TypedQ q := by
  obtain ⟨w, ws, rfl, hck⟩ := hq
  have hw : w.val < g'.toComp.exports.length := length_toComp_of_sameTypes h ▸ w.isLt
  refine ⟨⟨w.val, hw⟩, ws, rfl, ?_⟩
  have hck' : ValTy.checkList g.toComp.exports[w.val].ty.params ws = true := hck
  show ValTy.checkList g'.toComp.exports[w.val].ty.params ws = true
  rw [ty_of_sameTypes h w.isLt hw]
  exact hck'

/-- **Links with the same export types have the same typed questions.** -/
theorem sameQ_of_sameTypes (h : LinkedG.SameTypes g g') : (g.toExp Ii).SameQ (g'.toExp Ii') :=
  fun _ => ⟨typedQ_of_sameTypes h, typedQ_of_sameTypes (Eq.symm h)⟩

theorem typedQ_of_check {j : Fin g.imp.exports.length} {vs : List IVal}
    (hvs : ValTy.checkList g.imp.exports[j].ty.params vs = true) :
    (g.toExp Ii).TypedQ (j.val, .vals vs) := by
  have hj : j.val < g.toComp.exports.length := (LinkedG.exports_length_toComp g).symm ▸ j.isLt
  refine ⟨⟨j.val, hj⟩, vs, rfl, ?_⟩
  show ValTy.checkList g.toComp.exports[j.val].ty.params vs = true
  rw [LinkedG.toComp_ty g hj j.isLt]
  exact hvs

theorem typedQ_imp {q : Nat × Payload} (hq : (g.toExp Ii).TypedQ q) :
    ∃ (j : Fin g.imp.exports.length) (vs : List IVal), q = (j.val, .vals vs) ∧
      ValTy.checkList g.imp.exports[j].ty.params vs = true := by
  obtain ⟨w, ws, rfl, hck⟩ := hq
  have hw : w.val < g.imp.exports.length := LinkedG.exports_length_toComp g ▸ w.isLt
  refine ⟨⟨w.val, hw⟩, ws, rfl, ?_⟩
  have hck' : ValTy.checkList g.toComp.exports[w.val].ty.params ws = true := hck
  rw [LinkedG.toComp_ty g w.isLt hw] at hck'
  exact hck'

/-! ## Typed sessions are sessions of typed calls -/

/-- **The rounds of a session of a linked component answer results or traps.** -/
theorem ans_form_of_run {s s' : (g.toExp Ii).St} {L : List URound}
    (h : (g.toExp Ii).Run P s L s') : ∀ r ∈ L, r.2 = none ∨ ∃ ws, r.2 = some (.vals ws) := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | cons hs _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨d, -, -, -, rfl⟩ := hs
      exact LinkedSessionEquiv.up_lift_form _ _
    · exact ih r hr

/-- **Typed rounds answering results or traps are the rounds of typed calls.** -/
theorem sessU_of_typed : ∀ {L : List URound}, (∀ r ∈ L, (g.toExp Ii).Typed r) →
    (∀ r ∈ L, r.2 = none ∨ ∃ ws, r.2 = some (.vals ws)) →
    ∃ (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      SimpleI.TypedCalls g.imp calls ∧ calls.length = outs.length ∧ L = g.sessU calls outs
  | [], _, _ => ⟨[], [], (fun _ h => nomatch h), rfl, rfl⟩
  | ⟨q, R⟩ :: L, ht, hv => by
    obtain ⟨calls, outs, htc, hlen, rfl⟩ := sessU_of_typed
      (fun r hr => ht r (List.mem_cons_of_mem _ hr)) (fun r hr => hv r (List.mem_cons_of_mem _ hr))
    obtain ⟨j, vs, hq, hvs⟩ := typedQ_imp (ht _ List.mem_cons_self)
    obtain ⟨o, ho⟩ : ∃ o : Option (List IVal), R = o.map .vals := by
      rcases hv _ List.mem_cons_self with h | ⟨ws, h⟩
      · exact ⟨none, h⟩
      · exact ⟨some ws, h⟩
    subst hq ho
    refine ⟨(j, vs) :: calls, o :: outs, ?_, by simp [hlen], rfl⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hvs
    · exact htc c hc

theorem sessU_castCalls (len : g.imp.exports.length = g'.imp.exports.length) :
    ∀ (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      g'.sessU (LinkedG.castCalls len calls) outs = g.sessU calls outs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: cs, _ :: os => congrArg (List.cons _) (sessU_castCalls len cs os)

theorem mem_ir {c : Comp ImpModule} {x : List (Move sigU sigU)} :
    x ∈ (c.denUD (impSemD P)).toStrategy ↔ x ∈ c.denU (impSem P) := by
  rw [toStrategy_denUD_impSemD]

/-! ## The typed IR projections -/

/-- **Equal typed sessions are equal typed finite IR plays.** -/
theorem runEq_iff_irFinEq (h : LinkedG.SameTypes g g') (hA : (g.toExp Ii).Adeq P)
    (hA' : (g'.toExp Ii').Adeq P) :
    (g.toExp Ii).RunEq P (g'.toExp Ii') ↔ LinkedG.IRFinEq P g g' := by
  obtain ⟨len, -⟩ := LinkedGInf.sameTypes_iffG.mp h
  have hq := sameQ_of_sameTypes (Ii := Ii) (Ii' := Ii') h
  constructor
  · intro hR
    refine ⟨len, fun calls outs ht _ => ?_⟩
    have hL := LinkedGInf.typed_sessU (Ii := Ii) ht outs
    rw [mem_ir, mem_ir, sessU_castCalls len]
    constructor
    · intro hm
      obtain ⟨s', hs'⟩ := (hR _ hL).mp (hA.bwd _ hL hm)
      exact hA'.fwd _ _ hs'
    · intro hm
      obtain ⟨s, hs⟩ := (hR _ hL).mpr (hA'.bwd _ (typed_of_sameQ hq hL) hm)
      exact hA.fwd _ _ hs
  · rintro ⟨len, hF⟩ L ht
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨calls, outs, htc, hlen, rfl⟩ := sessU_of_typed ht (ans_form_of_run hs)
      have hm := (hF calls outs htc hlen).mp (mem_ir.mpr (hA.fwd _ _ hs))
      rw [mem_ir, sessU_castCalls len] at hm
      exact hA'.bwd _ (typed_of_sameQ hq ht) hm
    · rintro ⟨s', hs'⟩
      obtain ⟨calls, outs, htc, hlen, rfl⟩ := sessU_of_typed ht (ans_form_of_run hs')
      have hm' : uMoves (g'.sessU (LinkedG.castCalls len calls) outs) ∈
          (g'.toComp.denUD (impSemD P)).toStrategy := by
        rw [mem_ir, sessU_castCalls len]
        exact hA'.fwd _ _ hs'
      exact hA.bwd _ ht (mem_ir.mp ((hF calls outs htc hlen).mpr hm'))

/-- **Equal typed divergences are equal typed IR divergences.** -/
theorem divEq_iff_irDivEq (h : LinkedG.SameTypes g g') (hD : (g.toExp Ii).AdeqD P)
    (hD' : (g'.toExp Ii').AdeqD P) :
    (g.toExp Ii).DivEq P (g'.toExp Ii') ↔ LinkedG.IRDivEq P g g' := by
  obtain ⟨len, -⟩ := LinkedGInf.sameTypes_iffG.mp h
  have hq := sameQ_of_sameTypes (Ii := Ii) (Ii' := Ii') h
  constructor
  · intro hE
    refine ⟨len, fun calls outs j vs ht _ hvs => ?_⟩
    have hL := LinkedGInf.typed_sessU (Ii := Ii) ht outs
    have hj : (g.toExp Ii).TypedQ (j.val, .vals vs) := typedQ_of_check hvs
    rw [sessU_castCalls len]
    exact (hD _ _ hL hj).trans ((hE _ _ hL hj).trans
      (hD' _ _ (typed_of_sameQ hq hL) ((hq _).mp hj)).symm)
  · rintro ⟨len, hF⟩ L q ht hq₁
    obtain ⟨j, vs, rfl, hvs⟩ := typedQ_imp hq₁
    have hq₁' := (hq _).mp hq₁
    rw [← hD _ _ ht hq₁, ← hD' _ _ (typed_of_sameQ hq ht) hq₁']
    constructor
    · intro hm
      obtain ⟨s, hs, -⟩ := (hD _ _ ht hq₁).mp hm
      obtain ⟨calls, outs, htc, hlen, rfl⟩ := sessU_of_typed ht (ans_form_of_run hs)
      have hm' := (hF calls outs j vs htc hlen hvs).mp hm
      rw [sessU_castCalls len] at hm'
      exact hm'
    · intro hm
      obtain ⟨s', hs', -⟩ := (hD' _ _ (typed_of_sameQ hq ht) hq₁').mp hm
      obtain ⟨calls, outs, htc, hlen, rfl⟩ := sessU_of_typed ht (ans_form_of_run hs')
      refine (hF calls outs j vs htc hlen hvs).mpr ?_
      rw [sessU_castCalls len]
      exact hm

theorem run_streamTake {e : ExpSpec} {S : ℕ → e.St} {r : ℕ → URound} (h0 : S 0 = e.init)
    (hS : ∀ k, e.Step P (S k) (r k) (S (k + 1))) : ∀ n, e.Run P e.init (streamTake r n) (S n)
  | 0 => by
    rw [h0]
    simp only [streamTake, List.ofFn_zero]
    exact .nil _
  | n + 1 => by
    rw [LinkedSessionDAdeq.streamTake_snoc]
    exact LinkedG.run_append (run_streamTake h0 hS n) (.cons (hS n) (.nil _))

variable {o : GrowOracle}

/-- **Equal typed sessions give equal infinite IR plays of typed streams** (determinism). -/
theorem irInfEq_of_runEq (hg : g.ProfOk o) (hg' : g'.ProfOk o) (hI : g.imp.mod.IsInst Ii)
    (hI' : g'.imp.mod.IsInst Ii') (h : LinkedG.SameTypes g g')
    (hR : (g.toExp Ii).RunEq (profile o) (g'.toExp Ii')) : LinkedG.IRInfEq (profile o) g g' := by
  obtain ⟨len, hty⟩ := LinkedGInf.sameTypes_iffG.mp h
  refine ⟨len, fun a out ht => ?_⟩
  rw [LinkedG.inf_iff_run hg hI a out ht,
    LinkedG.inf_iff_run hg' hI' _ out (LinkedGInf.typed_castStreamG hty ht)]
  have hr : g'.roundU (LinkedG.castStream len a) out = g.roundU a out := rfl
  rw [hr]
  have htr : ∀ k, (g.toExp Ii).Typed (g.roundU a out k) := LinkedGInf.typed_roundU ht
  constructor
  · rintro ⟨S, h0, hS⟩
    exact LinkedGInf.stream_run_of_det (LinkedG.toExp_det hg'.det) _ _ fun n =>
      (hR _ (typed_streamTake htr n)).mp ⟨S n, run_streamTake h0 hS n⟩
  · rintro ⟨S, h0, hS⟩
    exact LinkedGInf.stream_run_of_det (LinkedG.toExp_det hg.det) _ _ fun n =>
      (hR _ (typed_streamTake htr n)).mpr ⟨S n, run_streamTake h0 hS n⟩

/-! ## The injection -/

/-- **The full injection of linked components into session objects** at `profile o`. -/
theorem compSession_inj_full {prof : ProfileKind} (hg : g.ProfOk o) (hg' : g'.ProfOk o) :
    LinkedG.RefSessEquivFull (profile o) prof g g' ↔
      LinkedG.SameTypes g g' ∧
        LinkedG.compSession (profile o) g = LinkedG.compSession (profile o) g' := by
  obtain ⟨Ii, hI⟩ := hg.link.inst.inst
  obtain ⟨Ii', hI'⟩ := hg'.link.inst.inst
  have hA := LinkedG.toExp_adeq hg.adeq hg.link.good hI hg.link.wireTy
  have hA' := LinkedG.toExp_adeq hg'.adeq hg'.link.good hI' hg'.link.wireTy
  have hD := LinkedG.toExp_adeqD_profile hg.adeq hg.adeqD hg.adeqI
    (ExpSpec.adeqIC_of_det hg.adeq hg.det) hg.link.good hI hg.link.wireTy
  have hD' := LinkedG.toExp_adeqD_profile hg'.adeq hg'.adeqD hg'.adeqI
    (ExpSpec.adeqIC_of_det hg'.adeq hg'.det) hg'.link.good hI' hg'.link.wireTy
  have hd := LinkedG.toExp_det (Ii := Ii) hg.det
  have hd' := LinkedG.toExp_det (Ii := Ii') hg'.det
  rw [LinkedG.refSessEquivFull_iff hg hg', compSession_eq_session hI, compSession_eq_session hI']
  constructor
  · rintro ⟨h, hF, hE, -⟩
    exact ⟨h, (session_eq_iff hd hd' (sameQ_of_sameTypes h)).mpr
      ⟨(runEq_iff_irFinEq h hA hA').mpr hF, (divEq_iff_irDivEq h hD hD').mpr hE⟩⟩
  · rintro ⟨h, he⟩
    obtain ⟨hR, hE⟩ := (session_eq_iff hd hd' (sameQ_of_sameTypes h)).mp he
    exact ⟨h, (runEq_iff_irFinEq h hA hA').mp hR, (divEq_iff_irDivEq h hD hD').mp hE,
      irInfEq_of_runEq hg hg' hI hI' h hR⟩

/-! ## Infinite plays -/

/-- **The infinite plays of typed call streams are the productive executions** at `profile o`. -/
theorem mem_inf_compSession {prof : ProfileKind} (hg : g.ProfOk o)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => (([] : List (Call (sigN 0))), outAns (out k))) ∈
        (LinkedG.compSession (profile o) g).inf ↔
      LinkedG.RefSessProd (profile o) prof g impl h₀ a out := by
  obtain ⟨Ii, hI⟩ := hg.link.inst.inst
  rw [compSession_eq_session hI, LinkedG.refSessProd_iff_run hg hI a out ht impl h₀]
  have e : (fun k => (([] : List (Call (sigN 0))), outAns (out k))) =
      fun k => (([] : List (Call (sigN 0))), ExpSpec.sumAns (g.roundU a out k).2) := by
    funext k
    simp only [LinkedG.roundU]
    cases out k <;> rfl
  rw [e]
  exact mem_inf_session_iff (LinkedG.toExp_det hg.det) (g.roundU a out)
    (LinkedGInf.typed_roundU ht)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession
