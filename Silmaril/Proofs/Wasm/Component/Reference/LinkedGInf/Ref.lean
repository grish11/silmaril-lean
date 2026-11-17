module

public import Silmaril.Wasm.Component.Reference.LinkedGInf.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGInst.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChatter.Det
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.ReachL
public import Silmaril.Proofs.Wasm.Component.Reference.SessionObs.Main

/-!
# Productive executions of a linked component with an abstract exporter

* `stream_run_of_det`: for a deterministic exporter, if every finite prefix of a stream of rounds
  is a session from `s₀`, one run serves the whole stream (the runs of the prefixes extend one
  another, `run_functional`);
* `refSessProd_prefixG`: a productive execution gives every finite prefix as a resumable session
  behaviour (`SessionObs.SessExec.prefix`, every profile);
* `sessExec_fwdB`, `refSessProd_of_run`: a stream of rounds of `g.toExp Ii` served along one run
  from its initial state is a productive execution: one linked call at a time from between calls
  (`linkCall_fwdB`, `ReadyB`, `resumeCfg` after a trap), by dependent choice
  (`SessionObs.exists_stream`), from instantiation (`instG_run`, `readyB_init`);
* `run_of_refSessProd`: conversely, for a deterministic `g.toExp Ii`, the prefixes of a
  productive execution of typed calls are specification sessions (`LinkedG.sess_refToSpecUX`),
  so runs of `g.toExp Ii`, which cohere (`stream_run_of_det`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy (refOuts_inj)
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq (streamTake_snoc)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind}

/-! ## Streams of rounds of a deterministic exporter -/

section Stream

variable {e : ExpSpec}

theorem run_nil_eq {s s' : e.St} (h : e.Run P s [] s') : s' = s := by
  cases h
  rfl

theorem run_one {s s' : e.St} {r : URound} (h : e.Run P s [r] s') : e.Step P s r s' := by
  cases h with
  | cons hs hn =>
    cases hn
    exact hs

/-- **One run for a whole stream of rounds** of a deterministic exporter. -/
theorem stream_run_of_det (hd : e.Det P) (r : ℕ → URound) (s₀ : e.St)
    (h : ∀ n, ∃ s, e.Run P s₀ (streamTake r n) s) :
    ∃ S : ℕ → e.St, S 0 = s₀ ∧ ∀ k, e.Step P (S k) (r k) (S (k + 1)) := by
  choose S hS using h
  refine ⟨S, run_nil_eq (hS 0), fun k => ?_⟩
  have h₁ := hS (k + 1)
  rw [streamTake_snoc] at h₁
  obtain ⟨π, ha, hb⟩ := Silmaril.Proofs.Wasm.Component.Reference.LinkedG.run_split _ _ h₁
  obtain rfl := LinkedGChatter.run_functional hd ha (hS k)
  exact run_one hb

end Stream

/-! ## Streams of calls of a linked component -/

section Calls

variable {g : LinkedG}

theorem sessU_streamTake (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal)) (n : ℕ) :
    g.sessU (streamTake a n) (streamTake out n) = streamTake (g.roundU a out) n := by
  simp only [LinkedG.sessU, streamTake, SessionObs.zip_ofFn, List.map_ofFn]
  rfl

theorem typed_streamTake {a : ℕ → Fin g.imp.exports.length × List IVal}
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) (n : ℕ) :
    SimpleI.TypedCalls g.imp (streamTake a n) := by
  intro q hq
  simp only [streamTake, List.mem_ofFn] at hq
  obtain ⟨i, rfl⟩ := hq
  exact ht i

theorem length_streamTake {α β : Type} (a : ℕ → α) (b : ℕ → β) (n : ℕ) :
    (streamTake a n).length = (streamTake b n).length := by
  simp [streamTake]

/-- A specification session from the initial states is a run of `g.toExp Ii` over `sessU`. -/
theorem run_of_sessSpec {Ii : SInst} {calls : List (Fin g.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {u' : Store Nat} {s' : g.exp.St}
    (h : LinkedG.SessSpec P g Ii Ii.store g.exp.init calls outs u' s') :
    (g.toExp Ii).Run P (g.toExp Ii).init (g.sessU calls outs) (u', s') := by
  obtain ⟨L, hL, hp, hr, hm⟩ := Silmaril.Proofs.Wasm.Component.Reference.LinkedG.sessSpec_roundsG h
  have hR := LinkedGDivIR.run_of_rounds_idle L hL hp hr
  rw [hm] at hR
  exact hR

end Calls

/-! ## Prefix closure -/

theorem refSessProd_prefixG {g : LinkedG} {σ : Type} {impl : HostImpl (core3P P) σ} {h₀ : σ}
    {a : ℕ → Fin g.imp.exports.length × List IVal} {out : ℕ → Option (List IVal)}
    (h : LinkedG.RefSessProd P prof g impl h₀ a out) (n : ℕ) :
    refOuts (streamTake out n) ∈ LinkedG.sessObs prof g impl h₀ (streamTake a n) := by
  obtain ⟨m₀, inst, es, fs, hinst, hlk, m, hx⟩ := h
  refine ⟨m₀, inst, es, streamTake fs n, hinst, ?_, ?_⟩
  · simp only [streamTake, List.map_ofFn]
    exact SessionObs.mapM_ofFn_some fun i => hlk i
  · have e₁ : (streamTake fs n).zip (((streamTake a n).map fun q =>
        (g.imp.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
        streamTake (fun k => (fs k, (a k).2.map toRefVal)) n := by
      simp only [streamTake, List.map_ofFn]
      exact SessionObs.zip_ofFn _ _
    have e₂ : refOuts (streamTake out n) =
        streamTake (fun k => (out k).map (List.map toRefVal)) n := by
      simp only [refOuts, streamTake, List.map_ofFn]
      rfl
    rw [e₁, e₂]
    exact SessionObs.SessExec.prefix hx n

/-! ## Forward: a run of rounds is a productive execution -/

section Fwd

variable {σ : Type} {impl : HostImpl (E3 P) σ}
variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- **A run of rounds of `lg.toExp Ii` from between calls is a coherent session execution.** -/
theorem sessExec_fwdB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded)
    (a : ℕ → Fin lg.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (S : ℕ → Store Nat × lg.exp.St)
    (hS : ∀ k, (lg.toExp Ii).Step P (S k) (lg.roundU a out k) (S (k + 1)))
    (m₀ : Machine.Config (E3 P) σ)
    (R₀ : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m₀ (S 0).2 (S 0).1 0) :
    ∃ m, SessExec prof (linkHost impl) m₀ (fun k => (⟨jf (a k).1⟩, (a k).2.map toRefVal))
      (fun k => (out k).map (List.map toRefVal)) m := by
  obtain ⟨m, h0, hm⟩ := SessionObs.exists_stream
    (fun k (m : Machine.Config (E3 P) σ) =>
      ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m (S k).2 (S k).1 k)
    (fun k m m' => SessStep prof (linkHost impl) m k ⟨jf (a k).1⟩ ((a k).2.map toRefVal)
      ((out k).map (List.map toRefVal)) m')
    R₀ (by
      intro k m R
      obtain ⟨dr, hok, hpath, hexp, hr⟩ := hS k
      have hr' : (⟨((a k).1.val, .vals (a k).2), (out k).map .vals⟩ : URound) =
          ⟨(dr.j.val, .vals dr.vs), dr.ans⟩ := hr
      obtain ⟨hq, hans⟩ := Sigma.mk.inj hr'
      obtain ⟨hj, hv⟩ := Prod.mk.inj hq
      have hjj : dr.j = (a k).1 := Fin.ext hj.symm
      have hvv : dr.vs = (a k).2 := (Payload.vals.inj hv).symm
      have hF := linkCall_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB R dr hok hpath
        hexp (eq_of_heq hans).symm
      rw [hjj, hvv] at hF
      cases hout : out k with
      | some ws =>
        rw [hout] at hF
        obtain ⟨m', hc, R'⟩ := hF
        exact ⟨m', .ret hc, R'⟩
      | none =>
        rw [hout] at hF
        obtain ⟨m', hc, R'⟩ := hF
        exact ⟨_, .trap hc, R'⟩)
  exact ⟨m, h0, hm⟩

end Fwd

/-- **A run of rounds of `g.toExp Ii` from its initial state is a productive execution**
(every profile and component choice profile, under every host). -/
theorem refSessProd_of_run {g : LinkedG} (he : g.exp.RefAdeqUX P) (hl : g.LinkOk) {Ii : SInst}
    (hI : g.imp.mod.IsInst Ii) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    {S : ℕ → (g.toExp Ii).St} (h0 : S 0 = (g.toExp Ii).init)
    (hS : ∀ k, (g.toExp Ii).Step P (S k) (g.roundU a out k) (S (k + 1))) :
    LinkedG.RefSessProd P prof g impl h₀ a out := by
  obtain ⟨d, hFr, hFw, -, hInit, hRes, hB⟩ := he
  obtain ⟨tr, m₁, pl, F, es, r, hA, hrs, hh, hs, hnh, ho⟩ :=
    instG_run (prof := prof) (impl := impl) (LinkedGInst.initUX_initSX hInit) hFr hl.wireTy
      hl.good hl.inst hl.arity ⟨hl.split.data, hl.split.elems⟩ hl.names hI h₀
  have ST := statB_init hl.wireTy hl.nodup hl.good hl.arity hl.floats hI hA hh
  have R := readyB_init hFr hB hl.wireTy hl.nodup hI hl.split hA rfl rfl rfl hrs hh
  obtain ⟨m, hm⟩ := sessExec_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB a out S hS _
    (by rw [h0]; exact R)
  refine ⟨afterG g Ii m₁ r, ⟨0⟩, exportMapG g m₁.store.funcs.length,
    fun k => ⟨m₁.store.funcs.length + (a k).1⟩, ?_, fun k => exportMapG_lookup hl.good _ (a k).1,
    m, hm⟩
  refine ⟨tr, hs, hnh, rfl, R.lock, ?_⟩
  rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]

/-! ## Backward: a productive execution is a run, for a deterministic linked component -/

/-- **Session behaviours of every finite prefix of typed calls, read back along one run** of a
deterministic `g.toExp Ii` (every profile and component choice profile, under every host). -/
theorem run_of_prefix {g : LinkedG} (he : g.exp.RefAdeqUX P) (hl : g.LinkOk) {Ii : SInst}
    (hI : g.imp.mod.IsInst Ii) (hd : (g.toExp Ii).Det P)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (h : ∀ n, refOuts (streamTake out n) ∈ LinkedG.sessObs prof g impl h₀ (streamTake a n)) :
    ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
      ∀ k, (g.toExp Ii).Step P (S k) (g.roundU a out k) (S (k + 1)) := by
  refine stream_run_of_det hd _ _ fun n => ?_
  obtain ⟨outs, u', s', hspec, ho⟩ := LinkedG.sess_refToSpecUX P prof he hl.wireTy hl.nodup
    hl.good hl.inst hl.arity hl.floats hl.split hl.names impl h₀ (typed_streamTake ht n) hI (h n)
  obtain rfl := refOuts_inj ho
  refine ⟨(u', s'), ?_⟩
  rw [← sessU_streamTake]
  exact run_of_sessSpec hspec

/-- **The prefixes of a productive execution of typed calls, read back along one run** of a
deterministic `g.toExp Ii`. -/
theorem run_of_refSessProd {g : LinkedG} (he : g.exp.RefAdeqUX P) (hl : g.LinkOk) {Ii : SInst}
    (hI : g.imp.mod.IsInst Ii) (hd : (g.toExp Ii).Det P)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    {impl : HostImpl (core3P P) σ} {h₀ : σ} (h : LinkedG.RefSessProd P prof g impl h₀ a out) :
    ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
      ∀ k, (g.toExp Ii).Step P (S k) (g.roundU a out k) (S (k + 1)) :=
  run_of_prefix he hl hI hd a out ht impl h₀ (refSessProd_prefixG h)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf
