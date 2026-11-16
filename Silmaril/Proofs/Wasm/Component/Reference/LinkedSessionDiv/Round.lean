module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Core

/-!
# Diverging linked calls: prefixes of rounds

* `doomed_resume`, `doomed_no_ask`: an import call answered by a trap leaves the importer's
  thread filled with a trap (`Doomed`), from which it never calls out again;
* `roundsPre_fwd`: the prefix variant of `rounds_fwd`. A path of the importer's instance from
  `.running f` along `callMoves rs` to `.running f s t` (no answer yet), whose import calls are
  answered by the exporter's specification (`ExpRunT`), is a segmented run `LSeg` of the shared
  thread with one record per import call, `LInv` holding at its end with the part at `(s, t)`
  and the exporter's end store; unless an import call was answered by a trap, in which case the
  part is `Doomed` at `(s, t)`;
* `lseg_runN`: `lseg_run` with the trace nonempty when the segmented run makes a nested call.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type}

/-! ## Doomed threads after a trapped import call -/

/-- **An import call answered by a trap dooms the thread.** -/
theorem doomed_resume {s : Store Nat} {t : STh} {k : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hc : Silmaril.Wasm.Game.CalloutAt s t k args) :
    Doomed s (Silmaril.Wasm.SingleThreaded.resumeResult s t .trap) := by
  obtain ⟨E, a, hd⟩ := hc
  have hd' : Silmaril.Wasm.SingleThreaded.decompose? (t.config s).store (t.config s).code =
      some (E, a, k, args) := (Silmaril.Wasm.SingleThreaded.Thread.config_store s t).symm ▸ hd
  refine ⟨(t.config s).frame, E, ?_⟩
  rw [resumeResult_config hd' .trap, Silmaril.Wasm.SingleThreaded.Thread.config_store]
  rfl

variable {Ii : Silmaril.Wasm.Game.ScalarInstance} {f : Ii.F.Op}

/-- **A doomed thread never calls out.** -/
theorem doomed_no_ask {s : Store Nat} {t : STh} (hd : Doomed s t) {e : Ii.E.Op}
    {rest : List (Move Ii.E Ii.F)} {q : Ii.HState}
    (h : Ii.Path P (.running f s t) (.inl (.ask e) :: rest) q) : False := by
  obtain ⟨fr, E, ht⟩ := hd
  cases h with
  | cons h₁ _ =>
    cases h₁ with
    | ucall run co _ => exact reach_doomed_callout run ht co

/-- A doomed thread has no served import call. -/
theorem doomed_no_call {s : Store Nat} {t : STh} (hd : Doomed s t)
    {c : Σ e : Ii.E.Op, Ii.E.Ar e} {q : Ii.HState}
    (h : Ii.Path P (.running f s t) (callMoves [c]) q) : False := by
  obtain ⟨e, v⟩ := c
  exact doomed_no_ask hd h

/-! ## Prefixes of rounds -/

variable {l : Linked2} {Ie : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}

/-- **A prefix of a specification round is a segmented run of the shared thread**, or the
importer's thread is doomed (an import call was answered by a trap). -/
theorem roundsPre_fwd (S : LStat P l Ie Ii u₀ F₀ B Op₀) :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (π π₁ s : Store Nat) (t : STh),
      LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rs dss →
      Linked2.ExpRunT P l Ie π dss.flatten π₁ →
      Ii.Path P (.running f x.1 x.2) (callMoves rs) (.running f s t) →
      (∃ (recs : List (LRec P)) (yc : CoreSt (E3 P)), LSeg B y recs yc ∧
        recs.length = rs.length ∧ LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f yc (s, t) π₁) ∨
      Doomed s t
  | [], dss, y, x, π, π₁, s, t, hI, hrel, hexp, hpath => by
    cases hrel
    cases hexp
    cases hpath
    exact .inl ⟨[], y, .done .refl, rfl, hI⟩
  | ⟨e, v⟩ :: rs, dss₀, y, x, π, π₁, s, t, hI, hrel, hexp, hpath => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss, Silmaril.Wasm.Component.Reference.ImpRel
        l.imp Ii ⟨e, v⟩ ds ∧ List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii)
          rs dss ∧ dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs)
      (by simpa [callMoves] using hpath)
    -- after a trapped import call the thread is doomed
    have hdoom : v = .trap → Doomed s t := by
      intro hv
      subst hv
      cases rs with
      | nil =>
        cases hpath'
        exact doomed_resume co
      | cons r rs =>
        obtain ⟨e', v'⟩ := r
        exact (doomed_no_ask (doomed_resume co) hpath').elim
    obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwd S hI run
    obtain ⟨nm, p, wi, xe, ys, E, a, hk, hw, hxe, hpx, hdx, hys, hst, hyty⟩ :=
      LInv.callout_fwd S hI₁ co op
    have hek := ifaceOp?_some op
    obtain ⟨nm', ft, A, hk', hA, hm⟩ := hd
    have hA' : payloadAnswer (Ii.imports.get e.1) A = v := hA
    have hft : ft = p := by
      rw [hek.1, hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact hk'.2.symm
    subst hft
    have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
      hek.2 ▸ filterMap_of_mapM hys
    have hmi : (nm, ft) ∈ l.imp.imports := List.mem_of_getElem? hk
    have hres : ft.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
    have hfl : ArenaField.funcs.get? B.store (l.wireFid k) =
        some (.lifted (Ie.addrs.getD xe.core 0) (witFt ft) {} ⟨1⟩) :=
      hpx ▸ S.lifted k wi xe hw hxe
    rw [hfilt] at hm
    split at hm
    · -- the arguments do not lift
      obtain ⟨rfl, rfl⟩ := hm
      exact .inr (hdoom hA.symm)
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      have hexp' : Linked2.ExpRunT P l Ie π
          (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) π₁ := by
        simpa only [List.flatten_cons, List.singleton_append] using hexp
      cases hexp' with
      | @ret _ π₂ _ _ _ us _ w₂ hwire hRet hrest =>
        have hw₂ : w₂.val = wi := by
          rw [hek.1, hw] at hwire
          exact (Option.some.inj hwire).symm
        have hx₂ : l.exp.exports[w₂] = xe :=
          (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w₂.val]? = some xe)).2
        rw [hx₂] at hRet
        obtain ⟨ev, zs, hrunA, hstA, husA, hI₂⟩ :=
          LInv.resume_fwd S hI₁ (hpx ▸ hk) hxe hdx op hRet
        have hcheck : ValTy.checkList ft.results us = true :=
          Silmaril.Wasm.Component.checkList_of_liftArgs (hpx ▸ husA)
        have hv : Silmaril.Wasm.Game.Answer.toResult v =
            .values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
          rw [← hA', hAR, hpx]
          have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower ft).up =
              some (.flat (lowerArgs ft.results us)) := by
            simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
              Silmaril.Wasm.Component.checkLower, hcheck, ite_true, Option.map_some]
          rw [hup, payloadAnswer_flat (w := .values ⟨_, resAnswer S hk hek.1 hcheck⟩) rfl]
          rfl
        rw [hv] at hpath'
        rcases roundsPre_fwd S rs dss _ _ _ π₁ s t hI₂ hrel' hrest hpath' with
          ⟨recs, yc, hseg, hlen, hIc⟩ | hdm
        · exact .inl ⟨_, yc, .call hy₁ hst hfl hres hws (hpx ▸ hrunA) hstA (hpx ▸ husA)
            (hpx ▸ hseg), by simp [hlen], hIc⟩
        · exact .inr hdm
      | trap w₂ hwire hT hrest =>
        exact .inr (hdoom (by rw [← hA', hAR]; rfl))

/-! ## Segmented runs with nonempty traces -/

/-- `lseg_run`, the trace nonempty when the segmented run makes a nested call. -/
theorem lseg_runN {prof : ProfileKind} {impl : HostImpl (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} (hB : LFrame B th) {x z : CoreSt (E3 P)}
    {recs : List (LRec P)} (h : LSeg B x recs z) :
    ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))),
      ThreadsOk ιe → LinkOk B x →
      ∃ (ιe' : InstState) (N' : List (NRec P)) (C' : List (Option (Activation (E3 P) σ)))
        (tr : List (Label (E3 P) σ)), ThreadsOk ιe' ∧ Quiet tr ∧ (recs = [] ∨ tr ≠ []) ∧
        Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr
          (coreCfg (extN B ιe' N' C') th K segs rest z) := by
  induction h with
  | done hy =>
    intro ιe N C hte _
    obtain ⟨tr, htr, r⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K) (segs := segs)
      (rest := rest) hy
    exact ⟨ιe, N, C, tr, hte, Quiet.of_core htr, .inl rfl, r⟩
  | @call x y e z f a p ys zs ws us rest₁ hy hs hf hr hws he hst hus _ ih =>
    intro ιe N C hte hk
    obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof)
      (hr := fun _ _ => false) (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K)
      (segs := segs) (rest := rest) hy
    obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexp⟩ := site_of (hk [] y _ ys (.done hy) hs) hf hr
    obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
    obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, hret, -⟩ :=
      nest_atTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
        (hB.entry _ _ _ _ _) hi hleave hf hB.len (addThread?_ok hte _)
        (removeThread?_enter ιe _) hpf hys hmaxp hws hr hrf hmaxr
    have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y.1,
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) := by
      rw [← hcore]
      exact eq_coreCfg hctl
    obtain ⟨tr₃, htr₃, r₃⟩ := Adequacy.coreCfg_steps_of (prof := prof)
      (hr := fun _ _ => false) (dispatch := DI P impl) (B := M₁) (th := th') (K := K')
      (segs := segs') (rest := rest') he
    have s₄ : Step prof (fun _ _ => false) (DI P impl) (coreCfg M₁ th' K' segs' rest' e) .tau
        (retCfg M₁ th' K' segs' rest' e zs) := Step.coreReturned rfl hst
    have hty : zs.map (·.type) = ValTy.flatList p.results := (hexp ws hws e he).2 zs hst
    obtain ⟨tr₅, h₅⟩ := hret e zs us hty hus
    obtain ⟨ιe'', N'', C'', tr₆, hte', hq₆, -, r₆⟩ := ih _ _ C₁ (threadsOk_after _ _)
      (hk.after hy hs hf hr hws he hst hus)
    have hlive₁ : Live M₁ := ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hlock⟩
    refine ⟨ιe'', N'', C'', tr₁ ++ (tr₂ ++ (tr₃ ++ (.tau :: (tr₅ ++ tr₆)))), hte', ?_,
      .inr (by simp), ?_⟩
    · refine (Quiet.of_core htr₁).append ((Quiet.of_lrun hrun hlive₁).append
        ((Quiet.of_core htr₃).append (?_ : Quiet (.tau :: (tr₅ ++ tr₆)))))
      exact (Quiet.tau (P := P) (σ := σ)).append ((Quiet.of_lrun h₅
        (coreCfg_extN_live _ _ _ _ _ _ _ _ _)).append hq₆)
    · refine Adequacy.steps_append r₁ (Adequacy.steps_append hrun.steps ?_)
      rw [← hM] at r₃
      refine Adequacy.steps_append r₃ (.cons s₄ (Adequacy.steps_append h₅.steps r₆))

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
