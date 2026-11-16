module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Stat

/-!
# Forward runs of a call of `HLinked2.toRef`: a round up to its first host call

* `KSeg B x recs z`: `LSeg` (a segmented run of the importer's core phase with nested calls to
  the exporter) recording, at each nested call, that its callout is a link site. `kseg_run` is
  `lseg_run` for it: it is a quiet machine run, without `LinkOk` (which fails as soon as the
  importer can reach a host callout);
* `rounds_toHost`: from `LInv` over the host-first layout, a specification round whose component
  import calls (`HLinked2.ExpRunH`) contain a host call is followed by the shared thread, as a
  `KSeg`, up to the callout of its first host call: the trampoline of host function `i`, on flat
  arguments of the host import's parameter types that lift. Before it every import call is a
  returned call of the exporter (a trapped one, or one whose arguments do not lift, ends the
  round at once: `path_doomed`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
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

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Segmented runs with their link sites -/

/-- **A segmented run of the importer's core phase with nested calls**, each callout a link
site (`LSeg` with `LinkSite` at each nested call). -/
inductive KSeg (B : Machine.Config (E3 P) σ) : CoreSt (E3 P) → List (LRec P) → CoreSt (E3 P) →
    Prop
  | done {x y : CoreSt (E3 P)} : Relation.ReflTransGen (CoreStep (E3 P)) x y → KSeg B x [] y
  | call {x y e z : CoreSt (E3 P)} {f : FuncId} {a : (E3 P).FuncAddr}
      {p : FuncTy} {ys zs : List Flat} {ws us : List Silmaril.Wasm.Component.Val}
      {rest : List (LRec P)} :
      Relation.ReflTransGen (CoreStep (E3 P)) x y →
      (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys →
      ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩) →
      p.results.length ≤ 1 → liftArgs p.params ys = some ws →
      LinkSite B y (.lowered f (witFt p) {} ⟨2⟩) ys →
      Relation.ReflTransGen (CoreStep (E3 P))
        (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) e →
      (E3 P).status e.1 e.2 = .returned (.values zs) → liftArgs p.results zs = some us →
      KSeg B (e.1, (E3 P).resume e.1 y.2 (.values (lowerArgs p.results us))) rest z →
      KSeg B x (⟨f, a, p, ys, ws, y, e, zs, us⟩ :: rest) z

/-- **A segmented run with its link sites is a quiet machine run** (`lseg_run`). -/
theorem kseg_run {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} (hB : LFrame B th) {x z : CoreSt (E3 P)}
    {recs : List (LRec P)} (h : KSeg B x recs z) :
    ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ))),
      ThreadsOk ιe →
      ∃ (ιe' : InstState) (N' : List (NRec P)) (C' : List (Option (Activation (E3 P) σ)))
        (tr : List (Label (E3 P) σ)), ThreadsOk ιe' ∧ Quiet tr ∧
        Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr
          (coreCfg (extN B ιe' N' C') th K segs rest z) := by
  induction h with
  | done hy =>
    intro ιe N C hte
    obtain ⟨tr, htr, r⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K) (segs := segs)
      (rest := rest) hy
    exact ⟨ιe, N, C, tr, hte, Quiet.of_core htr, r⟩
  | @call x y e z f a p ys zs ws us rest₁ hy hs hf hr hws hS he hst hus _ ih =>
    intro ιe N C hte
    obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof)
      (hr := fun _ _ => false) (dispatch := DI P impl) (B := extN B ιe N C) (th := th) (K := K)
      (segs := segs) (rest := rest) hy
    obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexp⟩ := site_of hS hf hr
    obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe N C
    have hadd := addThread?_ok hte ⟨(extN B ιe N C).store.threads.length⟩
    have hrem := removeThread?_enter ιe ⟨(extN B ιe N C).store.threads.length⟩
    obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₂, hrun, hctl, hcore, hlock, hret, -⟩ :=
      nest_atTS (prof := prof) (impl := impl) B ιe _ N C th K segs rest y f a p ys ιi ws hs
        (hB.entry _ _ _ _ _) hi hleave hf hB.len hadd hrem hpf hys hmaxp hws hr hrf hmaxr
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
    obtain ⟨ιe'', N'', C'', tr₆, hte', hq₆, r₆⟩ := ih _ _ C₁ (threadsOk_after _ _)
    have hlive₁ : Live M₁ := ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hlock⟩
    refine ⟨ιe'', N'', C'', tr₁ ++ (tr₂ ++ (tr₃ ++ (.tau :: (tr₅ ++ tr₆)))), hte', ?_, ?_⟩
    · refine (Quiet.of_core htr₁).append ((Quiet.of_lrun hrun hlive₁).append
        ((Quiet.of_core htr₃).append (?_ : Quiet (.tau :: (tr₅ ++ tr₆)))))
      exact (Quiet.tau (P := P) (σ := σ)).append ((Quiet.of_lrun h₅
        (coreCfg_extN_live _ _ _ _ _ _ _ _ _)).append hq₆)
    · refine Adequacy.steps_append r₁ (Adequacy.steps_append hrun.steps ?_)
      rw [← hM] at r₃
      refine Adequacy.steps_append r₃ (.cons s₄ (Adequacy.steps_append h₅.steps r₆))

/-! ## A round up to its first host call -/

/-- A wired component import call is not a host call. -/
theorem hostCalls_cons_wired {l : HLinked2}
    {d : Σ _ : (sigN l.imp.imports.length).Op, Option Payload}
    {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : d.1.1.val < l.wire.length) : l.hostCalls (d :: ds) = l.hostCalls ds := by
  have hn : l.hostCall? d = none := by
    unfold HLinked2.hostCall?
    split
    · omega
    · rfl
  exact List.filterMap_cons_none hn

/-- The host import `i` of a host call of the importer's import `k`. -/
theorem host_get_of {l : HLinked2} (hW : l.WireTy) {k : Nat} {nm : String} {p : FuncTy}
    (hk : l.imp.imports[k]? = some (nm, p)) (hwk : ¬ k < l.wire.length) :
    ∃ hi : k - l.wire.length < l.host.length, l.host[k - l.wire.length] = (nm, p) := by
  have hkl : k < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  have hlen := imports_length hW
  have hi : k - l.wire.length < l.host.length := by omega
  have e2 : l.wire.length + (k - l.wire.length) = k := by omega
  have hget : l.host[k - l.wire.length]? = some (nm, p) := by
    rw [← hW.shape.1, List.getElem?_drop, e2, hk]
  exact ⟨hi, (List.getElem?_eq_some_iff.mp hget).2⟩

/-- **A specification round with a host call is followed by the shared thread up to the callout
of its first host call**: a `KSeg` of returned nested calls to the exporter, then the callout to
the trampoline of host function `i`, on flat arguments of its parameter types that lift. -/
theorem rounds_toHost {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    {u₀ s₀ u : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
    {B : Machine.Config (E3 P) σ} {f : Ii.F.Op} (S : HStat P l Ie Ii u F₀ B (ownOf s₀))
    {w : Ii.F.Ar f} :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (π π₁ u₁ : Store Nat),
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rs dss →
      HLinked2.ExpRunH P l Ie π dss.flatten π₁ →
      Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f w)]) (.idle u₁) →
      l.hostCalls dss.flatten ≠ [] →
      ∃ (recs : List (LRec P)) (yc : CoreSt (E3 P)) (i : Nat) (hi : i < l.host.length)
        (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
        KSeg B y recs yc ∧
        (E3 P).status yc.1 yc.2 = .callout (.lowered ⟨i⟩ (witFt l.host[i].2) {} ⟨2⟩) ys ∧
        ys.map (·.type) = ValTy.flatList l.host[i].2.params ∧
        liftArgs l.host[i].2.params ys = some ws
  | [], dss, y, x, π, π₁, u₁, hI, hrel, hexp, hpath, hh => by
    cases hrel
    exact (hh rfl).elim
  | ⟨e, v⟩ :: rs, dss₀, y, x, π, π₁, u₁, hI, hrel, hexp, hpath, hh => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss, Silmaril.Wasm.Component.Reference.ImpRel
        l.imp Ii ⟨e, v⟩ ds ∧ List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii)
          rs dss ∧ dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs ++
      [.inr (.ans f w)]) (by simpa [callMoves] using hpath)
    obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwdH S hI run
    obtain ⟨nm, p, ys, E, a, hk, hdx, hys, hst, hyty⟩ := LInv.callout_fwdH S hI₁ co op
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
    rw [hfilt] at hm
    split at hm
    · -- the arguments do not lift: the round ends at once, without a host call
      next hws =>
      obtain ⟨rfl, rfl⟩ := hm
      have hv : v = .trap := hA.symm
      subst hv
      obtain ⟨rfl, -, -⟩ := path_doomed co hpath'
      cases hrel'
      exact (hh rfl).elim
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      by_cases hwk : k < l.wire.length
      · -- a wired call
        have hexp' : HLinked2.ExpRunH P l Ie π
            (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) π₁ := by
          simpa only [List.flatten_cons, List.singleton_append] using hexp
        have hh' : l.hostCalls dss.flatten ≠ [] := by
          intro h0
          apply hh
          rw [List.flatten_cons, List.singleton_append,
            hostCalls_cons_wired (by simpa [hek.1] using hwk), h0]
        obtain ⟨wi, hw⟩ : ∃ wi, l.wire[k]? = some wi := ⟨_, List.getElem?_eq_getElem hwk⟩
        obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty k wi hw
        have hpx : xe.ty = ft := by
          rw [hk] at hty
          simp only [Option.map_some, Option.some.injEq] at hty
          exact hty.symm
        subst hpx
        have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
        have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
        have hfl : ArenaField.funcs.get? B.store (l.fid k) =
            some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
          S.lifted k wi xe hw hxe
        have hsite : LinkSite B y₁ (.lowered (l.fid k) (witFt xe.ty) {} ⟨2⟩) ys :=
          LInv.siteH S hI₁ hk hw hxe hyty
        cases hexp' with
        | @ret _ π₂ _ _ _ us _ w₂ hwire hRet hrest =>
          have hw₂ : w₂.val = wi := by
            rw [hek.1, hw] at hwire
            exact (Option.some.inj hwire).symm
          have hx₂ : l.exp.exports[w₂] = xe :=
            (List.getElem?_eq_some_iff.mp (hw₂.symm ▸ hxe : l.exp.exports[w₂.val]? = some xe)).2
          rw [hx₂] at hRet
          obtain ⟨ev, zs, hrunA, hstA, husA, hI₂⟩ := LInv.resume_fwdH S hI₁ hk hxe hdx op hRet
          have hcheck : ValTy.checkList xe.ty.results us = true :=
            Silmaril.Wasm.Component.checkList_of_liftArgs husA
          have hv : Silmaril.Wasm.Game.Answer.toResult v =
              .values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
            rw [← hA', hAR]
            have hup : (some (Payload.vals us)).bind
                (Silmaril.Wasm.Component.Adapter.lower xe.ty).up =
                some (.flat (lowerArgs xe.ty.results us)) := by
              simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
                Silmaril.Wasm.Component.checkLower, hcheck, ite_true, Option.map_some]
            rw [hup, payloadAnswer_flat (w := .values ⟨_, resAnswerH S hk hek.1 hcheck⟩) rfl]
            rfl
          rw [hv] at hpath'
          obtain ⟨recs, yc, i, hi, ys', ws', hseg, h₁, h₂, h₃⟩ :=
            rounds_toHost S rs dss _ _ _ π₁ u₁ hI₂ hrel' hrest hpath' hh'
          exact ⟨_, yc, i, hi, ys', ws',
            .call hy₁ hst hfl hres hws hsite hrunA hstA husA hseg, h₁, h₂, h₃⟩
        | trap w₂ hwire hT hrest =>
          have hv : v = .trap := by
            rw [← hA', hAR]
            rfl
          subst hv
          obtain ⟨rfl, -, -⟩ := path_doomed co hpath'
          cases hrel'
          exact (hh' rfl).elim
        | host i hn hrest =>
          have h1 := hek.1
          simp only at hn
          omega
      · -- the first host call: stop at its callout
        obtain ⟨hi, hhost⟩ := host_get_of S.wireTy hk hwk
        have hfid : l.fid k = ⟨k - l.wire.length⟩ := by
          simp only [HLinked2.fid, hwk, ↓reduceIte]
        refine ⟨[], y₁, k - l.wire.length, hi, ys, ws, .done hy₁, ?_, ?_, ?_⟩
        · rw [hhost, ← hfid]
          exact hst
        · rw [hhost]
          exact hyty
        · rw [hhost]
          exact hws

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
