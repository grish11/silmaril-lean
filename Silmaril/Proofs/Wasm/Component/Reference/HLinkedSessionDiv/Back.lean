module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Trace
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.RefSess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.Main

/-!
# Diverging calls of `HLinked2.toRef`, backward: one round on an explicit run

From the importer's core activation at position `p` of an explicit infinite run `t`
(`t p = coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y`), `LInv` (at `l.toW`) relating it
to the importer's part `x` and the exporter's store `π`, `ldiv_roundH` follows `t`:

* **(i)** B's core activation runs forever: B's part runs host-free forever (`Linked2.DivB`,
  `link_inf_back`), and from `p` on the run stays in host state `h`;
* **(ii)** B calls out a wired import on arguments that lift and the nested activation of A runs
  forever: A diverges inside the import call (`Linked2.DivA`, at `l.toL2`), and from some
  position on the run stays in host state `h` (`nest_atTSH` keeps the host state);
* **(iii)** one served import call to a later position `p' > p`, where the importer's core
  activation is resumed, `LInv` holding again: a nested call to A that returned values that lift
  (`LInv.resumeH`), host state unchanged; or a host call answered as `g` answers in host state
  `h` (`HostHandlesB`, `LInv.resumeHost_fwdH`), the host state moving along the `HostRun`.

The other ends do not diverge: arguments that do not lift, a trap of A, results of A that do not
lift, a host call `g` does not answer all trap (`TrapsAtSH`), and the exits of B's core phase
other than callouts do not diverge (`ExitsQuietH`, `exitsQuietH_call`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

theorem TrapsAtSH.trapsFromH {M : Machine.Config (E3 P) σ}
    {c : (E3 P).Store (CanonHost (E3 P))} {h : σ} (H : TrapsAtSH prof P impl M c h) :
    TrapsFrom prof P impl M := by
  obtain ⟨tr, mT, r, -, h₁, hl, hu, -, -⟩ := H
  exact ⟨tr, mT, r, h₁, hl, hu⟩

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

/-- **The exits of the importer's core phase other than callouts do not diverge**, in every
`extG` extension of the call's frame. -/
def ExitsQuietH (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) (l : HLinked2)
    (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ u : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (M₀ : Machine.Config (E3 P) σ)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ)) (f : Ii.F.Op) : Prop :=
  ∀ (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) (h : σ) (y : CoreSt (E3 P))
    (x : Store Nat × STh) (π : Store Nat) (lb : Label (E3 P) σ) (m₁ : Machine.Config (E3 P) σ),
    LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π →
    (∀ h ys, (E3 P).status y.1 y.2 ≠ .callout h ys) →
    CoreExit (extG M₀ ιe SL CL TL HL C h) th K segs rest y lb m₁ →
    ¬ Diverges prof (fun _ _ => false) (DI P impl) m₁

/-- **In the frame of a call, the exits of the importer's core phase other than callouts do not
diverge** (`exitsQuiet_call` with the `extG` extensions). -/
theorem exitsQuietH_call {cs : (core3P P).Store (CanonHost (core3P P))} {ιe₀ ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j a : Nat}
    {x : SimpleExport} {vs : List Silmaril.Wasm.Component.Val}
    (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀))
    (hat : CallAtLKTS prof P impl cs ιe₀ ιi fs G ST h₀ k j x a vs M₀ th K segs rest)
    (hft : Ii.exports.get f.1 = fnOf x.ty.flat) :
    ExitsQuietH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f := by
  intro ιe SL CL TL HL C h y xp π lb m₁ hI hnco hx
  rcases hx with ⟨zs, hst, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨h', ys, hc⟩
  · obtain ⟨cvs, hcode, hm⟩ := status_values hst
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
    obtain ⟨ts, hs, ht⟩ := LInv.typedH S hI
    have hc : (y.2.config (Store.mapH (gL P l.toW) y.1)).code =
        Silmaril.Wasm.Execution.Core.vals cvs :=
      (config_code_mapH (gL P l.toW) y.1 y.2).trans hcode
    obtain ⟨vs', hv, hvm⟩ := values_back P hL hs ht hc
    have hm' : (vs'.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
        some zs := by
      rw [hvm]
      exact hm
    have hvs' : vs' = cvs := (map_val_of_mapM _ hm').symm.trans hvm
    have hr : Silmaril.Wasm.Game.ResultAt xp.1 xp.2 (.values cvs) := hvs' ▸ hv
    obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
      (valEnv_throwsBelow Ii _) hI.run hr
    have hty : zs.map (·.type) = ValTy.flatList x.ty.results := results_typed hft hw hm
    cases hl : liftArgs x.ty.results zs with
    | some ws =>
      obtain ⟨C', hRes⟩ := hat.retG ιe SL CL TL HL C h y zs ws hty hl
      exact ResolvesAtL.not_diverges hRes
    | none => exact TrapsFrom.not_diverges (TrapsAtSH.trapsFromH (hat.trapGH ιe SL CL TL HL C h y zs hty hl))
  · exact not_diverges_trapCfg _
  · exact absurd hc (hnco h' ys)

/-- **One round of a quietly diverging call on an explicit run**: (i), (ii), or a served import
call to a later position. -/
theorem ldiv_roundH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandlesB prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g)
    (hex : ExitsQuietH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f)
    {t : ℕ → Machine.Config (E3 P) σ} (ht : IRun prof (fun _ _ => false) (DI P impl) t)
    {p : ℕ} {ιe : InstState} {SL : List Subtask} {CL : List (Caller (E3 P))}
    {TL : List (Runtime.Task (E3 P))} {HL : List Runtime.Thread}
    {C : List (Option (Activation (E3 P) σ))} {h : σ} {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat}
    (hp : t p = coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) (hte : ThreadsOk ιe)
    (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π) :
    (Linked2.DivB P x.1 x.2 ∧ ∀ n, p ≤ n → (t n).host = h) ∨
    (Linked2.DivA P l.toL2 Ie Ii f x.1 x.2 π ∧ ∃ p₀, ∀ n, p₀ ≤ n → (t n).host = h) ∨
    ∃ (c : Σ e : Ii.E.Op, Ii.E.Ar e)
      (ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)) (p' : ℕ)
      (ιe' : InstState) (SL' : List Subtask) (CL' : List (Caller (E3 P)))
      (TL' : List (Runtime.Task (E3 P))) (HL' : List Runtime.Thread)
      (C' : List (Option (Activation (E3 P) σ))) (h' : σ) (y' : CoreSt (E3 P))
      (x' : Store Nat × STh) (π' : Store Nat),
      p < p' ∧ t p' = coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' h') th K segs rest y' ∧
      ThreadsOk ιe' ∧
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y' x' π' ∧
      Ii.Path P (.running f x.1 x.2) (callMoves [c]) (.running f x'.1 x'.2) ∧
      Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds ∧
      HLinked2.ExpRunH P l Ie π ds π' ∧ HostRun g h (l.hostCalls ds) h' ∧
      ((l.hostCalls ds = [] ∧ h' = h) ∨ ∃ fn args rs, g h fn args = some (rs, h')) := by
  rcases IRun.core ht hp with ⟨hinf, hhost⟩ | ⟨n, hpn, y₁, lb, hn, hy, hx, -, -⟩
  · -- (i) B's core activation runs forever
    left
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
    obtain ⟨ts, hs, ht'⟩ := LInv.typedH S hI
    exact ⟨link_inf_back (gL P l.toW) hinf hL hs ht', hhost⟩
  obtain ⟨⟨zs, zt⟩, hI₁, hr₁⟩ := LInv.reachH S hI hy
  by_cases hco : ∃ h ys, (E3 P).status y₁.1 y₁.2 = .callout h ys
  swap
  · exact absurd (ht.diverges (n + 1))
      (hex ιe SL CL TL HL C h y₁ _ π lb _ hI₁ (fun h ys e => hco ⟨h, ys, e⟩) hx)
  obtain ⟨hc, ys, hst⟩ := hco
  obtain ⟨k, nm, pT, E, a', args, e, rfl, hk, hdx, hm, he', hyty⟩ := LInv.calloutH S hI₁ hst
  obtain ⟨hek, rfl⟩ := ifaceOp?_some he'
  subst hek
  have hkl : e.1.val < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys := filterMap_of_mapM hm
  have hco' : Silmaril.Wasm.Game.CalloutAt zs zt e.1.val e.2.1 := ⟨E, a', hdx⟩
  have hdn := ht.diverges n
  rw [hn] at hdn
  by_cases hwk : e.1.val < l.wire.length
  · -- a wired import: a nested call of the exporter
    obtain ⟨wi, hw⟩ : ∃ wi, l.wire[e.1.val]? = some wi := ⟨_, List.getElem?_eq_getElem hwk⟩
    obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty e.1.val wi hw
    have hpx : xe.ty = pT := by
      rw [hk] at hty
      simp only [Option.map_some, Option.some.injEq] at hty
      exact hty.symm
    subst hpx
    have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
    have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
    have hfl : ArenaField.funcs.get? M₀.store (l.fid e.1.val) =
        some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
      S.lifted e.1.val wi xe hw hxe
    have hsite : LinkSite M₀ y₁ (.lowered (l.fid e.1.val) (witFt xe.ty) {} ⟨2⟩) ys :=
      LInv.siteH S hI₁ hk hw hxe hyty
    obtain ⟨hpf, hys, hmaxp, hrf, hmaxr, hexpS⟩ := site_of hsite hfl hres
    have hB := hF.lframe ιe SL CL TL HL C h
    have hf' : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C h).store (l.fid e.1.val) =
        some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
      (funcs_extG _ _ _ _ _ _ _ _ _).trans hfl
    obtain ⟨ιi, hi, hleave⟩ := hB.inst2 ιe [] C
    have hadd := addThread?_ok hte
      ⟨(extN (extG M₀ ιe SL CL TL HL C h) ιe [] C).store.threads.length⟩
    have hrem := removeThread?_enter ιe
      ⟨(extN (extG M₀ ιe SL CL TL HL C h) ιe [] C).store.threads.length⟩
    have hn' : t n = coreCfg (extN (extG M₀ ιe SL CL TL HL C h) ιe [] C) th K segs rest y₁ := by
      rw [extN_extG_nil]
      exact hn
    have hxm : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
    have hwl : wi < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
    have hxw : l.exp.exports[(⟨wi, hwl⟩ : Fin l.exp.exports.length)] = xe :=
      (List.getElem?_eq_some_iff.mp hxe).2
    cases hws : liftArgs xe.ty.params ys with
    | none =>
      have hT' := nest_trap_argsTSH (prof := prof) (impl := impl)
        (extG M₀ ιe SL CL TL HL C h) ιe _ [] C th K segs rest y₁ (l.fid e.1.val) _ xe.ty ys ιi
        hst (hB.entry _ _ _ _ _) hi hleave hf' hB.len hadd hpf hys hmaxp hws
      rw [extN_extG_nil] at hT'
      exact absurd hdn (TrapsFrom.not_diverges (TrapsAtSH.trapsFromH hT'))
    | some ws =>
      have hfw : liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) =
          some ws := by rw [hfilt, hws]
      obtain ⟨pos, C₁, M₁, th', K', segs', rest', tr₁, hrun, hctl, hcore, hlock, hhost, hret,
        htrap⟩ := nest_atTSH (prof := prof) (impl := impl)
          (extG M₀ ιe SL CL TL HL C h) ιe _ [] C th K segs rest y₁ (l.fid e.1.val) _ xe.ty ys ιi
          ws hst (hB.entry _ _ _ _ _) hi hleave hf' hB.len hadd hrem hpf hys hmaxp hws hres hrf
          hmaxr
      have hM : M₁ = coreCfg M₁ th' K' segs' rest' (y₁.1,
          Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
            (lowerArgs xe.ty.params ws)) := by
        rw [← hcore]
        exact eq_coreCfg hctl
      have hp₁ := ht.lrun hrun hn'
      have hp₁' := hp₁.trans hM
      have typed : ValTy.checkList xe.ty.params ws = true :=
        Silmaril.Wasm.Component.checkList_of_liftArgs hws
      rcases IRun.core ht hp₁' with ⟨hinfA, hhostA⟩ | ⟨n₂, hpn₂, ev, lb', hn₂, hev, hx₂, -, -⟩
      · -- (ii) the nested activation of A runs forever
        right; left
        obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI₁.rel
        obtain ⟨nm', hcx⟩ := S.expGood.core xe hxm
        have hkc : xe.core < l.exp.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
        obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hI₁.wf
          (opAt S.expInst hkc (exp_hxs hcx typed hkc))
        have hL₀ := exp_invoke hR.rp hI₁.fnE (hR.fnp ▸ S.owned xe hxm) (lowerArgs xe.ty.params ws)
        have hrunA := link_inf_back (gL P l.toW) hinfA hL₀ hI₁.wf.storeOk htyped
        refine ⟨⟨e, zs, zt, nm, xe.ty, ws, ⟨wi, hwl⟩, .cons (.ucall hr₁ hco' he') (.nil _), hk,
          hfw, hw, ?_⟩, n + tr₁.length, fun n' hn' => ?_⟩
        · rw [hxw]
          exact ⟨typed, hrunA⟩
        · rw [hhostA n' hn']
          exact hhost
      · obtain ⟨hnco, htyz⟩ := hexpS ws hws ev hev
        rcases hx₂ with ⟨zs', hzs, -, hm₂⟩ | ⟨-, -, hm₂⟩ | ⟨h', ys', hc'⟩
        · have hdn₂ := ht.diverges (n₂ + 1)
          rw [hm₂] at hdn₂
          cases hus : liftArgs xe.ty.results zs' with
          | none =>
            exact absurd hdn₂ (TrapsFrom.not_diverges
              (TrapsAtSH.trapsFromH (htrap ev zs' (htyz zs' hzs) hus)))
          | some us =>
            -- (iii) one served wired import call
            right; right
            obtain ⟨tr₄, h₄⟩ := hret ev zs' us (htyz zs' hzs) hus
            have hp₂ := ht.lrun h₄ hm₂
            rw [extN_extG] at hp₂
            obtain ⟨π₂, hI₂, hRet⟩ := LInv.resumeH S hI₁ hk hxe hdx he' hws hev hzs hus
            have hcheck : ValTy.checkList xe.ty.results us = true :=
              Silmaril.Wasm.Component.checkList_of_liftArgs hus
            have hrel₁ := impRel_link (l := l.toL2) hk rfl rfl hm hws hcheck
              (.values ⟨_, resAnswerH S hk rfl hcheck⟩) rfl
            have hw' : l.wire[(⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val]? = some wi := hw
            refine ⟨⟨e, .values ⟨_, resAnswerH S hk rfl hcheck⟩⟩, _, _, _, _, _, _, _, _, h, _,
              _, π₂, by omega, hp₂, threadsOk_after _ _, hI₂,
              .cons (.ucall hr₁ hco' he') (.cons (.uret _) (.nil _)), hrel₁,
              .ret ⟨wi, hwl⟩ hw' (hxw ▸ hRet) (.nil π₂), hostRun_wired (by exact hwk) (.nil h),
              .inl ⟨hostCalls_cons_wired (by exact hwk), rfl⟩⟩
        · have hdn₂ := ht.diverges (n₂ + 1)
          rw [hm₂] at hdn₂
          exact absurd hdn₂ (not_diverges_trapCfg _)
        · exact absurd hc' (hnco h' ys')
  · -- a host import: a host callout
    obtain ⟨hi, hhost⟩ := host_get_of S.wireTy hk hwk
    have hp2 : l.host[e.1.val - l.wire.length].2 = pT := by rw [hhost]
    have hfid : l.fid e.1.val = ⟨e.1.val - l.wire.length⟩ := by
      simp only [HLinked2.fid, hwk, ↓reduceIte]
    have hst' : (E3 P).status y₁.1 y₁.2 =
        .callout (.lowered ⟨e.1.val - l.wire.length⟩ (witFt pT) {} ⟨2⟩) ys := by
      rw [← hfid]
      exact hst
    have hge : l.wire.length ≤ (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val :=
      Nat.le_of_not_lt hwk
    have hnn : (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val =
        l.wire.length + (⟨e.1.val - l.wire.length, hi⟩ : Fin l.host.length).val := by
      show e.1.val = l.wire.length + (e.1.val - l.wire.length)
      omega
    have hst'' : (E3 P).status y₁.1 y₁.2 = .callout (.lowered ⟨e.1.val - l.wire.length⟩
        (witFt l.host[e.1.val - l.wire.length].2) {} ⟨2⟩) ys := by
      rw [hp2]
      exact hst'
    have hys'' : ys.map (·.type) = ValTy.flatList l.host[e.1.val - l.wire.length].2.params := by
      rw [hp2]
      exact hyty
    have hHk := hH ιe SL CL TL HL C h y₁ _ hi ys hst'' hys''
    cases hws : liftArgs pT.params ys with
    | none =>
      exact absurd hdn (TrapsFrom.not_diverges (TrapsAtSH.trapsFromH (hHk.1 (by rw [hp2]; exact hws))))
    | some ws =>
      have hHw := hHk.2 ws (by rw [hp2]; exact hws)
      cases hg : g h ⟨e.1.val - l.wire.length⟩ (ws.map toRefVal) with
      | none => exact absurd hdn (TrapsFrom.not_diverges (TrapsAtSH.trapsFromH (hHw.1 hg)))
      | some rs₁ =>
        obtain ⟨rs₁, s₁⟩ := rs₁
        obtain ⟨us, rfl, hck⟩ := hT h _ hi ws rs₁ s₁ hg
        obtain ⟨xS, cS, trH, hL⟩ := hHw.2 us s₁ hg hck
        rw [hp2] at hck hL
        right; right
        have hp₂ := ht.lrun hL hn
        have hI₂ := LInv.resumeHost_fwdH S hI₁ hk hdx he' hck
        have hrel₁ := impRel_link (l := l.toL2) hk rfl rfl hm hws hck
          (.values ⟨_, resAnswerH S hk rfl hck⟩) rfl
        refine ⟨⟨e, .values ⟨_, resAnswerH S hk rfl hck⟩⟩, _, _, _, _, _, _, _, _, s₁, _,
          _, π, by simp only [List.length_cons]; omega, hp₂, hte, hI₂,
          .cons (.ucall hr₁ hco' he') (.cons (.uret _) (.nil _)), hrel₁,
          .host ⟨e.1.val - l.wire.length, hi⟩ hnn (.nil π),
          hostRun_host hge hi ⟨⟨e.1.val - l.wire.length, hi⟩, ws, rfl, hg⟩ (.nil s₁),
          .inr ⟨_, _, _, hg⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
