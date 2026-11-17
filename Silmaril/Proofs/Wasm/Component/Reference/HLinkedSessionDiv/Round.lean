module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Call
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Round
public import Silmaril.Wasm.Component.Reference.HLinkedSessionDiv.Defs

/-!
# Diverging calls of `HLinked2.toRef`: quiet divergence and prefixes of rounds

* `coreCfg_quietDiverges`: an infinite core run of a core activation is a quiet divergence of
  the machine in the host state of its frame, one core step per segment;
* `quietDiverges_of_segs`: configurations in host state `st` from which nonempty runs without
  host events always reach such a configuration again diverge quietly in `st`;
* `steps_callQuiet`: a finite run without host events after the invocation, then quiet
  divergence, is a quietly diverging call;
* `roundsPre_fwdH`: the prefix variant of `rounds_fwdH` (and the `HLinked2` counterpart of
  `LinkedSessionDiv.roundsPre_fwd`). A path of the importer's instance from `.running f` along
  `callMoves rs` to `.running f s t`, whose component import calls are an `ExpRunH` segment
  (wired calls answered by the exporter) and whose host calls are answered by the host as `g`
  prescribes (`HostRun g`, `HostHandles`), is a quiet run of the machine between `extG`
  extensions of the call's frame, from host state `h` to the host state `h'` at the end of the
  `HostRun`, with `LInv` at its end; unless an import call was answered by a trap, in which case
  the importer's part is `Doomed` at `(s, t)`. The run is nonempty when the prefix makes a wired
  call (`rs = [] ∨ tr ≠ [] ∨` a host call).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

/-! ## Quiet divergence -/

section Quiet

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- **An infinite core run is a quiet divergence** of its core activation, in the host state of
the frame. -/
theorem coreCfg_quietDiverges {B : Machine.Config E σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} (h : Silmaril.InfiniteTrace (CoreStep E) x) :
    QuietDiverges prof hr dispatch B.host (coreCfg B th K segs rest x) :=
  Silmaril.InfiniteTrace.map (coreCfg B th K segs rest) (fun a b hab => by
    obtain ⟨hst, hi⟩ := hab
    refine ⟨rfl, rfl, [.core], .cons (Step.coreInternal rfl hst hi) (.refl _), by simp, ?_⟩
    intro ev hm
    simp at hm) h

/-- **Productive quiet segments diverge quietly**: if from every configuration of `Q`, all in
host state `st`, a nonempty run without host events reaches `Q` again, every configuration of
`Q` diverges quietly in `st`. -/
theorem quietDiverges_of_segs (Q : Machine.Config E σ → Prop) (st : σ)
    (hst : ∀ m, Q m → m.host = st)
    (h : ∀ m, Q m → ∃ tr m', Steps prof hr dispatch m tr m' ∧ tr ≠ [] ∧
      (∀ ev, Label.host ev ∉ tr) ∧ Q m')
    {m : Machine.Config E σ} (hm : Q m) : QuietDiverges prof hr dispatch st m := by
  refine Silmaril.InfiniteTrace.coinduct Q (fun m hm => ?_) hm
  obtain ⟨tr, m', r, hne, hq, hm'⟩ := h m hm
  exact ⟨m', ⟨hst m hm, hst m' hm', tr, r, hne, hq⟩, hm'⟩

/-- A finite run without host events extends the run before a quiet divergence. -/
theorem steps_quiet_append {m₁ m₂ m₃ : Machine.Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : Steps prof hr dispatch m₁ tr₁ m₂) (hq₁ : ∀ ev, Label.host ev ∉ tr₁)
    (h₂ : Steps prof hr dispatch m₂ tr₂ m₃) (hq₂ : ∀ ev, Label.host ev ∉ tr₂) :
    Steps prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ ∧ ∀ ev, Label.host ev ∉ tr₁ ++ tr₂ :=
  ⟨Adequacy.steps_append h₁ h₂, fun ev hm =>
    (List.mem_append.mp hm).elim (hq₁ ev) (hq₂ ev)⟩

end Quiet

/-! ## Prefixes of rounds -/

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

section Rounds

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

/-- **A prefix of a specification round with host calls answered is a quiet run of the
machine** between `extG` extensions of the call's frame, from host state `h` to the host state
`h'` at the end of the `HostRun`, `LInv` holding at its end; or the importer's part is doomed (an
import call was answered by a trap). -/
theorem roundsPre_fwdH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandles prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g) :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (π π₁ s₁ : Store Nat) (t₁ : STh)
      (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
      (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
      (C : List (Option (Activation (E3 P) σ))) (h h' : σ),
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rs dss →
      HLinked2.ExpRunH P l Ie π dss.flatten π₁ →
      HostRun g h (l.hostCalls dss.flatten) h' →
      Ii.Path P (.running f x.1 x.2) (callMoves rs) (.running f s₁ t₁) →
      ThreadsOk ιe →
      (∃ (ιe' : InstState) (SL' : List Subtask) (CL' : List (Caller (E3 P)))
          (TL' : List (Runtime.Task (E3 P))) (HL' : List Runtime.Thread)
          (C' : List (Option (Activation (E3 P) σ))) (tr : List (Label (E3 P) σ))
          (yc : CoreSt (E3 P)),
        ThreadsOk ιe' ∧ Quiet tr ∧ (rs = [] ∨ tr ≠ [] ∨ l.hostCalls dss.flatten ≠ []) ∧
        Steps prof (fun _ _ => false) (DI P impl)
          (coreCfg (extG M₀ ιe SL CL TL HL C h) th K segs rest y) tr
          (coreCfg (extG M₀ ιe' SL' CL' TL' HL' C' h') th K segs rest yc) ∧
        LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f yc (s₁, t₁) π₁) ∨
      Doomed s₁ t₁
  | [], dss, y, x, π, π₁, s₁, t₁, ιe, SL, CL, TL, HL, C, h, h', hI, hrel, hexp, hhr, hpath,
      hte => by
    cases hrel
    cases hexp
    obtain rfl := hostRun_nil hhr
    cases hpath
    exact .inl ⟨ιe, SL, CL, TL, HL, C, [], y, hte, Quiet.nil, .inl rfl, .refl _, hI⟩
  | ⟨e, v⟩ :: rs, dss₀, y, x, π, π₁, s₁, t₁, ιe, SL, CL, TL, HL, C, h, h', hI, hrel, hexp, hhr,
      hpath, hte => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss, Silmaril.Wasm.Component.Reference.ImpRel
        l.imp Ii ⟨e, v⟩ ds ∧ List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii)
          rs dss ∧ dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs)
      (by simpa [callMoves] using hpath)
    -- after a trapped import call the thread is doomed
    have hdoom : v = .trap → Doomed s₁ t₁ := by
      intro hv
      subst hv
      cases rs with
      | nil =>
        cases hpath'
        exact doomed_resume co
      | cons r rs =>
        obtain ⟨e', v'⟩ := r
        exact (doomed_no_ask (doomed_resume co) hpath').elim
    obtain ⟨y₁, hy₁, hI₁⟩ := LInv.reach_fwdH S hI run
    obtain ⟨tr₁, htr₁, r₁⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := extG M₀ ιe SL CL TL HL C h) (th := th) (K := K)
      (segs := segs) (rest := rest) hy₁
    have hq₁ : Quiet tr₁ := Quiet.of_core htr₁
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
    · -- the arguments do not lift
      obtain ⟨rfl, rfl⟩ := hm
      exact .inr (hdoom hA.symm)
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      have hexp' : HLinked2.ExpRunH P l Ie π
          (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) π₁ := by
        simpa only [List.flatten_cons, List.singleton_append] using hexp
      have hhr₀ : HostRun g h
          (l.hostCalls (⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten)) h' := by
        simpa only [List.flatten_cons, List.singleton_append] using hhr
      have hflat : ([⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩] ::
          dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))).flatten =
          ⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten := by
        simp only [List.flatten_cons, List.singleton_append]
      by_cases hwk : k < l.wire.length
      · -- a wired call
        have hhr' : HostRun g h (l.hostCalls dss.flatten) h' := by
          rwa [hostCalls_cons_wired (by simpa [hek.1] using hwk)] at hhr₀
        obtain ⟨wi, hw⟩ : ∃ wi, l.wire[k]? = some wi := ⟨_, List.getElem?_eq_getElem hwk⟩
        obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty k wi hw
        have hpx : xe.ty = ft := by
          rw [hk] at hty
          simp only [Option.map_some, Option.some.injEq] at hty
          exact hty.symm
        subst hpx
        have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
        have hres : xe.ty.results.length ≤ 1 := (S.arity.2 _ hmi).2.2
        have hfl : ArenaField.funcs.get? M₀.store (l.fid k) =
            some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
          S.lifted k wi xe hw hxe
        have hsite : LinkSite M₀ y₁ (.lowered (l.fid k) (witFt xe.ty) {} ⟨2⟩) ys :=
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
          obtain ⟨ιe₂, SL₂, CL₂, TL₂, HL₂, C₂, tr₂, hte₂, hq₂, hne₂, r₂⟩ :=
            nest_retG (prof := prof) (impl := impl) (K := K) (segs := segs) (rest := rest)
              (SL := SL) (CL := CL) (TL := TL) (HL := HL) (C := C) (s := h) hF hte hst hfl hres
              hsite hws hrunA hstA husA
          rcases roundsPre_fwdH S hF hH hT rs dss _ _ _ π₁ s₁ t₁ ιe₂ SL₂ CL₂ TL₂ HL₂ C₂ h h' hI₂
              hrel' hrest hhr' hpath' hte₂ with
            ⟨ιe', SL', CL', TL', HL', C', tr₃, yc, hte', hq₃, -, r₃, hIc⟩ | hdm
          · refine .inl ⟨ιe', SL', CL', TL', HL', C', tr₁ ++ (tr₂ ++ tr₃), yc, hte',
              hq₁.append (hq₂.append hq₃), .inr (.inl (by simp [hne₂])), ?_, hIc⟩
            exact Adequacy.steps_append r₁ (Adequacy.steps_append r₂ r₃)
          · exact .inr hdm
        | trap w₂ hwire hTr hrest =>
          exact .inr (hdoom (by rw [← hA', hAR]; rfl))
        | host i hn hrest =>
          have h1 := hek.1
          simp only at hn
          omega
      · -- a host call
        obtain ⟨hi, hhost⟩ := host_get_of S.wireTy hk hwk
        have hfid : l.fid k = ⟨k - l.wire.length⟩ := by
          simp only [HLinked2.fid, hwk, ↓reduceIte]
        have hst' : (E3 P).status y₁.1 y₁.2 = .callout (.lowered ⟨k - l.wire.length⟩
            (witFt l.host[k - l.wire.length].2) {} ⟨2⟩) ys := by
          rw [hhost, ← hfid]
          exact hst
        have hys' : ys.map (·.type) = ValTy.flatList l.host[k - l.wire.length].2.params := by
          rw [hhost]
          exact hyty
        have hws' : liftArgs l.host[k - l.wire.length].2.params ys = some ws := by
          rw [hhost]
          exact hws
        have hHk := (hH ιe SL CL TL HL C h y₁ _ hi ys hst' hys').2 ws hws'
        have hrest : HLinked2.ExpRunH P l Ie π dss.flatten π₁ := by
          cases hexp' with
          | ret w₂ hwire _ _ =>
            exfalso
            have hge : l.wire.length ≤ e.1.val := by omega
            rw [List.getElem?_eq_none hge] at hwire
            cases hwire
          | trap w₂ hwire _ _ =>
            exfalso
            have hge : l.wire.length ≤ e.1.val := by omega
            rw [List.getElem?_eq_none hge] at hwire
            cases hwire
          | host _ _ hrest => exact hrest
        have hwl : l.wire.length ≤ (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val := by
          simp only [hek.1]
          omega
        have hil : (⟨e.1.val, hkl⟩ : Fin l.imp.imports.length).val - l.wire.length <
            l.host.length := by
          simp only [hek.1]
          exact hi
        have hhc := hostCalls_cons_host (d := ⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩)
          (ds := dss.flatten) hwl hil
        have hne : l.hostCalls ([⟨(⟨e.1.val, hkl⟩, .vals ws), R⟩] :: dss).flatten ≠ [] := by
          rw [hflat, hhc]
          exact List.cons_ne_nil _ _
        rw [hhc] at hhr₀
        obtain ⟨h₁, hd₁, hhr'⟩ : ∃ h₁, HostAnswersS g h
            (⟨(⟨e.1.val - l.wire.length, hil⟩, .vals ws), R⟩ :
              Σ _ : (sigN l.host.length).Op, Option Payload) h₁ ∧
            HostRun g h₁ (l.hostCalls dss.flatten) h' := by
          cases hhr₀ with
          | cons hd₁ hhr' => exact ⟨_, hd₁, hhr'⟩
        obtain ⟨k', ws', hkw, hans⟩ := hd₁
        simp only [Prod.mk.injEq, Payload.vals.injEq] at hkw
        obtain ⟨rfl, rfl⟩ := hkw
        have hik : e.1.val - l.wire.length = k - l.wire.length := by rw [hek.1]
        cases R with
        | none =>
          exact .inr (hdoom (by rw [← hA', hAR]; rfl))
        | some A₀ =>
          cases A₀ with
          | flat _ => exact hans.elim
          | vals us =>
            have hg : g h ⟨k - l.wire.length⟩ (ws.map toRefVal) = some (us.map toRefVal, h₁) := by
              simpa only [hik] using hans
            obtain ⟨us', hus', hck'⟩ := hT h _ hi ws _ h₁ hg
            obtain rfl := map_toRefVal_inj hus'
            have hcheck : ValTy.checkList ft.results us = true := by
              rw [hhost] at hck'
              exact hck'
            have hv : Silmaril.Wasm.Game.Answer.toResult v =
                .values ((lowerArgs ft.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
              rw [← hA', hAR]
              have hup : (some (Payload.vals us)).bind
                  (Silmaril.Wasm.Component.Adapter.lower ft).up =
                  some (.flat (lowerArgs ft.results us)) := by
                simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
                  Silmaril.Wasm.Component.checkLower, hcheck, ite_true, Option.map_some]
              rw [hup, payloadAnswer_flat (w := .values ⟨_, resAnswerH S hk hek.1 hcheck⟩) rfl]
              rfl
            rw [hv] at hpath'
            have hI₂ := LInv.resumeHost_fwdH S hI₁ hk hdx op hcheck
            obtain ⟨xS, cS, tr₂, hq₂, r₂⟩ := hHk.2 us h₁ hg (by rw [hhost]; exact hcheck)
            rw [hhost] at r₂
            rcases roundsPre_fwdH S hF hH hT rs dss _ _ _ π₁ s₁ t₁ ιe (SL ++ [xS]) (CL ++ [cS])
                TL HL C h₁ h' hI₂ hrel' hrest hhr' hpath' hte with
              ⟨ιe', SL', CL', TL', HL', C', tr₃, yc, hte', hq₃, -, r₃, hIc⟩ | hdm
            · exact .inl ⟨ιe', SL', CL', TL', HL', C', tr₁ ++ (tr₂ ++ tr₃), yc, hte',
                hq₁.append (hq₂.append hq₃), .inr (.inr hne),
                Adequacy.steps_append r₁ (Adequacy.steps_append r₂ r₃), hIc⟩
            · exact .inr hdm

end Rounds

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
