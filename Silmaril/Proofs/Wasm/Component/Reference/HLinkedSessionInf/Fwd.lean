module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.Run
public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SessionObs.Main
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Call

/-!
# Calls with infinitely many host calls, forward

* `hchatter_segs`: from the importer's core activation in an `extG` extension of the call's frame
  in host state `hst 0`, `LInv` (at `l.toW`) relating it to the importer's part and the exporter's
  store, an infinite sequence of served import calls (the wired ones answered by A, the host ones
  answered as `g` answers from `hst k` to `hst (k + 1)`) is an infinite sequence of runs without
  host events between core activations in the host states `hst k` (`roundsPre_fwdH` on one call
  at a time, as `chatter_coreH` for wired chatter);
* `linkHProd_fwd`: from a configuration between calls (`ReadyL`), a round making infinitely many
  import calls (`HLinked2.RoundInf`) whose host state changes infinitely often is the host's
  invocation followed by an explicit infinite run of internal steps meeting every host state
  `hst k`, at unboundedly late positions (`segs_compress`, `irun_of_segs`, `irun_prepend`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

section Chatter

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

/-- **Served import calls, forever, are runs without host events between core activations**, in
the host states of the calls. -/
theorem hchatter_segs (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandles prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g)
    {q : ℕ → Ii.HState} {c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds : ℕ → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    {πs : ℕ → Store Nat} {hst : ℕ → σ}
    (hc : ∀ k, Ii.Path P (q k) (callMoves [c k]) (q (k + 1)) ∧
      Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii (c k) (ds k) ∧
      HLinked2.ExpRunH P l Ie (πs k) (ds k) (πs (k + 1)) ∧
      HostRun g (hst k) (l.hostCalls (ds k)) (hst (k + 1)))
    {y : CoreSt (E3 P)} {x : Store Nat × STh} (hq0 : q 0 = .running f x.1 x.2)
    (hI : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x (πs 0))
    {ιe : InstState} (hte : ThreadsOk ιe) (SL : List Subtask) (CL : List (Caller (E3 P)))
    (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
    (C : List (Option (Activation (E3 P) σ))) :
    ∃ cf : ℕ → Machine.Config (E3 P) σ,
      cf 0 = coreCfg (extG M₀ ιe SL CL TL HL C (hst 0)) th K segs rest y ∧
      ∀ k, (cf k).host = hst k ∧ ∃ tr, Steps prof (fun _ _ => false) (DI P impl) (cf k) tr
        (cf (k + 1)) ∧ ∀ ev, Label.host ev ∉ tr := by
  obtain ⟨cf, h0, hcf⟩ := SessionObs.exists_stream
    (fun k (m : Machine.Config (E3 P) σ) => ∃ (y : CoreSt (E3 P)) (x : Store Nat × STh)
      (ιe : InstState) (SL : List Subtask) (CL : List (Caller (E3 P)))
      (TL : List (Runtime.Task (E3 P))) (HL : List Runtime.Thread)
      (C : List (Option (Activation (E3 P) σ))),
      m = coreCfg (extG M₀ ιe SL CL TL HL C (hst k)) th K segs rest y ∧ ThreadsOk ιe ∧
      q k = .running f x.1 x.2 ∧
      LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x (πs k))
    (fun k m m' => m.host = hst k ∧ ∃ tr, Steps prof (fun _ _ => false) (DI P impl) m tr m' ∧
      ∀ ev, Label.host ev ∉ tr)
    (x₀ := coreCfg (extG M₀ ιe SL CL TL HL C (hst 0)) th K segs rest y)
    ⟨y, x, ιe, SL, CL, TL, HL, C, rfl, hte, hq0, hI⟩
    (by
      rintro k _ ⟨y, x, ιe, SL, CL, TL, HL, C, rfl, hte, hqk, hIk⟩
      obtain ⟨hpath, hrel, hexp, hhr⟩ := hc k
      rw [hqk] at hpath
      obtain ⟨s₁, t₁, hq₁⟩ : ∃ s₁ t₁, q (k + 1) = .running f s₁ t₁ := by
        generalize q (k + 1) = q' at hpath
        obtain ⟨e, v⟩ := c k
        obtain ⟨s', t', -, -, -, -, -, hp⟩ :=
          path_round_inv (rest := []) (by simpa [callMoves] using hpath)
        cases hp
        exact ⟨_, _, rfl⟩
      rw [hq₁] at hpath
      have hexp' : HLinked2.ExpRunH P l Ie (πs k) [ds k].flatten (πs (k + 1)) := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hexp
      have hhr' : HostRun g (hst k) (l.hostCalls [ds k].flatten) (hst (k + 1)) := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hhr
      rcases roundsPre_fwdH S hF hH hT [c k] [ds k] y x (πs k) (πs (k + 1)) s₁ t₁ ιe SL CL TL HL
          C (hst k) (hst (k + 1)) hIk (.cons hrel .nil) hexp' hhr' hpath hte with
        ⟨ιe', SL', CL', TL', HL', C', tr, yc, hte', hq, -, r, hIc⟩ | hdm
      · exact ⟨_, ⟨rfl, tr, r, hq.1⟩, yc, (s₁, t₁), ιe', SL', CL', TL', HL', C', rfl, hte', hq₁,
          hIc⟩
      · have h₂ := (hc (k + 1)).1
        rw [hq₁] at h₂
        exact (doomed_no_call hdm h₂).elim)
  exact ⟨cf, h0, fun k => (hcf k)⟩

end Chatter

section Call

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **A round making infinitely many import calls, its host state changing infinitely often, is
an explicitly infinite call of the reference machine** meeting every host state of the round, at
unboundedly late positions. -/
theorem linkHProd_fwd (hHd : Handles prof P impl g l) (hT : l.HostTyped g)
    (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) {j : Fin l.imp.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {hst : ℕ → σ}
    (hd : HLinked2.RoundInf P l Ie Ii g u π h₀ j vs hst)
    (hinf : ∀ N, ∃ i, N ≤ i ∧ hst i ≠ hst (i + 1)) :
    ∃ t : ℕ → Machine.Config (E3 P) σ,
      Step prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀)
        (.host (invokeTop ⟨k⟩ ⟨l.host.length + l.exp.exports.length + j⟩ (vs.map toRefVal)))
        (t 0) ∧
      IRun prof (fun _ _ => false) (DI P impl) t ∧
      (∀ i, ∃ p, (t p).host = hst i) ∧ ∀ N, ∃ i p, N ≤ p ∧ (t p).host = hst i := by
  obtain ⟨f, xs, q, c, ds, πs, hck, hf₁, hf₂, hpath0, hπ0, hh0, hc⟩ := hd
  have hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs l.imp.exports[j].ty.params vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.host.length + l.exp.exports.length + j]? =
      some (.lifted (s₀.funcs.length + Ii.addr f.1) (liftedFt l.imp.exports[j]) {} ⟨2⟩) :=
    ha ▸ hfs j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.host.length + l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax
    hres hmaxr hrf R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hF := gframe_of hat
  have hH := hHd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hat S.hostFn
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hq0 : q 0 = .running f u (Ii.initThread f) := by
    generalize q 0 = q0 at hpath0
    cases hpath0 with
    | cons h₁ h₂ =>
      cases h₁
      cases h₂
      rfl
  have hstart : M₀ = coreCfg (extG M₀ ιe [] [] [] [] M₀.conts h₀) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) := by
    have e := hat.start
    rw [extN_eq_extG] at e
    rw [← hat.host]
    exact e
  have hlive₀ : Live M₀ := by
    rw [hat.start]
    exact coreCfg_extN_live _ _ _ _ _ _ _ _ _
  have hq₁ : Quiet tr₁ := Quiet.of_lrun hpre hlive₀
  obtain ⟨cf, hcf0, hcf⟩ := hchatter_segs (u₀ := u₀) S hF hH hT hc (x := (u, Ii.initThread f))
    hq0 (hπ0 ▸ hI₀) R.thE [] [] [] [] M₀.conts
  have hcf0' : cf 0 = M₀ := by rw [hcf0, hh0, ← hstart]
  have hseg : ∀ k, ∃ tr, Steps prof (fun _ _ => false) (DI P impl) (cf k) tr (cf (k + 1)) ∧
      ∀ ev, Label.host ev ∉ tr := fun k => (hcf k).2
  have hchg : ∀ N, ∃ i, N ≤ i ∧ cf i ≠ cf (i + 1) := by
    intro N
    obtain ⟨i, hi, hne⟩ := hinf N
    refine ⟨i, hi, fun e => hne ?_⟩
    rw [← (hcf i).1, ← (hcf (i + 1)).1, e]
  obtain ⟨φ, hφ0, hφ, hcov, -⟩ := segs_compress hseg hchg
  obtain ⟨t', ht'0, ht', hpos⟩ := irun_of_segs (c := fun k => cf (φ k)) hφ
  have hpre' := hpre.steps
  obtain ⟨t, ht0, ht, hshift⟩ := irun_prepend hpre' hq₁.1 (t' := t')
    (by rw [ht'0]; show cf (φ 0) = M₀; rw [hφ0, hcf0']) ht'
  refine ⟨t, ht0 ▸ invoke_stepL R.fresh _ _, ht, fun i => ?_, fun N => ?_⟩
  · obtain ⟨k', hk'⟩ := hcov i
    obtain ⟨p, -, hp⟩ := hpos k'
    refine ⟨tr₁.length + p, ?_⟩
    rw [hshift, hp]
    show (cf (φ k')).host = hst i
    rw [← hk']
    exact (hcf i).1
  · obtain ⟨p, hp, e⟩ := hpos N
    refine ⟨φ N, tr₁.length + p, by omega, ?_⟩
    rw [hshift, e]
    exact (hcf (φ N)).1

end Call

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf
