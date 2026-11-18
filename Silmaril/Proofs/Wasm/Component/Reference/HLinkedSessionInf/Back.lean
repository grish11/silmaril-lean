module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.Run
public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Inv

/-!
# Calls with infinitely many host calls, backward

* `lprod_classifyH`: an explicit infinite run from the importer's core activation along which a
  measure `μ` of the host state (for the logging host, the length of the log) is unbounded, and
  along which `μ` only grows, is an infinite sequence of served import calls at strictly
  increasing positions (`ldiv_roundH` at each round; B diverging host-free or A diverging inside a
  wired call would keep the host state from some position on);
* `linkHProd_inv`: from a configuration between calls (`ReadyL`, host-safe for the logging host),
  a call making infinitely many host calls (`CallHostProd`) is a specification round making
  infinitely many import calls (`HLinked2.RoundInf`) under the logging host whose logs are, at
  unboundedly late rounds, the call's log followed by unboundedly long prefixes of `ev`: along the
  run the log only grows by extension (`HostWrite`), and each round of the run lies between two
  positions of the run.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.HostWrite
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val
local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Logs as prefixes of a stream -/

section Log

variable {α : Type}

theorem length_streamTake (ev : ℕ → α) (n : ℕ) : (streamTake ev n).length = n := by
  simp [streamTake]

theorem take_streamTake (ev : ℕ → α) {a n : ℕ} (h : a ≤ n) :
    (streamTake ev n).take a = streamTake ev a := by
  apply List.ext_getElem
  · simp [length_streamTake, h]
  · intro i h₁ h₂
    simp [streamTake]

theorem prefix_streamTake {ev : ℕ → α} {C : List α} {n : ℕ} (h : C <+: streamTake ev n) :
    C = streamTake ev C.length := by
  have hl : C.length ≤ n := by
    have := h.length_le
    rwa [length_streamTake] at this
  conv_lhs => rw [List.prefix_iff_eq_take.mp h]
  rw [take_streamTake ev hl]

/-- A log between `L` and an extension of `L` by a prefix of `ev` is `L` followed by a prefix of
`ev`. -/
theorem log_form {L Y : List α} {ev : ℕ → α} {n : ℕ} (h₁ : L <+: Y)
    (h₂ : Y <+: L ++ streamTake ev n) : Y = L ++ streamTake ev (Y.length - L.length) := by
  obtain ⟨C, rfl⟩ := h₁
  have hC : C <+: streamTake ev n := (List.prefix_append_right_inj L).mp h₂
  rw [List.length_append, Nat.add_sub_cancel_left, ← prefix_streamTake hC]

end Log

/-! ## The classification -/

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

section Classify

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

/-- **The classification of a call with unbounded host measure**: an infinite sequence of served
import calls along the run. -/
theorem lprod_classifyH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandlesB prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g)
    (hex : ExitsQuietH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f)
    {t : ℕ → Machine.Config (E3 P) σ} (ht : IRun prof (fun _ _ => false) (DI P impl) t)
    (μ : σ → ℕ) (hmono : ∀ a b, a ≤ b → μ (t a).host ≤ μ (t b).host)
    (hunb : ∀ M, ∃ n, M ≤ μ (t n).host) {z₀ : DStH P σ}
    (hz₀ : DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z₀) :
    ∃ (sq : ℕ → DStH P σ) (gs : ℕ → (Σ e : Ii.E.Op, Ii.E.Ar e) ×
        List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)),
      sq 0 = z₀ ∧ ∀ k,
        (Ii.Path P (.running f (sq k).x.1 (sq k).x.2) (callMoves [(gs k).1])
            (.running f (sq (k + 1)).x.1 (sq (k + 1)).x.2) ∧
          Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii (gs k).1 (gs k).2 ∧
          HLinked2.ExpRunH P l Ie (sq k).π (gs k).2 (sq (k + 1)).π ∧
          HostRun g (sq k).h (l.hostCalls (gs k).2) (sq (k + 1)).h ∧ (sq k).p < (sq (k + 1)).p) ∧
        DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t (sq (k + 1)) := by
  -- the host state cannot stay fixed from some position on
  have hnofix : ∀ (p : ℕ) (h : σ), ¬ ∀ n, p ≤ n → (t n).host = h := by
    intro p h hc
    obtain ⟨n, hn⟩ := hunb (μ h + 1)
    have h₁ := hmono n (max n p) (le_max_left _ _)
    rw [hc _ (le_max_right _ _)] at h₁
    omega
  let T : DStH P σ → (Σ e : Ii.E.Op, Ii.E.Ar e) ×
      List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → DStH P σ → Prop :=
    fun z gz z' => (Ii.Path P (.running f z.x.1 z.x.2) (callMoves [gz.1])
        (.running f z'.x.1 z'.x.2) ∧
      Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii gz.1 gz.2 ∧
      HLinked2.ExpRunH P l Ie z.π gz.2 z'.π ∧ HostRun g z.h (l.hostCalls gz.2) z'.h ∧
      z.p < z'.p) ∧ DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z'
  have step : ∀ z, DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z →
      ∃ gz z', T z gz z' ∧ DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z' := by
    intro z hz
    rcases ldiv_roundH (u₀ := u₀) S hF hH hT hex ht hz.1 hz.2.1 hz.2.2 with h | h |
      ⟨c, ds, p', ιe', SL', CL', TL', HL', C', h', y', x', π', hpp, hp', hte', hI', hpath, hrel,
        hexp, hhr, -⟩
    · exact absurd h.2 (hnofix _ _)
    · obtain ⟨-, p₀, hc⟩ := h
      exact absurd hc (hnofix _ _)
    let z' : DStH P σ := ⟨p', y', x', π', ιe', SL', CL', TL', HL', C', h'⟩
    have hz' : DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z' := ⟨hp', hte', hI'⟩
    exact ⟨(c, ds), z', ⟨⟨hpath, hrel, hexp, hhr, hpp⟩, hz'⟩, hz'⟩
  obtain ⟨sq, gs, h0, hs⟩ := seq_of_step _ T step hz₀
  exact ⟨sq, gs, h0, hs⟩

end Classify

/-! ## One call -/

section Call

variable {σ₀ : Type} {g₀ : σ₀ → HostFuncId → List RVal → Option (List RVal × σ₀)}
variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {B₀ : Machine.Config (E3 P) (σ₀ × List HLinked2.HostEvent)}
  {fs : List (CFuncInst (core3P P))}

/-- **A call of the reference machine between calls making infinitely many host calls is a
specification round making infinitely many import calls**, under the logging host, whose logs
are, at unboundedly late rounds, the call's log followed by unboundedly long prefixes of the
call's host events. -/
theorem linkHProd_inv (hT : l.HostTyped g₀)
    (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P (σ₀ × List HLinked2.HostEvent)} {ST : List Subtask}
    {h₀ : σ₀ × List HLinked2.HostEvent} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k)
    (hsafe : CfgSafe logExt (readyCfgL cs ιe ιi fs G ST h₀)) (j : Fin l.imp.exports.length)
    {vs : List IVal} (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {ev : ℕ → HLinked2.HostEvent}
    (hd : CallHostProd prof (fun _ _ => false) (DI P (answerImplS (HLinked2.logG g₀)))
      (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩ ⟨l.host.length + l.exp.exports.length + j⟩
      (vs.map toRefVal) ev) :
    ∃ hst : ℕ → σ₀ × List HLinked2.HostEvent,
      HLinked2.RoundInf P l Ie Ii (HLinked2.logG g₀) u π h₀ j vs hst ∧
      ∀ N, ∃ n i, N ≤ n ∧ (hst i).2 = h₀.2 ++ streamTake ev n := by
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := S₀.impGood.core _ hx
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : l.imp.mod.exports[l.imp.exports[j].core] = (nm, l.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs l.imp.exports[j].ty.params vs).map (·.type) =
      l.imp.mod.exports[l.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI S₀.impInst hk hxs
  have hft' : Ii.exports.get f.1 = fnOf l.imp.exports[j].ty.flat := by rw [hft, hflat]
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.host.length + l.exp.exports.length + j]? = some (.lifted
      (s₀.funcs.length + Ii.addr f.1) (liftedFt l.imp.exports[j]) {} ⟨2⟩) := ha ▸ hfs j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS
    (impl := answerImplS (HLinked2.logG g₀)) prof cs ιe ιi fs G ST h₀ k
    (l.host.length + l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf
    R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hF := gframe_of hat
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) (u, Ii.initThread f) π :=
    linv_ready R.inv hf₂ rfl
  have hck : checkLower l.imp.exports[j].ty.params vs =
      some (lowerArgs l.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨t, s, ht, hlog⟩ := hd
  replace ht : IRun prof (fun _ _ => false) (DI P (answerImplS (HLinked2.logG g₀))) t := ht
  have e₁ := invoke_invL s
  have hstart : M₀ = coreCfg (extG M₀ ιe [] [] [] [] M₀.conts h₀) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs l.imp.exports[j].ty.params vs)) := by
    have e := hat.start
    rw [extN_eq_extG] at e
    rw [← hat.host]
    exact e
  have hp₀ := ht.lrun hpre (p := 0) e₁
  rw [hstart] at hp₀
  -- the log only grows, by extension, along the run
  have hsafe₀ : CfgSafe logExt (t 0) :=
    step_cfgSafe dispatchSafe_log s hsafe fun p e => by cases e
  have hpref : ∀ a b, a ≤ b → (t a).host.2 <+: (t b).host.2 := by
    intro a b hab
    obtain ⟨tra, ra, hha⟩ := ht.steps_le (Nat.zero_le a)
    have hsa := (steps_cfgSafe dispatchSafe_log ra hsafe₀ fun p hp => absurd hp (hha _)).1
    obtain ⟨trb, rb, hhb⟩ := ht.steps_le hab
    rcases hostChain_logExt (steps_cfgSafe dispatchSafe_log rb hsa
      fun p hp => absurd hp (hhb _)).2 with e | ⟨hp, -⟩
    · rw [e]
    · exact hp
  have hunb : ∀ M, ∃ n, M ≤ (t n).host.2.length := by
    intro M
    obtain ⟨n, p, hn, hp⟩ := hlog M
    refine ⟨p, ?_⟩
    rw [hp, List.length_append, length_streamTake]
    omega
  have hH := handlesB_answer (prof := prof) (P := P) (g := HLinked2.logG g₀) S₀.arity S₀.floats
    S₀.wireTy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hat S.hostFn
  obtain ⟨sq, gs, h0, hs⟩ := lprod_classifyH (u₀ := u₀) S hF hH (HostTyped.logG hT)
    (exitsQuietH_call (u₀ := u₀) S hat hft') ht (fun s => s.2.length)
    (fun a b hab => (hpref a b hab).length_le) hunb
    (z₀ := ⟨0 + tr₁.length, _, (u, Ii.initThread f), π, ιe, [], [], [], [], M₀.conts, h₀⟩)
    ⟨hp₀, R.thE, hI₀⟩
  have hinv : ∀ i, DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t (sq i)
    | 0 => h0 ▸ ⟨hp₀, R.thE, hI₀⟩
    | i + 1 => (hs i).2
  have hhost : ∀ i, (t (sq i).p).host = (sq i).h := fun i => by rw [(hinv i).1]; rfl
  have hpos : ∀ i, i ≤ (sq i).p := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := (hs i).1.2.2.2.2; omega
  have hm₀ : (readyCfgL cs ιe ιi fs G ST h₀).host = h₀ := rfl
  -- the log at the start of the call
  have hL : ∀ p, h₀.2 <+: (t p).host.2 := by
    intro p
    have e : (t 0).host = h₀ := by rw [e₁]; rfl
    rw [← e]
    exact hpref 0 p (Nat.zero_le p)
  refine ⟨fun i => (sq i).h, ⟨f, _, fun i => .running f (sq i).x.1 (sq i).x.2,
    fun i => (gs i).1, fun i => (gs i).2, fun i => (sq i).π, hck, hf₁, hf₂, ?_, by simp only [h0],
    by simp only [h0], fun i => ?_⟩, fun N => ?_⟩
  · show Ii.Path P (.idle u) [.inr (.ask f)] (.running f (sq 0).x.1 (sq 0).x.2)
    rw [h0]
    exact .cons (.call u f) (.nil _)
  · obtain ⟨⟨hp, hr, he, hh, -⟩, -⟩ := hs i
    exact ⟨hp, hr, he, hh⟩
  · rw [hm₀] at hlog
    obtain ⟨n, p, hn, hp⟩ := hlog N
    have h₁ : (t p).host.2 <+: (sq p).h.2 := by
      rw [← hhost p]
      exact hpref _ _ (hpos p)
    obtain ⟨n', p', hn', hp'⟩ := hlog (sq p).h.2.length
    have hY : (sq p).h.2 <+: h₀.2 ++ streamTake ev n' := by
      rcases le_total p' (sq p).p with hle | hle
      · have h₂ := hpref _ _ hle
        rw [hp', hhost p] at h₂
        have e := h₂.eq_of_length (by
          rw [List.length_append, length_streamTake]
          have := h₂.length_le
          rw [List.length_append, length_streamTake] at this
          omega)
        exact e ▸ List.prefix_refl _
      · have h₂ := hpref _ _ hle
        rwa [hp', hhost p] at h₂
    have hL' : h₀.2 <+: (sq p).h.2 := by
      have := hL (sq p).p
      rwa [hhost p] at this
    have e := log_form hL' hY
    refine ⟨(sq p).h.2.length - h₀.2.length, p, ?_, e⟩
    have := h₁.length_le
    rw [hp, List.length_append, length_streamTake] at this
    omega

end Call

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf
