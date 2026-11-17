module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.RefSess
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.SessionObs.Main

/-!
# Productive executions of `HLinked2.toRef`: infinitely many terminating calls

* `hlinked2_refSessProd_of_spec`: an infinite specification session (`HLinked2.SpecSessProd`)
  from the instances' stores, its host calls answered by the logging host from `(s₀, [])`, is a
  productive execution of the reference machine with the same host-state stream: the reference
  configurations are built one call at a time (`sessH_fwd` on a one-call session, `ReadyL`
  between calls, `resumeCfg` after a trap), by dependent choice (`SessionObs.exists_stream`);
* `hlinked2_spec_of_refSessProd`: conversely, for typed calls, the given stream of reference
  configurations is read back one call at a time (`sessH_inv` on a one-call session), the
  specification stores chosen along it by dependent choice. No determinism is used: both
  directions hold at every profile.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "RVal" => Silmaril.Wasm.Component.Reference.Val
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {prof : ProfileKind}

/-! ## One-call sessions -/

section One

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type} {h : Host E σ}

theorem sessStep_of_run {m m' : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)}
    (hr : LinkedSession.SessRun prof h m k [(f, args)] [o] m') :
    SessStep prof h m k f args o m' := by
  cases hr with
  | ret hc hS =>
    cases hS
    exact .ret hc
  | trap hc hS =>
    cases hS
    exact .trap hc

theorem run_of_sessStep {m m' : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)} (hs : SessStep prof h m k f args o m') :
    LinkedSession.SessRun prof h m k [(f, args)] [o] m' := by
  cases hs with
  | ret hc => exact .ret hc (.nil _ _)
  | trap hc => exact .trap hc (.nil _ _)

end One

theorem sessSpec_one {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    {u π u' π' : Store Nat} {q : Fin l.imp.exports.length × List IVal}
    {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    (h : HLinked2.SessSpec P l Ie Ii u π [q] outs hs u' π') :
    ∃ o hc, outs = [o] ∧ hs = [hc] := by
  cases h with
  | round d _ _ _ _ h' =>
    cases h'
    exact ⟨_, _, rfl, rfl⟩

theorem flatten_one {α : Type} (x : List α) : [x].flatten = x := by simp

/-! ## Specification to reference -/

/-- **An infinite specification session is a productive execution of the reference machine**,
with the same host-state stream. -/
theorem hlinked2_refSessProd_of_spec (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (hst : ℕ → σ × List HLinked2.HostEvent) (h0 : hst 0 = (s₀, []))
    (h : HLinked2.SpecSessProd P l Ie Ii (HLinked2.logG g) a out hst) :
    HLinked2.RefSessProd P prof l g s₀ a out hst := by
  obtain ⟨u, π, hs, hu0, hπ0, hk⟩ := h
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hIe hIi
  let fid : ℕ → FuncId := fun k => ⟨l.host.length + l.exp.exports.length + (a k).1⟩
  obtain ⟨mm, hmm0, hmm⟩ := SessionObs.exists_stream
    (fun k (m : Machine.Config (core3P P) (σ × List HLinked2.HostEvent)) =>
      ∃ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
        (G : Garb P (σ × List HLinked2.HostEvent)) (ST : List Subtask),
        m = readyCfgL cs ιe ιi fs G ST (hst k) ∧
        ReadyL P l.toW Ie Ii Ie.store Ii.store F₀ cs ιe ιi G (u k) (π k) k)
    (fun k m m' => SessStep prof (answerHostS P (HLinked2.logG g)) m k (fid k)
      ((a k).2.map toRefVal) ((out k).map (List.map toRefVal)) m' ∧ m.host = hst k)
    (x₀ := readyCfgL cs {} {} fs Garb.empty [] (s₀, []))
    ⟨cs, {}, {}, Garb.empty, [], by rw [h0], by rw [hu0, hπ0]; exact R₀⟩
    (by
      rintro k _ ⟨cs₁, ιe, ιi, G, ST, rfl, R⟩
      obtain ⟨hsp, hhr⟩ := hk k
      obtain ⟨cs', ιe', ιi', G', ST', hsr, R'⟩ := sessH_fwd (prof := prof)
        (impl := answerImplS (HLinked2.logG g))
        (handles_answer hl.impArity hl.impFloatFree hl.wireTy) (HostTyped.logG hT) S₀ rfl hfs
        hsp cs₁ ιe ιi G ST (hst k) k (hst (k + 1)) R (by rw [flatten_one]; exact hhr)
      exact ⟨_, ⟨sessStep_of_run hsr, rfl⟩, cs', ιe', ιi', G', ST', rfl, R'⟩)
  refine ⟨_, ⟨0⟩, l.exportMap, fid, mm, hmem, fun k => exportMapH_lookup hl.impGood (a k).1,
    ⟨hmm0, fun k => (hmm k).1⟩, fun k => (hmm k).2⟩

/-! ## Reference to specification -/

/-- **A productive execution of the reference machine is an infinite specification session**,
for typed calls, with the same host-state stream starting at `(s₀, [])`. -/
theorem hlinked2_spec_of_refSessProd (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true)
    (hst : ℕ → σ × List HLinked2.HostEvent)
    (h : HLinked2.RefSessProd P prof l g s₀ a out hst) :
    hst 0 = (s₀, []) ∧ ∃ Ie Ii : Silmaril.Wasm.Game.ScalarInstance,
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      HLinked2.SpecSessProd P l Ie Ii (HLinked2.logG g) a out hst := by
  obtain ⟨m₀, inst, es, fs', mm, hr, hlk, hx, hhost⟩ := h
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := P) hl.expGood hl.expInst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hFe.isInst hIi
  obtain ⟨mU, -, -, -, huniq⟩ :=
    hlinked2_instantiates P prof hl (answerHostS P (HLinked2.logG g)) (s₀, [])
  have h₁ := huniq _ hmem
  have h₂ := huniq _ hr
  simp only [InstResult.instance.injEq] at h₁ h₂
  obtain ⟨rfl, rfl, rfl⟩ := h₂
  have hm₀ : mm 0 = readyCfgL cs {} {} fs Garb.empty [] (s₀, []) := hx.zero.trans h₁.1.symm
  have hfid : ∀ k, fs' k = ⟨l.host.length + l.exp.exports.length + (a k).1⟩ := fun k =>
    Option.some.inj ((hlk k).symm.trans (exportMapH_lookup hl.impGood (a k).1))
  refine ⟨(hhost 0).symm.trans (by rw [hm₀]; rfl), Ie, Ii, hFe.isInst, hIi, ?_⟩
  obtain ⟨st, hst0, hstep⟩ := SessionObs.exists_stream
    (fun k (x : Store Nat × Store Nat) =>
      ∃ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
        (G : Garb P (σ × List HLinked2.HostEvent)) (ST : List Subtask),
        mm k = readyCfgL cs ιe ιi fs G ST (mm k).host ∧
        ReadyL P l.toW Ie Ii Ie.store Ii.store F₀ cs ιe ιi G x.1 x.2 k)
    (fun k x y => ∃ hc : List (Σ _ : (sigN l.host.length).Op, Option Payload),
      HLinked2.SessSpec P l Ie Ii x.1 x.2 [a k] [out k] [hc] y.1 y.2 ∧
        HostRun (HLinked2.logG g) (hst k) hc (hst (k + 1)))
    (x₀ := (Ii.store, Ie.store))
    ⟨cs, {}, {}, Garb.empty, [], by rw [hm₀]; rfl, R₀⟩
    (by
      rintro k x ⟨cs₁, ιe, ιi, G, ST, hmk, R⟩
      have hrun := run_of_sessStep (hx.step k)
      rw [hmk, hfid k] at hrun
      have hrun' : LinkedSession.SessRun prof (linkHost (answerImplS (HLinked2.logG g)))
          (readyCfgL cs₁ ιe ιi fs G ST (mm k).host) k (callArgsH l [a k]) (refOuts [out k])
          (mm (k + 1)) := hrun
      obtain ⟨outs', hc, u', π', hspec, hhr, ho', cs', ιe', ιi', G', ST', hmE, R'⟩ :=
        sessH_inv (prof := prof) (impl := answerImplS (HLinked2.logG g))
          (handlesB_answer hl.impArity hl.impFloatFree hl.wireTy) (HostTyped.logG hT) S₀
          rfl hfs [a k] cs₁ ιe ιi G ST (mm k).host x.1 x.2 k _ (mm (k + 1)) R
          (fun q hq => by
            simp only [List.mem_singleton] at hq
            subst hq
            exact ht k) hrun'
      obtain rfl := SessionAdequacy.refOuts_inj ho'
      obtain ⟨o, hc₁, ho, rfl⟩ := sessSpec_one hspec
      refine ⟨(u', π'), ⟨hc₁, hspec, ?_⟩, cs', ιe', ιi', G', ST', hmE, R'⟩
      rw [← hhost k, ← hhost (k + 1)]
      simpa only [flatten_one] using hhr)
  refine ⟨fun k => (st k).1, fun k => (st k).2, fun k => Classical.choose (hstep k),
    by simp only [hst0], by simp only [hst0], fun k => Classical.choose_spec (hstep k)⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf
