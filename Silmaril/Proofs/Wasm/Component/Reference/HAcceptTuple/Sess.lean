module

public import Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple.Inst
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Thms

/-!
# The `tuple<u8, u8>` acceptor: the session `run`

* `run_path`: the core instance's play of `run`. Its import call `accept(104, 105)` is
  answered with no results, and `run` returns, at every profile.
* `accept_impRel`: that core import call is the component import call
  `accept(record [u8 104, u8 105])`, answered with no results, through `canon lower`.
* `tupleL_sessSpec`: the specification session `[run]`, its host call recorded.
* `tupleL_ir_session`: its IR play (`HLinked2.sess_specToIR`).
* `tupleL_hostRun`: the logging host of `acceptG` answers that host call and logs it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HAcceptTuple
open Silmaril.Wasm.Component.Reference.LinkedSession (setGetS unitTy)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- The core arguments of the import call. -/
abbrev acceptArgs : List Silmaril.Wasm.Execution.Core.Val := [.i32 104, .i32 105]

/-- The export question `run()`. -/
def runQ : tcInst.F.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- The import question `accept(104, 105)`. -/
def acceptE : tcInst.E.Op := ⟨⟨0, by decide⟩, ⟨acceptArgs, .cons ⟨104, rfl⟩ (.cons ⟨105, rfl⟩ .nil)⟩⟩

/-- The answer of `accept`: no results. -/
def acceptAI : tcInst.E.Ar acceptE := .values ⟨[], .nil⟩

/-- The answer of `run`: no results. -/
def runAO : tcInst.F.Ar runQ := .values ⟨[], .nil⟩

theorem accept_importOp : tcInst.importOp? 0 acceptArgs = some acceptE := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · exact absurd acceptE.2.2 ‹_›
  · exact absurd (show 0 < tcInst.imports.length by decide) ‹_›

/-- **`run` reaches its import call `accept(104, 105)`**, host-free, the store unchanged. -/
theorem run_callout (P : Profile) {fr fh : FuncInst Nat}
    (hf : tcStore.funcs[1]? = some fr) (he : Expand fr.type unitFn.toComp)
    (hc : isRun 0 fr = true) (hfh : tcStore.funcs[0]? = some fh)
    (heh : Expand fh.type pairFn.toComp) (hcode : fh.code = .host 0) :
    ∃ (t : Thread) (F : Frame), Reach P (tcStore, .pending 1 []) (tcStore, t) ∧
      decompose? tcStore (t.config tcStore).code =
        some (ppCtx (Ty.ofList (unitFn.results.map ScalarType.toC)).length F, 0, 0,
          acceptArgs) ∧
      (t.config tcStore).frame = {} := by
  obtain ⟨code, x, hcode', hloc, hbody, hx, hm⟩ := isRun_code hc
  let F := Frame.forCall fr.module [] code.locals
  let n := (Ty.ofList (unitFn.results.map ScalarType.toC)).length
  have hn : ([] : List Silmaril.Wasm.Execution.Core.Val).length =
      (Ty.ofList (unitFn.params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList]
    rfl
  have s₁ : Step P Det.noHost (invoke tcStore 1 [])
      ⟨tcStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he hn hcode'
  have hxF : F.module.funcs[x.toNat]? = some 0 := by rw [hx]; exact hm
  have s₂ : Steps P Det.noHost ⟨tcStore, F, expression code.body⟩
      ⟨tcStore, F, vals acceptArgs ++ [.ref (.func 0), .callRefType fh.type]⟩ := by
    rw [hbody]
    have h := Step.ctxtInstrs (P := P) (host := Det.noHost) (vs := acceptArgs) (rest := [])
      (Step.call hxF hfh) (.inl (by simp))
    simp only [List.append_nil] at h
    exact .single h
  have run : Steps P Det.noHost ((Thread.pending 1 []).config tcStore)
      ⟨tcStore, {}, (ppCtx n F).fill (vals acceptArgs ++ [.ref (.func 0), .callRefType fh.type])⟩ :=
    (Relation.ReflTransGen.single s₁).trans (Litmus.steps_frame_label s₂)
  obtain ⟨s₁', t₁, hr₁, hd₁⟩ := Litmus.reach_of_steps run
  have hs₁ : s₁' = tcStore := by
    have h₁ : (t₁.config s₁').store = s₁' := by cases t₁ <;> rfl
    rw [← h₁, hd₁]
  subst hs₁
  have hn' : acceptArgs.length = (Ty.ofList (pairFn.params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList]
    rfl
  refine ⟨t₁, F, hr₁, ?_, by rw [hd₁]⟩
  rw [hd₁]
  exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ trivial hfh heh hn' hcode

/-- **`run` with its import call `accept(104, 105)` answered** returns, for every profile. -/
theorem run_path (P : Profile) :
    tcInst.Path P (.idle tcInst.store)
      (.inr (.ask runQ) :: callMoves [⟨acceptE, acceptAI⟩] ++ [.inr (.ans runQ runAO)])
      (.idle tcStore) := by
  obtain ⟨_, ⟨h₀, fr, hfuncs, i₀, ir⟩⟩ := tcFacts
  simp only [tcInfo, Prod.mk.injEq] at i₀ ir
  have hf1 : tcStore.funcs[1]? = some fr := by rw [hfuncs]; rfl
  have hf0 : tcStore.funcs[0]? = some h₀ := by rw [hfuncs]; rfl
  obtain ⟨t, F, hr, hd, hfr⟩ := run_callout P hf1 (FnType.expand_of_ofDefType? ir.1) ir.2.2
    hf0 (FnType.expand_of_ofDefType? i₀.1) (isHost_code i₀.2.1)
  let n := (Ty.ofList (unitFn.results.map ScalarType.toC)).length
  have hn : ([] : List Silmaril.Wasm.Execution.Core.Val).length = n := (Ty.length_ofList (unitFn.results.map ScalarType.toC)).symm
  have hres : resumeResult tcStore t (Answer.toResult acceptAI) =
      .active {} [.frame n F [.label n [] (vals [])]] := by
    unfold resumeResult
    simp only [hd, hfr]
    rfl
  have run₂ : Steps P Det.noHost
      ((Thread.active {} [.frame n F [.label n [] (vals [])]]).config tcStore)
      ⟨tcStore, {}, vals []⟩ :=
    (Relation.ReflTransGen.single (.ctxtFrame .labelVals)).tail (.frameVals hn)
  obtain ⟨s₂', t₂, hr₂, hd₂⟩ := Litmus.reach_of_steps run₂
  have hs₂ : s₂' = tcStore := by
    have h₂ : (t₂.config s₂').store = s₂' := by cases t₂ <;> rfl
    rw [← h₂, hd₂]
  subst hs₂
  have hfin : ResultAt tcStore t₂ (.values []) := by
    show (t₂.config tcStore).code = _
    rw [hd₂]
    rfl
  have hans : Answer.ofResult? (tcInst.exports.get runQ.1) (.values []) = some runAO := by
    unfold Answer.ofResult?
    exact dite_eq_left .nil
  refine .cons (.call _ _) (.cons (.ucall hr ⟨_, _, hd⟩ accept_importOp)
    (.cons (.uret acceptAI) ?_))
  rw [hres]
  exact .cons (.oret hr₂ hfin hans) (.nil _)

/-- The component import call: `accept(record [u8 104, u8 105])`, answered with no results. -/
def acceptD : Σ _ : (sigN tupleL.imp.imports.length).Op, Option Payload :=
  ⟨(⟨0, by decide⟩, .vals [.record [.u8 104, .u8 105]]), some (.vals [])⟩

/-- **The core import call is the component import call** through `canon lower`: the flat
arguments `104, 105` lift to `record [u8 104, u8 105]`, and the empty answer lowers back. -/
theorem accept_impRel : Silmaril.Wasm.Component.Reference.ImpRel tupleI tcInst ⟨acceptE, acceptAI⟩ [acceptD] :=
by
  refine ⟨"accept", acceptTy, some (.flat []), rfl, ?_, ?_⟩
  · show payloadAnswer (tcInst.imports.get acceptE.1) (some (.flat [])) = acceptAI
    have ht : typed? (tcInst.imports.get acceptE.1).results (([] : List Flat).map ofFlat) =
        some ⟨[], .nil⟩ := by
      unfold typed?
      exact dite_eq_left .nil
    unfold payloadAnswer
    dsimp only
    erw [ht]
    rfl
  · exact ⟨show 0 < 1 by decide, _, rfl, rfl⟩

/-- The session round `run()`. -/
def runR : Linked2.SessRound tupleL.toL2 tcInst where
  j := ⟨0, by decide⟩
  vs := []
  f := runQ
  cs := [⟨acceptE, acceptAI⟩]
  w := runAO
  dss := [[acceptD]]

theorem runR_ok : runR.Ok := ⟨[], rfl, rfl, rfl, .cons accept_impRel .nil⟩

/-- The host call of the round, at the host interface. -/
def acceptH : Σ _ : (sigN tupleL.host.length).Op, Option Payload :=
  ⟨(⟨0, by decide⟩, .vals [.record [.u8 104, .u8 105]]), some (.vals [])⟩

theorem hostCalls_run : tupleL.hostCalls [acceptD] = [acceptH] := rfl

/-- **The specification session `[run]`**, for every profile: `run` returns, after the host call
`accept(record [u8 104, u8 105])` answered with no results. -/
theorem tupleL_sessSpec (P : Profile) :
    HLinked2.SessSpec P tupleL sgInst tcInst tcInst.store sgInst.store [(⟨0, by decide⟩, [])]
      [some []] [[acceptH]] tcStore sgInst.store :=
  hostCalls_run ▸ .round runR runR_ok (run_path P)
    (.host ⟨0, by decide⟩ rfl (.nil _)) rfl (.nil _ _)

/-- **The IR play of the session `[run]`**, for every profile. -/
theorem tupleL_ir_session (P : Profile) :
    tupleL.sessMoves [(⟨0, by decide⟩, [])] [some []] [[acceptH]] ∈
      tupleL.toComp.den (impSem P) :=
  HLinked2.sess_specToIR setGetS_good tupleI_good sg_isInst tc_isInst (tupleL_sessSpec P)

/-- **The logging host of `acceptG` answers the host call and logs it.** -/
theorem tupleL_hostRun :
    HostRun (HLinked2.logG acceptG) ((), []) [acceptH]
      ((), [(⟨0⟩, [toRefVal (.record [.u8 104, .u8 105])], [])]) :=
  .cons ⟨⟨0, by decide⟩, [.record [.u8 104, .u8 105]], rfl, rfl⟩ (.nil _)

end Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple
