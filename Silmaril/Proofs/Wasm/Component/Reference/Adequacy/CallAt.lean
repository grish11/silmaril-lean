module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiPath
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.LiftTrap

/-!
# The deterministic parts of call `k`, with specification traps

`call_at_kS` is `call_at_k` (`MultiPath`, same proof), recording in addition that the trap of
a failing lift is a specification trap (`TrapsNextS`, from `lrun_lift_trapS`): the trapping
call is then a `Calls` outcome `trap` of the reference machine.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type}

/-- From `mS`, the call traps after one live step, with a specification trap. -/
def TrapsNextS (prof : ProfileKind) (P : Profile) (mS : Machine.Config (E3 P) Unit) : Prop :=
  ∃ mT r, (∀ msg, r ≠ .internal msg) ∧ LRun prof (refHost P).hr (D P) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT)

/-- `CallAtK`, with specification traps where the IR lift fails. -/
structure CallAtKS (prof : ProfileKind) (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat)
    (x : SimpleExport) (a : (E3 P).FuncAddr) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
    (rest : List (Activation (E3 P) Unit)) : Prop where
  toCallAtK : CallAtK prof P cs ι' fs G k j x a vs M₀ th K segs rest
  trapS : ∀ (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextS prof P (retCfg M₀ th K segs rest y ys)

theorem call_at_kS (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat)
    (a : (E3 P).FuncAddr) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι'))
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtKS prof P cs ι' fs G k j x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) _ _
    unfold invokedAt
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := store₁ cs ι fs G x k (vs.map toRefVal)) ((e₁ _ rfl).trans rfl)
    have hS₁ : (store₁ cs ι fs G x k (vs.map toRefVal)).insts = [ι] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter (Gt := G.tasks) (y := task₀ x G.callers) rfl rfl rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (store₁ cs ι fs G x k (vs.map toRefVal))) = store₂ cs ι ι' fs G x k (vs.map toRefVal) :=
      enter_eq rfl rfl rfl hadd rfl
    apply LRun.store_congr (S' := store₂ cs ι ι' fs G x k (vs.map toRefVal)) (by exact e₂)
    have hS₂ : (store₂ cs ι ι' fs G x k (vs.map toRefVal)).tasks =
        G.tasks ++ [task₁ x G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := G.tasks) hS₂))
      rfl
    apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) Unit),
        RunsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lower x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    apply LRun.store_congr (S' := store₃ cs ι ι' fs G x k (vs.map toRefVal))
      (setTaskState_last (Gt := G.tasks) rfl _)
    mstep
    exact .refl _

  refine ⟨⟨rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
  · show ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
      ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
      ResolvesAt prof P _ (readyCfg y.1 (InstState.removeThread 1 ι') fs
        (nextGarb G x k j a (vs.map toRefVal) (ws.map toRefVal)))
    intro y ys ws hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (refHost P).hr (D P) (retCfg _ _ _ _ _ y ys) _ _
      apply LRun.store_congr (S' := store₃ y.1 ι ι' fs G x k (vs.map toRefVal)) rfl
      have hS₃ : (store₃ y.1 ι ι' fs G x k (vs.map toRefVal)).tasks =
          G.tasks ++ [(task₁ x G.callers ⟨G.threads.length⟩).withState .started] := rfl
      unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_some x hres hmaxr hffr hys hws _ _).choose_spec rfl
      apply RunsQ.chunk2 rfl
        (runs_return (Gt := G.tasks) (Gc := G.callers) _ hS₃ rfl rfl rfl rfl) rfl
      apply LRun.store_congr (S' := store₄ y.1 ι ι' fs G x k (vs.map toRefVal))
        (by refine setTaskState_last (Gt := G.tasks) ?_ _; rfl)
      apply RunsQ.chunk rfl
        (runs_exit (Gt := G.tasks) (Gth := G.threads)
          (y := ((task₁ x G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
          (z := (thread₁ G.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      have e₄ : CStore.unregisterThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩ 1
          (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) =
            { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
              tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
              insts := [InstState.removeThread 1 ι'] } :=
        unregisterThreadSt_eq _ _ rfl rfl rfl
      apply LRun.store_congr (S' := { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
          tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
          insts := [InstState.removeThread 1 ι'] }) e₄
      mstep
      have e₅ : threadStatusSt ⟨G.threads.length⟩ .exited
          { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
            tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] } = store₅ y.1 ι ι' fs G x k (vs.map toRefVal) :=
        threadStatus_last (z := (thread₁ G.tasks).withIndex 1) rfl _
      apply LRun.store_congr (S' := store₅ y.1 ι ι' fs G x k (vs.map toRefVal)) e₅
      apply RunsQ.chunk rfl (runs_callUnit_loop (Gt := G.tasks) rfl rfl) rfl
      mstep
      mstep
      mstep
      exact .refl _
    · rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro y ys hys hn
    exact lrun_lift_trap prof x hres hmaxr hffr hys hn rfl rfl
  · intro y ys hys hn
    exact lrun_lift_trapS prof x hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
