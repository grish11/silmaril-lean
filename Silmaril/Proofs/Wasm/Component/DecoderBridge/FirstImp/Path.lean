module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Start

/-!
# The start call during instantiation, with the store it leaves

`FirstCore.Path.start_coreG` runs `Instantiate.runStart ⟨0⟩ a` to the core activation of the
start function; `start_coreX` is the same run (the same proof) with the store reached
(`gStore₃`: the start task and thread registered with the root instance `0`), the current
thread and the host state; `callInv_start`: so the start activation of the first core
instantiation satisfies the invariant `CallInv` of the host calls (`Start`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

section Path

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)] {impl : HostImpl E σ}

theorem start_coreX (prof : ProfileKind) (M : Machine.Config E σ) (a : E.FuncAddr)
    (ι ι' : InstState) {th : Option ThreadId} {K : Unit → Canon.P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : M.ctl = ⟨th, .prog (Instantiate.runStart ⟨0⟩ a >>= K), segs⟩ :: rest)
    (hl : M.store.lockdown = false) (hi : M.store.insts = [ι])
    (hadd : ι.addThread? ⟨M.store.threads.length⟩ = some (1, ι')) :
    ∃ M₀ thc Kc segsc restc tr, LRun prof (fun _ _ => false) (DG impl) M tr M₀ ∧
      M₀.ctl = ⟨thc, .core (E.invoke a []) Kc, segsc⟩ :: restc ∧
      M₀.store = gStore₃ M.store a ι' ∧ thc = some ⟨M.store.threads.length⟩ ∧
      M₀.host = M.host := by
  obtain ⟨S, h₀, ctl₀, conts, pending, results, cancels⟩ := M
  dsimp only at hc hl hi hadd ⊢
  subst hc
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  apply RunsQ.chunk2 rfl (runs_allocObjG ArenaField.funcs (.lifted a Instantiate.startType {} ⟨0⟩) _ rfl) hl
  apply RunsQ.chunk2 rfl (runs_allocObjG ArenaField.callers (.sub .start) _ rfl) hl
  apply LRun.prog rfl (fun _ _ e => by cases e) hl (.call rfl)
  have hget : ArenaField.funcs.get? (gStore₁ S a) (⟨S.funcs.length⟩ : FuncId) =
      some (.lifted a Instantiate.startType {} ⟨0⟩) := by
    show (S.funcs ++ [_])[S.funcs.length]? = _
    rw [List.getElem?_concat_length]
  apply RunsQ.chunk rfl (runs_getObjG ArenaField.funcs _ _ hget) hl
  apply RunsQ.chunk rfl (runs_allocObjG ArenaField.tasks _ _ rfl) hl
  apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) hl
  apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) hl
  apply RunsQ.chunk2 rfl (runs_ite_falseG (by exact threadIs_lastG rfl) _ _) hl
  apply LRun.prog rfl (fun _ _ e => by cases e) hl
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  have e₁ : ∀ S' : CStore E, S'.threads = S.threads ++ [{ task := ⟨S.tasks.length⟩ }] →
      threadStatusSt ⟨S.threads.length⟩ .running S' =
        { S' with threads := S.threads ++ [startThread S.tasks] } :=
    fun S' h => threadStatus_lastG h _
  apply LRun.store_congrG (S' := gStore₁ S a) ((e₁ _ rfl).trans rfl)
  have hS₁ : (gStore₁ S a).insts = [ι] := hi
  apply RunsQ.chunk (th := some ⟨S.threads.length⟩)
    (p := Task.enterImplicitThread Quirks.none ⟨S.tasks.length⟩) (a := true) rfl
    (runs_enterG' (Gt := S.tasks) (y := startTask S.callers) rfl rfl rfl hS₁ hadd) hl
  have e₂ : CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩ (gStore₁ S a)) =
        gStore₂ S a ι' :=
    registerThreadSt_eqG (tasks_modify_lastG rfl _) rfl hS₁ hadd rfl
  apply LRun.store_congrG (S' := gStore₂ S a ι') (by exact e₂)
  have hS₂ : (gStore₂ S a ι').tasks = S.tasks ++ [startTask₁ S.callers ⟨S.threads.length⟩] :=
    rfl
  apply RunsQ.chunk rfl (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG (Gt := S.tasks) hS₂))
    hl
  apply RunsQ.chunk rfl (runs_startSG (Gt := S.tasks) (Gc := S.callers) hS₂ rfl rfl) hl
  apply RunsQ.chunk rfl (runs_lower_nilG _ _) hl
  apply LRun.store_congrG (S' := gStore₃ S a ι') (by
    exact setTaskState_lastG (Gt := S.tasks) (y := startTask₁ S.callers ⟨S.threads.length⟩)
      rfl _)
  mstepG
  exact .refl _
  · rfl
  · rfl
  · rfl
  · rfl

end Path

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
