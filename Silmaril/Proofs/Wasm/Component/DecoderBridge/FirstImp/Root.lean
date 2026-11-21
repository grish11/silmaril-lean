module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Prefix

/-!
# Root instantiation up to the first core instantiation, with its trampolines

`root_firstX` is `FirstCore.Root.root_first` for the concrete engine `core3 o` and root arguments
that are all one component function `g0`: root instantiation traps with a specification trap
before the first core instantiation, or reaches it with the core store of the trampolines
(`lowStore`, one per `canon lower` before it), the core functions `0, …` and the inline core
instances `preInsts pre` in the frame.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.SingleThreaded (GrowOracle)

variable {o : GrowOracle} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call (core3 o) → Canon.P (core3 o) σ (Ret (core3 o))}

/-- The configuration at the first core instantiation: the store `firstStore` with the core store
of `n` trampolines `h`. -/
def lowCfg (m : Machine.Config (core3 o) σ) (n : Nat) (h : CanonHost (core3 o)) :
    Machine.Config (core3 o) σ :=
  { m with store := firstStore m.store (lowStore n h) }

/-- **Root instantiation up to the first core instantiation, with its trampolines.** -/
theorem root_firstX {m : Machine.Config (core3 o) σ}
    {r pre post : Syntax.Component (core3 o).Module} {mi : Nat} {cargs : List (String × Nat)}
    {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}
    (hs : firstCore? r = some (pre, mi, cargs, post))
    (hpre : preOk 0 0 pre = true) (ha : ArgsOk args m)
    (hg0 : ∀ n v, args.lookup n = some v → v = .func g0)
    (hfx : ArenaField.funcs.get? m.store g0 = some fx)
    (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} ⟨0⟩ : CanonHost (core3 o)).coreType at_ =
      Param.v1Type fFlat)
    (hl : m.store.lockdown = false) (hi : m.store.insts = [])
    (hcore : m.store.core = ({} : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3 o)))) :
    (∃ tr mT, TrapsQS dispatch none (instantiateProg r args) m tr mT) ∨
      ∃ f : Frame (core3 o),
        FocusAt prof hr dispatch none (instantiateCore ⟨0⟩ f mi cargs) (instantiateProg r args) m
          (lowCfg m (preLowers pre) (CanonHost.lowered g0 fx.ft {} ⟨0⟩)) ∧
        f.coreModules = coreMods pre ∧ f.coreFuncs = List.range (preLowers pre) ∧
        f.coreInstances = instsVal (preInsts pre) := by
  have hrr := firstCore?_eq r hs
  suffices h : FOut prof hr dispatch (fun f : Frame (core3 o) =>
      (instantiateCore (σ := σ) ⟨0⟩ f mi cargs)) (instantiateProg r args) m
      (fun f m₁ => m₁ = lowCfg m (preLowers pre) (CanonHost.lowered g0 fx.ft {} ⟨0⟩) ∧
        f.coreModules = coreMods pre ∧ f.coreFuncs = List.range (preLowers pre) ∧
        f.coreInstances = instsVal (preInsts pre)) by
    rcases h with h | ⟨f, m₁, hf, rfl, hc⟩
    · exact .inl h
    · exact .inr ⟨f, hf, hc⟩
  unfold instantiateProg
  refine FOut.seqT (TOrT.runs (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) m)
    (Q := fun _ m' => m' = { m with store := DispatchSt.incNestingSt m.store }) rfl) ?_
  rintro _ m₁ rfl
  refine FOut.left ?_
  unfold instantiateRootCall instantiateRoot
  refine FOut.seqT (tOrT_trapIf (fun _ h => by cases h) _) ?_
  rintro _ m₂ rfl
  refine FOut.seqT (TOrT.runs (TRuns.getStore _)
    (Q := fun s m' => s = (DispatchSt.incNestingSt m.store : CStore (core3 o)) ∧
      m' = { m with store := DispatchSt.incNestingSt m.store }) ⟨rfl, rfl⟩) ?_
  rintro s m₃ ⟨rfl, rfl⟩
  refine FOut.seqT (tOrT_checkImport _ _) ?_
  rintro _ m₄ rfl
  refine FOut.seqT (TOrT.runs (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} _)
    (Q := fun i m' => i = (⟨0⟩ : InstId) ∧
      m' = { m with store := ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt m.store) })
    ⟨by simp [ArenaField.size, ArenaField.insts, DispatchSt.incNestingSt, hi],
      rfl⟩) ?_
  rintro i m₅ ⟨rfl, rfl⟩
  refine FOut.left ?_
  unfold instantiateComponent
  refine FOut.left ?_
  dsimp only
  rw [hrr, List.foldlM_append]
  have hpi : PreInv ({} : Scope (core3 o))
      ({ m with store := ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt m.store) } :
        Machine.Config (core3 o) σ) 0 0 [] :=
    ⟨rfl, (fun _ h => by cases h), rfl, rfl, hl⟩
  have hpx : PreInvX g0 fx ⟨0⟩ ({} : Scope (core3 o))
      ({ m with store := ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt m.store) } :
        Machine.Config (core3 o) σ) 0 [] :=
    ⟨(fun _ h => by cases h), hfx, rfl, rfl, hcore⟩
  refine FOut.seqT (prefix_runX hty hg0 pre 0 0 {} _ [] [] ha hpre hpi hpx) ?_
  rintro sc' m₆ ⟨c', nf', ncf', rfl, hinv, hinvx⟩
  rw [List.foldlM_cons]
  refine FOut.left ?_
  simp only [instantiateDef]
  refine .inr ⟨sc'.frame, _, FocusAt.here _ _, ?_, by simpa using hinv.mods, ?_, ?_⟩
  · have hc : c' = lowStore (preLowers pre) (CanonHost.lowered g0 fx.ft {} ⟨0⟩) := by
      simpa using hinvx.core
    rw [hc]
    rfl
  · simpa using hinvx.coreFuncs
  · simpa using hinvx.coreInsts

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
