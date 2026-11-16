module

public import Silmaril.Wasm.Game.IOAccept.Thms
public import Silmaril.Wasm.Game.IOAccept.Example.Defs
import Silmaril.Proofs.Wasm.Game.Examples.StartImport
import Silmaril.Proofs.Wasm.Game.Linking.Callout
import Silmaril.Proofs.Wasm.Game.Accept.Example

/-!
# Traced I/O acceptance of a concrete module: proofs

`exStart` (`Silmaril.Wasm.Game.Examples`) imports `"env" "f" : [] → []`; its function `1` has
body `call 0`, is the start function and is exported as `"run"`. Against `unitEnv` (which
answers `values []` in the same store; it satisfies the host contract), the traced session

1. runs the start function to the call of `"env" "f"` (`run_to_callout`) and tags the callout;
2. takes the host answer and returns from the start function: instantiation has finished;
3. invokes `"run"` (address `1`) with no arguments, tagging `enter`;
4. runs to the same call and tags it again.

Its tag list is `[out f, enter 1, out f]`: the first output is internal to instantiation and is
dropped by `bracket`; the second is triggered by the invocation.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.IOAccept.Example

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept Silmaril.Accept.IO
  Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.Examples Silmaril.Proofs.Wasm.Game.Examples
  Silmaril.Wasm.Game.IOAccept.Example

/-- `unitEnv` satisfies the host contract. -/
theorem unitEnv_ok (s₀ : Store Nat) : UEnvOk s₀ unitEnv := by
  rintro q e a q' ps rs - ⟨hs, fi, hfi, hcode, hexp, -⟩ ⟨rfl, hr⟩
  refine ⟨hs, Extend.refl hs, ?_⟩
  show ResultTyped e.store (.values []) rs.toList
  rw [hr fi hfi hcode ps rs hexp]
  exact .nil

/-- The redex of the call of `"env" "f"` from function `1`. -/
abbrev redex (fi₀ fi₁ : FuncInst Nat) : List Admin :=
  [.frame 0 (Frame.forCall fi₁.module [] []) [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]]]

/-- The context of that redex. -/
abbrev redexCtx (fi₁ : FuncInst Nat) : Ctx :=
  .frame [] 0 (Frame.forCall fi₁.module [] []) (.label [] 0 [] (.top [] []) []) []

/-- The instance has no memory. -/
theorem memAddr_eq : exC₀.frame.module.mems[0]? = none := by
  simp [exC₀_eq, Silmaril.Proofs.Wasm.Game.Accept.t_mems]

variable {P : Profile}

/-- The callout at the redex, in any frame. -/
theorem decompose_redex {fi₀ fi₁ : FuncInst Nat} (hl : exPrep.1.store.funcs = [fi₀, fi₁])
    (h0 : fi₀.code = .host 0) (ht₀ : FnType.ofDefType? fi₀.type = some ⟨[], []⟩) :
    decompose? exPrep.1.store (redex fi₀ fi₁) = some (redexCtx fi₁, 0, 0, []) := by
  have hd := Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill (s := exPrep.1.store)
    (redexCtx fi₁) (args := []) (a := 0) (c := .callRefType fi₀.type) trivial
    (by rw [hl]; rfl) (ty_nil ht₀) (by simp [Ty.length]) h0
  simpa [Ctx.fill, vals] using hd

theorem calloutAt_redex {fi₀ fi₁ : FuncInst Nat} (hl : exPrep.1.store.funcs = [fi₀, fi₁])
    (h0 : fi₀.code = .host 0) (ht₀ : FnType.ofDefType? fi₀.type = some ⟨[], []⟩) (f : Frame) :
    calloutAt? exStart exC₀.frame.module.mems[0]? ⟨exPrep.1.store, f, redex fi₀ fi₁⟩ =
      some ⟨("env", "f"), [], none⟩ := by
  refine calloutAt?_eq_some_iff.2 ⟨redexCtx fi₁, 0, 0, decompose_redex hl h0 ht₀, rfl, ?_⟩
  simp [memAddr_eq]

/-- `unitEnv` answers the call of import `0` in the instantiated store. -/
theorem unitEnv_ans {fi₀ fi₁ : FuncInst Nat} (hl : exPrep.1.store.funcs = [fi₀, fi₁])
    (h0 : fi₀.code = .host 0) (h1c : ∀ h, fi₁.code ≠ .host h)
    (ht₀ : FnType.ofDefType? fi₀.type = some ⟨[], []⟩) :
    unitEnv.Ans () ⟨0, exPrep.1.store, []⟩ ⟨exPrep.1.store, .values []⟩ () := by
  refine ⟨rfl, fun fi hfi hcode ps rs hexp => ?_⟩
  rw [hl, List.mem_cons, List.mem_singleton] at hfi
  rcases hfi with rfl | rfl
  · obtain ⟨-, hrs⟩ := Ty.func.inj (Expand.func_eq (ty_nil ht₀) hexp)
    rw [← hrs, Ty.toList_ofList]
  · exact absurd hcode (h1c 0)

/-- Entering `"run"` from `$invoke` reaches the redex. -/
theorem run_invoke {fi₀ fi₁ : FuncInst Nat} {code : Func} {x : FuncIdx}
    (hl : exPrep.1.store.funcs = [fi₀, fi₁]) (h1 : fi₁.code = .wasm code)
    (hloc : code.locals = []) (hbody : code.body = [.call x]) (hx : x.toNat = 0)
    (ht₁ : FnType.ofDefType? fi₁.type = some ⟨[], []⟩) (hm₁ : fi₁.module.funcs = [0, 1]) :
    Steps P (fun _ _ _ _ => False) (invoke exPrep.1.store 1 [])
      ⟨exPrep.1.store, {}, redex fi₀ fi₁⟩ := by
  have h₂ : Step P (fun _ _ _ _ => False) (invoke exPrep.1.store 1 [])
      ⟨exPrep.1.store, {}, [.frame 0 (Frame.forCall fi₁.module [] [])
        [.label 0 [] [.plain (.call x)]]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := fun _ _ _ _ => False) (s := exPrep.1.store)
      (f := {}) (c := .callRefType ((exPrep.1.store.funcs[1]?.map FuncInst.type).getD default))
      (vs := []) (a := 1) (fi := fi₁) (code := code) trivial (by rw [hl]; rfl) (ty_nil ht₁)
      (by simp [Ty.length]) h1
    simpa [invoke, vals, hloc, hbody, expression, Ty.length] using h
  have h₃ : Step P (fun _ _ _ _ => False)
      ⟨exPrep.1.store, Frame.forCall fi₁.module [] [], [.plain (.call x)]⟩
      ⟨exPrep.1.store, Frame.forCall fi₁.module [] [], [.ref (.func 0), .callRefType fi₀.type]⟩ :=
    Step.call (by simp [Frame.forCall, hm₁, hx]) (by rw [hl]; rfl)
  exact h₂.steps.trans (Step.ctxtFrame (Step.ctxtLabel h₃)).steps

/-- **The traced session of `exStart`**, every profile. -/
theorem run_tsession : ∃ x, TSession P unitEnv exStart exC₀.frame.module.mems[0]? runRoles exC₀
    () exI.addrs .run true x runTags := by
  obtain ⟨fi₀, fi₁, code, x, hl, h0, h1, hloc, hbody, hx, ht₀, ht₁, hm₁⟩ := exShape
  have h1c : ∀ h, fi₁.code ≠ .host h := fun h he => by rw [h1] at he; cases he
  have hco := calloutAt_redex hl h0 ht₀
  have hd := decompose_redex hl h0 ht₀
  -- 1. the start function reaches the call, which is tagged
  have hrun := run_to_callout (P := P) (host := fun _ _ _ _ => False) hl t_funcs h1 hloc hbody
    hx ht₁ hm₁
  rw [← exC₀_eq] at hrun
  have s₁ := TSession.call (R := runRoles) (m := exStart) (memAddr := exC₀.frame.module.mems[0]?)
    (TSession.of_core_steps (c₀ := exC₀) (q₀ := ()) (L := unitEnv) (addrs := exI.addrs)
      .start hrun) hd
  rw [hco] at s₁
  -- 2. the host answers; the start function returns
  have s₂ := TSession.answer s₁ hd (unitEnv_ans hl h0 h1c ht₀)
  rw [hco] at s₂
  have hret : Steps P (fun _ _ _ _ => False)
      ⟨exPrep.1.store, exPrep.1.frame, (redexCtx fi₁).fill (Result.values []).toAdmin⟩
      ⟨exPrep.1.store, exPrep.1.frame, []⟩ := by
    have h₂ : Step P (fun _ _ _ _ => False)
        ⟨exPrep.1.store, Frame.forCall fi₁.module [] [], [.label 0 [] []]⟩
        ⟨exPrep.1.store, Frame.forCall fi₁.module [] [], []⟩ := Step.labelVals (vs := [])
    have h₃ : Step P (fun _ _ _ _ => False)
        ⟨exPrep.1.store, exPrep.1.frame, [.frame 0 (Frame.forCall fi₁.module [] []) []]⟩
        ⟨exPrep.1.store, exPrep.1.frame, []⟩ := Step.frameVals (vs := []) rfl
    simpa [Ctx.fill, Result.toAdmin, vals] using (Step.ctxtFrame h₂).steps.trans h₃.steps
  have s₃ := TSession.of_core_steps s₂ hret
  -- 3. the environment invokes `"run"`
  have hok : InvokeOk exPrep.1.store 1 [] :=
    ⟨fi₁, _, _, by rw [hl]; rfl, ty_nil ht₁, by simp⟩
  have s₄ := TSession.invoke s₃ (by decide) ⟨[], rfl⟩ (by simp [exI, t_addrs]) hok
  -- 4. it reaches the call, which is tagged
  have s₅ := TSession.call (TSession.of_core_steps s₄ (run_invoke hl h1 hloc hbody hx ht₁ hm₁)) hd
  rw [hco] at s₅
  exact ⟨_, by simpa [runTags, Roles.callTags, Roles.answerTags, runRoles] using s₅⟩

/-- **`"run"` triggers its call of `"env" "f"`**, in the entry reading. -/
theorem run_triggers :
    (1, ("env", "f")) ∈ triggers (entryIORuns P UEnvOk 0 exStart runRoles) := by
  obtain ⟨x, h⟩ := run_tsession (P := P)
  refine ⟨⟨1, [("env", "f")], none⟩, ⟨_, ⟨runTags, ?_, rfl⟩, ?_⟩, rfl, by simp⟩
  · exact ⟨exMT, exI, exC₀, ex_isSpecInstance, unitEnv, (), unitEnv_ok _, .run, true, x, h⟩
  · decide +kernel

end Silmaril.Proofs.Wasm.Game.IOAccept.Example
