module

public import Silmaril.Wasm.Cfg.ExampleLogged.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region

@[expose] public section

/-!
# The logged machine: native against Core conventions (regression fixtures, proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleLogged

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Cfg.ExampleLogged
open Silmaril.Wasm.Abstract (EvalLXPS SCall)

variable {H : Type}

/-- The block's frame: arity `0`, no outer values. -/
abbrev frameE : LFrame := ⟨0, [], false, false, [], .empty⟩

theorem const_run {s : Store H} {f : Frame} (k : BitVec 32) (stk : List Val) :
    EvalLXPS s f stk [.op (.intConst .i32 k) []] [] (s, f, .flow (.normal (.i32 k :: stk))) := by
  exact EvalLXPS.opOk (s := s) (f := f) (stk := stk) (i := .intConst .i32 k) (args := [])
    (es := []) (l₁ := []) (l₂ := []) (fun _ => nofun) .nil rfl .nil

theorem cond_block : CondArm (.block .empty innerExtra) [] 0 [] [] := by
  simpa using CondArm.plain (i := .block .empty innerExtra) (ws := []) (us := []) (fun _ _ _ => nofun)

/-- **The logged machine exits with `3`**: leaving the block keeps its `0` result values. -/
theorem logged_run (s : Store H) (f : Frame) :
    MRunL bodyExtra (initial bodyExtra s f) [] ⟨.exit, [.i32 3], [], s, f⟩ := by
  have h₁ : MStepL bodyExtra (initial bodyExtra s f) []
      ⟨.block ⟨[(0, 0)], 0⟩, [], [frameE], s, f⟩ :=
    MStepL.enter (b := ⟨[], 0⟩) (sg := ⟨[], some (.block .empty innerExtra)⟩) (stk := [])
      (stk₁ := []) (ws := []) (us := []) (ls := []) (a := 0) (c := innerExtra) (bt := .empty)
      (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl .block .nil
      cond_block rfl rfl rfl
  have h₂ : MStepL bodyExtra ⟨.block ⟨[(0, 0)], 0⟩, [], [frameE], s, f⟩ []
      ⟨.block ⟨[], 1⟩, [], [], s, f⟩ := by
    refine MStepL.run (sg := ⟨innerExtra, none⟩) (r := (s, f, .flow (.normal [.i32 2, .i32 1])))
      rfl (by simp) ?_ (.next rfl)
    have := EvalLXPS.opOk (s := s) (f := f) (stk := []) (i := .intConst .i32 1) (args := [])
      (es := [.op (.intConst .i32 2) []]) (l₁ := []) (l₂ := []) (fun _ => nofun) .nil rfl
      (const_run 2 [.i32 1])
    simpa [MachineL.codeOf, innerExtra, liftInstrs, liftInstr] using this
  have h₃ : MStepL bodyExtra ⟨.block ⟨[], 1⟩, [], [], s, f⟩ [] ⟨.exit, [.i32 3], [], s, f⟩ := by
    refine MStepL.run (sg := ⟨[.intConst .i32 3], none⟩) (r := (s, f, .flow (.normal [.i32 3])))
      rfl (by simp) ?_ (.next rfl)
    exact const_run (s := s) (f := f) 3 []
  simpa using MRunL.step h₁ (MRunL.step h₂ (MRunL.step h₃ (.refl _)))

/-- **So the body runs natively**, with no open call, to a flow returning `3`
(`MachineL.forward_sink`). -/
theorem logged_native (s : Store H) (f : Frame) :
    ∃ r, EvalLXPS s f [] (liftInstrs bodyExtra) [] r ∧
      EndRel (⟨.exit, [.i32 3], [], s, f⟩ : Machine.MState H) r :=
  forward_sink (logged_run s f) trivial

theorem val_i32 (k : BitVec 32) : (Admin.plain (.intConst .i32 k)).val? = some (.i32 k) := rfl

/-- **The Core machine exits with `1, 2, 3`**: leaving the block keeps the whole stack. -/
theorem core_run {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H} (s : Store H)
    (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyExtra) (initial bodyExtra s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := by
  have h₁ := MStepC.enter (P := P) (host := host) (C := C) (body := bodyExtra) (b := ⟨[], 0⟩)
    (sg := ⟨[], some (.block .empty innerExtra)⟩) (stk := []) (stk₁ := []) (ws := []) (us := [])
    (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := innerExtra) (bt := .empty)
    (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl .block .nil
    cond_block rfl rfl
  refine .head h₁ (.head (b := ⟨.block ⟨[], 1⟩, [.i32 1, .i32 2], [], s, f⟩) ?_ (.single ?_))
  · exact MStepC.fall (sg := ⟨innerExtra, none⟩) (stk₁ := [.i32 1, .i32 2]) rfl rfl
      (.val (val_i32 1) (.val (val_i32 2) .nil))
  · exact MStepC.fall (sg := ⟨[.intConst .i32 3], none⟩) (stk₁ := [.i32 1, .i32 2, .i32 3]) rfl rfl
      (.val (val_i32 3) .nil)

end Silmaril.Wasm.Cfg.Proofs.ExampleLogged
