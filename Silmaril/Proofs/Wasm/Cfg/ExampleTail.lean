module

public import Silmaril.Wasm.Cfg.ExampleTail.Defs
public import Silmaril.Wasm.Cfg.MachineClosed.Thms
public import Silmaril.Wasm.Abstract.SelfLoop.Thms
public import Silmaril.Proofs.Wasm.Cfg.ExampleRec

@[expose] public section

/-!
# Divergence through a tail callee: proofs

The machine enters the block (`MStepC.enter`), whose only segment ends in `return_call x`; the
call resolves to `recStore`'s self-call, which `closedDiv` names, so `TailCallDiv` holds there.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleTail

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Abstract
  Silmaril.Wasm.Cfg.ExampleTail

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- **The machine enters the block**: the state at its first segment, under its frame. -/
theorem enter (x : FuncIdx) (s : Store H) (f : Frame) :
    MStepC P host C (tailBody x) (initial (tailBody x) s f)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [tailFrame], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := tailBody x) (b := ⟨[], 0⟩)
    (sg := ⟨[], some (.block .empty (tailInner x))⟩) (stk := []) (stk₁ := []) (ws := []) (us := [])
    (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := tailInner x) (bt := .empty)
    (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl .block
    (by simpa [expression] using (RunC.nil : RunC P host C s f [] [] s f (.normal [])))
    (by
      have := CondArm.plain (i := Instr.block .empty (tailInner x)) (ws := []) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- **`TailCallDiv` at the block**: its terminator `return_call x` is a pending tail call of the
self-call of `recStore`, on no arguments, which `closedDiv` names. -/
theorem tailCallDiv (P : Profile) {fi : FuncInst Empty} {x : FuncIdx} {f : Frame}
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    TailCallDiv P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (tailBody x)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [tailFrame], recStore, f⟩ := by
  have hty : Validation.DefType.funcType? fi.type = some ([], []) := by
    simpa [hfi] using recStore_funcType
  have hfunc : recStore.func? f x = some (0, fi) := by simp [Store.func?, hx, hfi]
  exact ⟨⟨[(0, 0)], 0⟩, ⟨[], some (.returnCall x)⟩, .returnCall x, [], recStore, recStore, f, f,
    [], 0, _, fi, [], [], [], [], rfl, rfl, rfl, by simp [Instr.IsTailCall],
    by simpa [expression] using (RunC.nil : RunC P _ Abstract.closedCallOk recStore f [] [] recStore f
      (.normal [])),
    RunC.returnCall (code := []) hfunc, hfi, hty, by simp [brVals, tailFrame], rfl,
    ExampleRec.rec_closedDiv P⟩

/-- **`MDivT` at the entry of `tailBody`.** -/
theorem tail_mdivT (P : Profile) {fi : FuncInst Empty} {x : FuncIdx} {f : Frame}
    (hfi : recStore.funcs[0]? = some fi) (hx : f.module.funcs[x.toNat]? = some 0) :
    MDivT P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv (tailBody x)
      (initial (tailBody x) recStore f) :=
  .inr ⟨_, .single (enter x recStore f), tailCallDiv P hfi hx⟩

end Silmaril.Wasm.Cfg.Proofs.ExampleTail
