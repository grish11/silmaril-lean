module

public import Silmaril.Wasm.Cfg.ExampleRetJunk.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.ExampleNested

@[expose] public section

/-!
# A validated exit from a frame holding outer values (proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleRetJunk

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Cfg.ExampleRetJunk
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Cfg.Proofs.ExampleNested (ev_op ev_stop val_i32 cond_plain)

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem retMod_valid : (Validation.validate? retMod).isSome = true := by decide +kernel

/-- The `block`'s frame: arity `1`, the outer value `1`. -/
abbrev frB : LFrame := ⟨1, [.i32 1], false, false, [], .value .i32⟩

/-- **The logged machine exits `bodyRet` with the branch-site stack `2`.** -/
theorem ret_logged (s : Store H) (f : Frame) :
    MRunL bodyRet (initial bodyRet s f) [] ⟨.exit, [.i32 2], [], s, f⟩ := by
  have h₁ : MStepL bodyRet (initial bodyRet s f) [] ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩ :=
    MStepL.enter (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 1], some (.block (.value .i32) retBlock)⟩)
      (a := 0) (V := [.i32 1]) (V' := [.i32 1]) rfl rfl rfl .block
      (ev_op (fun _ => nofun) rfl .nil) (.plain (fun _ _ _ => nofun)) rfl rfl
  have h₂ : MStepL bodyRet ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩ []
      ⟨.exit, [.i32 2], [], s, f⟩ :=
    MStepL.run (sg := ⟨[.intConst .i32 2], some .return_⟩) rfl
      (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
      (ev_op (fun _ => nofun) rfl (ev_stop (fun _ => nofun) rfl (by simp [Flow.IsNormal])))
      DispL.ret
  simpa using MRunL.step h₁ (MRunL.step h₂ (.refl _))

/-- **`MStepC` exits `bodyRet` with `1, 2`**: the outer value of the frame the `return` leaves,
under the branch-site stack. -/
theorem ret_core (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyRet) (initial bodyRet s f)
      ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ := by
  have h₁ : MStepC P host C bodyRet (initial bodyRet s f)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩ :=
    MStepC.enter (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 1], some (.block (.value .i32) retBlock)⟩)
      (a := 0) (stk₁ := [.i32 1]) (ws := [.i32 1]) (us := []) rfl rfl rfl .block
      (.val (val_i32 1) .nil) (cond_plain (fun _ _ _ => nofun)) rfl rfl
  have h₂ : MStepC P host C bodyRet ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩
      ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
    MStepC.ret (sg := ⟨[.intConst .i32 2], some .return_⟩) rfl rfl (.val (val_i32 2) .nil)
  exact .head h₁ (.single h₂)

/-- The two exit states are related by the projection relation, with the junk `1`. -/
theorem ret_projRel (s : Store H) (f : Frame) :
    ProjRel (⟨.exit, [.i32 2], [], s, f⟩ : MState H) ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
  .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, [.i32 1], rfl⟩

/-- **They are different states**: the boundary is crossed. -/
theorem ret_ne (s : Store H) (f : Frame) :
    (⟨.exit, [.i32 2], [], s, f⟩ : MState H) ≠ ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ := by
  intro h; cases h

/-- **They agree on the function's result**: the top value (result arity `1`). -/
theorem ret_top : topVals 1 [Val.i32 2] = topVals 1 [Val.i32 1, Val.i32 2] := rfl

/-- The native run of `bodyRet`: a `return` of `2`. -/
theorem ret_native (s : Store H) (f : Frame) :
    ∃ r, EvalLXPS s f [] (liftInstrs bodyRet) [] r ∧
      EndRel (⟨.exit, [.i32 2], [], s, f⟩ : MState H) r :=
  forward_sink (ret_logged s f) trivial

end Silmaril.Wasm.Cfg.Proofs.ExampleRetJunk
