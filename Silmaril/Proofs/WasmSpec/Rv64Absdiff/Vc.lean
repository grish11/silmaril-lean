module

public import Silmaril.WasmSpec.Rv64Absdiff.Defs
public import Silmaril.Wasm.Logic.VCTotal.Thms

/-!
# `Rv64Absdiff` v1, mode `tactic`

`spec_vc : Spec`: the verification-condition generator `wpc` on the body (loop-free), total
soundness (`wpc_sound_total`), and a run from total correctness (`wp_of_twp`); the condition is
closed by `simp` and `bv_omega`. Kernel-checked; no solver.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Rv64Absdiff

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC
open Silmaril.Wasm.Logic.Core (funcPost)

set_option maxRecDepth 10000 in
theorem loops_body : loops func.body = 0 := by simp [func, program, loops, ctl]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
/-- The body's condition: it returns `absdiff a0 a1` (by `return`), store unchanged. -/
theorem body_vc {H : Type} (s : Store H) (m : ModuleInst)
    (a0 a1 : BitVec 64) (Q : Silmaril.Wasm.Logic.Core.Post H)
    (hQ : ∀ f, Q s f (.ret [.i64 (if a1.slt a0 then a0 - a1 else a1 - a0)])) :
    wpc (fun _ _ _ _ => True) 0 func.body Q s
      (Frame.forCall m [.i64 a0, .i64 a1] func.locals) [] := by
  simp [func, program, wpc, ctl, enterVC, labelQ, popI32, Silmaril.Wasm.Logic.Core.exec1,
    Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
    Frame.local?, Frame.setLocal, Frame.forCall, ModuleInst.blockType?, Idx.toNat, Val.i64,
    Val.i32, intRelOp_i64_ltS, bool32, BitVec.slt]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hQ ⟨[some (.i64 (a0 - a1)), some (.i64 a1)], m⟩
    rwa [ite_eq_left (by simpa [BitVec.slt] using h)] at this
  · have := hQ ⟨[some (.i64 (a1 - a0)), some (.i64 a1)], m⟩
    rwa [ite_eq_right (by simp [BitVec.slt]; omega)] at this

/-- **Mode `tactic`.** -/
theorem spec_vc : Spec := by
  intro a0 a1 _ f₀ _ P host
  refine wp_of_twp (fun _ _ => ⟨id, fun _ => id⟩) ?_
  have := wpc_sound_total (P := P) (host := host) (fun _ _ _ _ => True) 0 func.body loops_body
    (funcPost P host 1 fun s' r => s' = store ∧ ∃ r_a0, r = [.i64 r_a0] ∧ Post a0 a1 r_a0) store
    _ [] (body_vc store f₀.module a0 a1 _ fun _ => ⟨[], _, rfl, rfl, rfl, _, rfl, rfl⟩)
  simpa [vals] using this

end Silmaril.WasmSpec.Rv64Absdiff
