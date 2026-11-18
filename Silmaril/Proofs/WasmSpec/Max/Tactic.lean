module

public import Silmaril.WasmSpec.Max.Defs
import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `Max` v1, mode `tactic`

`spec_of_vcs : VCs → Spec`: run the comparison with `wasm_step`, case on its
result, enter the chosen branch as a block and run it; what remains is one
verification condition per branch (`VCs`), proved by unfolding `smax`
(`vcs_tactic`). `spec_tactic` combines them. Kernel-checked; no solver.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Max

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

/-- The quoted body: a comparison, then an `if`. -/
theorem maxFunc_body : maxFunc.body =
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .intRelOp .i32 (.gt .signed),
      .if_ (.value .i32) [.localGet ⟨0⟩] [.localGet ⟨1⟩]] := rfl

/-- `$max` declares no locals besides its parameters. -/
theorem maxFunc_locals : maxFunc.locals = [] := rfl

/-- `i32.gt_s` as a signed comparison. -/
theorem gtS32 (x y : BitVec 32) : intRelOp .i32 (.gt .signed) x y = bool32 (y.slt x) := rfl

/-- The verification conditions: each branch returns the specified value. -/
structure VCs : Prop where
  then_ : ∀ x y : BitVec 32, y.slt x = true → x = smax x y
  else_ : ∀ x y : BitVec 32, y.slt x = false → y = smax x y

/-- `VCs` by unfolding `smax`. -/
theorem vcs_tactic : VCs where
  then_ _ _ h := by simp [smax, h]
  else_ _ _ h := by simp [smax, h]

/-- **Reduction**: symbolic execution, one case per branch, leaves `VCs`. -/
theorem spec_of_vcs (vcs : VCs) : Spec := by
  intro x y H P host s m
  rw [maxFunc_body, maxFunc_locals]
  show WP P host s (Frame.forCall m [.i32 x, .i32 y] [])
    (expression [.localGet ⟨0⟩, .localGet ⟨1⟩, .intRelOp .i32 (.gt .signed)] ++
      .plain (.if_ (.value .i32) [.localGet ⟨0⟩] [.localGet ⟨1⟩]) :: []) _
  simp only [Frame.forCall, List.map_cons, List.map_nil, List.append_nil]
  wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one, gtS32]
  refine wp_if_bool32_cons (vs := []) (rest := []) ?_
  cases h : y.slt x
  · simp only [Bool.false_eq_true, ite_false]
    wasm_block
    wasm_step [Idx.toNat, Fin.val_one]
    simp only [blockPost, seqPost]
    exact wp_vals (vs := [_]) ⟨rfl, rfl, by rw [← vcs.else_ x y h]⟩
  · simp only [ite_true]
    wasm_block
    wasm_step [Idx.toNat, Fin.val_zero]
    simp only [blockPost, seqPost]
    exact wp_vals (vs := [_]) ⟨rfl, rfl, by rw [← vcs.then_ x y h]⟩

/-- Mode `tactic`. -/
theorem spec_tactic : Spec := spec_of_vcs vcs_tactic

end Silmaril.WasmSpec.Max
