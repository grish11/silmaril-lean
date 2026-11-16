module

public import Silmaril.WasmSpec.Add3.Defs
public import Silmaril.Wasm.Logic.Core.Thms
import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `Add3` v1, mode `tactic`

`spec_tactic : Spec`. Each `call $add` is discharged by `add_call`, which
applies the call rule `wp_call` to `Adder.CallSpec` only: the proof never looks
at an adder's body. The straight-line code between calls runs by `wasm_step`.
Kernel-checked; no solver.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Add3

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

/-- The quoted body. -/
theorem add3Func_body : add3Func.body =
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .call ⟨0⟩, .localGet ⟨2⟩, .call ⟨0⟩] := rfl

/-- `$add3` declares no locals besides its parameters. -/
theorem add3Func_locals : add3Func.locals = [] := rfl

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `Val.i32` is injective. -/
theorem i32_inj {x y : BitVec 32} (h : Val.i32 x = Val.i32 y) : x = y := by
  cases h
  rfl

/-- **One call of an adder** through `Adder.CallSpec`: `call 0` on `x, y` leaves
`x + y` and the store unchanged. -/
theorem add_call {a : Nat} {Inv : Store H → Prop} {s : Store H} {f : Frame}
    {vs : List Val} {rest : List Admin} {Q : Post H} {x y : BitVec 32}
    (hspec : Adder.CallSpec P host a Inv) (hm : f.module.funcs[0]? = some a)
    (hs : (s.funcs[a]?).isSome) (hinv : Inv s)
    (hk : WP P host s f (vals (vs ++ [.i32 (x + y)]) ++ rest) Q) :
    WP P host s f (vals (vs ++ [.i32 x, .i32 y]) ++ .plain (.call ⟨0⟩) :: rest) Q := by
  refine wp_call (args := Adder.args (x, y)) hm hs hspec ⟨hinv, (x, y), rfl⟩ ?_
  rintro s' res ⟨rfl, xy, hargs, rfl⟩
  have h : Val.i32 x = Val.i32 xy.1 ∧ Val.i32 y = Val.i32 xy.2 := by
    simpa only [Adder.args, List.cons.injEq, and_true] using hargs
  have hxy : xy = (x, y) := Prod.ext (i32_inj h.1).symm (i32_inj h.2).symm
  rw [hxy]
  exact hk

/-- Mode `tactic`: two uses of `add_call`. -/
theorem spec_tactic : Spec := by
  intro H P host a Inv s m hspec hm hs hinv x y z
  rw [add3Func_body, add3Func_locals]
  simp only [Frame.forCall, List.map_cons, List.map_nil, List.append_nil]
  show WP P host s _ (vals [] ++ expression [.localGet ⟨0⟩, .localGet ⟨1⟩] ++
    .plain (.call ⟨0⟩) :: [.plain (.localGet ⟨2⟩), .plain (.call ⟨0⟩)]) _
  wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one]
  refine add_call (vs := []) hspec hm hs hinv ?_
  show WP P host s _ (vals [.i32 (x + y)] ++ expression [.localGet ⟨2⟩] ++
    .plain (.call ⟨0⟩) :: []) _
  wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one]
  refine add_call (vs := []) hspec hm hs hinv ?_
  exact wp_vals (vs := [_]) ⟨rfl, rfl, rfl⟩

end Silmaril.WasmSpec.Add3
