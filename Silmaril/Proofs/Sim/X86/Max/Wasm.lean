module

public import Silmaril.Sim.X86.Max.Defs
public import Silmaril.Sim.X86.G.Thms

/-!
# `max`: the Wasm problem, solved with the verification-condition generator

`wasm_solution`: the Wasm problem of `max` (`WProblem … maxCode (fun _ => True) MaxPost`) at
every profile and for every host relation. `g_vc` evaluates `wpc` on `maxCode`; what remains is
one bit-vector fact, `max_bits`: the generated `cmovl` computes the signed maximum, because
`SF xor OF` after `cmp` is signed less-than (silmaril's `slt_eq_sign_xor_overflow`).
-/

@[expose] public section

namespace Silmaril.Sim.X86.Max

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg)
open Silmaril.Sim.X86.G

theorem b64_xor (a b : Bool) : b64 a ^^^ b64 b = b64 (a ^^ b) := by
  cases a <;> cases b <;> decide

/-- The arithmetic of the generated `cmp; cmovl`. -/
theorem max_bits (x y : BitVec 64) :
    x ^^^ ((x ^^^ y) &&& ((0 : BitVec 64) - ((x - y) >>> 63 ^^^ ((x ^^^ y) &&& (x ^^^ (x - y))) >>> 63))) =
      if x.slt y then y else x := by
  rw [shr63, shr63, b64_xor, cmov_bits, Silmaril.X86.Ext.slt_eq_sign_xor_overflow]
  rfl

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The Wasm problem of `max` is solved.** -/
theorem wasm_solution : WProblem (H := H) P host maxCode (fun _ => True) MaxPost := by
  intro s f R ⟨hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩ _
  apply hwp_of_wpc (fun _ _ _ _ => True)
  g_vc [maxCode, hl, hr, hw, hc, hz, hs, ho, List.append_assoc]
  refine ⟨trivial, fun R' h => ⟨?_, fun r hr => ?_⟩⟩
  · have h' := h .rax
    simp only [ite_true, Option.some.injEq, val_i64_inj] at h'
    rw [← h', max_bits]
  · have h' := h r
    simp only [hr, ite_false, Option.some.injEq, val_i64_inj] at h'
    exact h'.symm

end Silmaril.Sim.X86.Max
