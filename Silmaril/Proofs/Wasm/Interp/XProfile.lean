module

public import Silmaril.Wasm.Interp.XProfile.Defs
public import Silmaril.Wasm.Interp.ExampleT.Thms

@[expose] public section

/-!
# The instruction profile of the extended arity check (proofs)
-/

namespace Silmaril.Proofs.Wasm.Interp.XProfile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.XProfile

variable {H : Type}

set_option linter.unusedSimpArgs false in
theorem xInstr_of_flatChkE {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {h : Nat} {i : Instr} {o : Option Nat}
    (hc : flatChkE ext F mi nl ret labels h i = some o) : xInstr i = true := by
  cases i
  case intLoad t p m a => cases p <;> first | rfl | simp [flatChkE, flatEff] at hc
  case intStore t p m a => cases p <;> first | rfl | simp [flatChkE, flatEff] at hc
  all_goals first | rfl | simp [flatChkE, flatEff] at hc

theorem xInstr_iff (i : Instr) :
    xInstr i = true ↔ Binaryen.nativeInstr i = true ∨ xCallForm i = true ∨ ∃ t, i = .select (some t) := by
  cases i <;> simp [xInstr, xCallForm, Binaryen.nativeInstr]
  all_goals first
    | (rename_i a b c d; cases b <;> simp)
    | (rename_i o; cases o <;> simp)

/-- A function with a tail call is outside the native profile. -/
theorem not_nativeFuncsOk_of {F : List (FuncInst H)} {fi : FuncInst H} {fn : Func} {i : Instr}
    (hfi : fi ∈ F) (hc : fi.code = .wasm fn) (hi : i ∈ fn.body) (hx : xCallForm i = true) :
    ¬ Binaryen.NativeFuncsOk F := by
  intro hF
  obtain ⟨fn', hc', hp⟩ := hF fi hfi
  rw [hc] at hc'; cases hc'
  have := hp i hi
  cases i <;> simp [xCallForm] at hx <;>
    (rw [Binaryen.instrInNativeProfile.eq_def] at this; simp [Binaryen.nativeInstr] at this)

/-- **The tail example is outside the native profile.** -/
theorem tStore_not_nativeFuncsOk : ¬ Binaryen.NativeFuncsOk ExampleT.tStore.funcs := by
  obtain ⟨fi, hfi, hc, -⟩ := Silmaril.Proofs.Wasm.Interp.ExampleT.gi_spec 0
    Silmaril.Proofs.Wasm.Interp.ExampleT.g0 (by simp)
  exact not_nativeFuncsOk_of (List.mem_of_getElem? hfi) hc (i := .returnCallIndirect ⟨0⟩ ⟨0⟩)
    (by simp) rfl

end Silmaril.Proofs.Wasm.Interp.XProfile
