module

public import Silmaril.Sim.X86.Calls.Defs
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Sim.X86.Max.Thms

/-!
# The P-calls `max`, verified modularly with `wpc`'s call rule

* `regs_set`, `all_set`, `globalVal_of_all`: the global file of a store after `setGlobalIdx`
  (the frame rule `Silmaril.Wasm.Logic.VC.globalVal_setGlobalIdx_ne` under `mi.globals.Nodup`);
* `mov_valid`, `cmp_valid`, `cmovl_valid`, `next_valid`: each quoted method of
  `Silmaril.Sim.X86.G.simModule` meets its `mspec`, by `FSpecValid.of_wpc` and `wat_vc` over a
  **symbolic** store (only `AllI64` is known);
* **`max_valid_of`**: `max` (the body is calls only) meets `maxSpec` **assuming** the spec
  context `maxSpecs` is valid: the callee bodies are not looked at (`FSpecValid.of_wpc_ctx`);
* `maxSpecs_valid`, **`max_valid`**: discharging the assumption with the method proofs;
* **`max_regs`**: what that means for the registers: `rax` is the signed maximum of `rdi` and
  `rsi` (`Silmaril.Sim.X86.Max.max_bits`), RIP advanced by 10, the other GPRs unchanged.

Every profile, every host relation. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86.Calls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.VC
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)
open Silmaril.Sim.X86.G (simModule)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## The global file -/

section File

variable {s : Store H} {mi : ModuleInst}

theorem globalVal_of_all (h : AllI64 s mi) {k : Nat} (hk : k < 23) :
    globalVal s mi k = some (.num ⟨.int .i64, regs s mi k⟩) := by
  obtain ⟨v, hv⟩ := h k hk
  simp [regs, hv]

theorem regs_set (hnd : mi.globals.Nodup) (h : AllI64 s mi) {x : Nat} (hx : x < 23)
    (v : BitVec 64) :
    regs (setGlobalIdx s mi x (.num ⟨.int .i64, v⟩)) mi = Function.update (regs s mi) x v := by
  funext k
  by_cases hk : k = x
  · subst hk
    rw [regs, globalVal_setGlobalIdx_self, globalVal_of_all h hx]
    simp
  · simp only [Function.update, hk, dite_false]
    simp only [regs, globalVal_setGlobalIdx_ne hnd hk]

theorem all_set (hnd : mi.globals.Nodup) (h : AllI64 s mi) {x : Nat} (hx : x < 23)
    (v : BitVec 64) : AllI64 (setGlobalIdx s mi x (.num ⟨.int .i64, v⟩)) mi := by
  intro k hk
  by_cases hkx : k = x
  · subst hkx
    exact ⟨v, by rw [globalVal_setGlobalIdx_self, globalVal_of_all h hx]; rfl⟩
  · rw [globalVal_setGlobalIdx_ne hnd hkx]
    exact h k hk

end File

/-! ## The methods -/

section Methods

variable {mi : ModuleInst} {a : Nat} {fi : FuncInst H} {ps rs : Validation.Ty (.list .val)}

/-- Evaluate a method body over a symbolic store with `AllI64` (`hA`) and distinct global
addresses (`hnd`). -/
local macro "method_vc" F:ident hnd:ident hA:ident : tactic => `(tactic| (
  wat_vc [Silmaril.Sim.X86.G.simModule, mspec, globalVal_of_all $hA, globalVal_setGlobalIdx_ne $hnd,
    regs_set $hnd, all_set $hnd, $hA:ident, $F:ident, NextArg]
  all_goals simp (maxDischargeDepth := 20) [regs_set $hnd, all_set $hnd, $hA:ident]))

theorem mov_valid (hnd : mi.globals.Nodup) (hm : fi.module = mi)
    (hcode : fi.code = .wasm simModule.funcs[0])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0) (hrs : rs.length = 0) :
    FSpecValid P host a (mspec mi fi a (· = []) Fmov) := by
  refine FSpecValid.of_wpc (fun _ _ => fun _ _ _ _ => True) (fun _ _ h => h.1) hcode he
    (fun _ _ h => by rw [h.2.1, hps]; rfl) fun s args ⟨_, hargs, hA⟩ => ?_
  subst hargs hm
  rw [hrs]
  method_vc Fmov hnd hA

theorem cmp_valid (hnd : mi.globals.Nodup) (hm : fi.module = mi)
    (hcode : fi.code = .wasm simModule.funcs[4])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0) (hrs : rs.length = 0) :
    FSpecValid P host a (mspec mi fi a (· = []) Fcmp) := by
  refine FSpecValid.of_wpc (fun _ _ => fun _ _ _ _ => True) (fun _ _ h => h.1) hcode he
    (fun _ _ h => by rw [h.2.1, hps]; rfl) fun s args ⟨_, hargs, hA⟩ => ?_
  subst hargs hm
  rw [hrs]
  method_vc Fcmp hnd hA

theorem cmovl_valid (hnd : mi.globals.Nodup) (hm : fi.module = mi)
    (hcode : fi.code = .wasm simModule.funcs[5])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 0) (hrs : rs.length = 0) :
    FSpecValid P host a (mspec mi fi a (· = []) Fcmovl) := by
  refine FSpecValid.of_wpc (fun _ _ => fun _ _ _ _ => True) (fun _ _ h => h.1) hcode he
    (fun _ _ h => by rw [h.2.1, hps]; rfl) fun s args ⟨_, hargs, hA⟩ => ?_
  subst hargs hm
  rw [hrs]
  method_vc Fcmovl hnd hA

theorem next_valid (hnd : mi.globals.Nodup) (hm : fi.module = mi)
    (hcode : fi.code = .wasm simModule.funcs[6])
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 0) :
    FSpecValid P host a (mspec mi fi a NextArg Fnext) := by
  refine FSpecValid.of_wpc (fun _ _ => fun _ _ _ _ => True) (fun _ _ h => h.1) hcode he
    (fun _ _ h => by obtain ⟨_, rfl⟩ := h.2.1; rw [hps]; rfl)
    fun s args ⟨_, ⟨len, hargs⟩, hA⟩ => ?_
  subst hargs hm
  rw [hrs]
  method_vc Fnext hnd hA

end Methods

/-! ## `max` -/

theorem maxSpecs_specs (mi : ModuleInst) (a0 a4 a5 a6 : Nat) (f0 f4 f5 f6 : FuncInst H)
    (a : Nat) :
    (maxSpecs mi a0 a4 a5 a6 f0 f4 f5 f6).specs a =
      if a = a0 then some (0, mspec mi f0 a0 (· = []) Fmov)
      else if a = a4 then some (0, mspec mi f4 a4 (· = []) Fcmp)
      else if a = a5 then some (0, mspec mi f5 a5 (· = []) Fcmovl)
      else if a = a6 then some (1, mspec mi f6 a6 NextArg Fnext)
      else none := rfl

/-- **`max` from the specifications of the methods it calls** (modular: assumes the spec
context, does not look at the callee bodies). -/
theorem max_valid_of {mi : ModuleInst} {a a0 a4 a5 a6 : Nat} {fi f0 f4 f5 f6 : FuncInst H}
    (hf0 : mi.funcs[0]? = some a0) (hf4 : mi.funcs[4]? = some a4) (hf5 : mi.funcs[5]? = some a5)
    (hf6 : mi.funcs[6]? = some a6)
    (h40 : a4 ≠ a0) (h50 : a5 ≠ a0) (h54 : a5 ≠ a4) (h60 : a6 ≠ a0) (h64 : a6 ≠ a4)
    (h65 : a6 ≠ a5) (hΓ : (maxSpecs (H := H) mi a0 a4 a5 a6 f0 f4 f5 f6).Valid P host)
    (hm : fi.module = mi) (hcode : fi.code = .wasm simModule.funcs[7])
    {ps rs : Validation.Ty (.list .val)} (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = 0) (hrs : rs.length = 0) :
    FSpecValid P host a (maxSpec mi fi a a0 a4 a5 a6 f0 f4 f5 f6) := by
  refine FSpecValid.of_wpc_ctx hΓ (fun _ _ => fun _ _ _ _ => True) (fun _ _ h => h.1) hcode he
    (fun _ _ h => by rw [h.2.1, hps]; rfl) fun s args ⟨_, hargs, hA, h0, h4, h5, h6⟩ => ?_
  subst hargs hm
  rw [hrs]
  wat_vc [Silmaril.Sim.X86.G.simModule, maxSpecs_specs, maxSpec, mspec, NextArg, hf0, hf4, hf5,
    hf6, h40, h50, h54, h60, h64, h65, h0, h4, h5, h6, hA]

/-- A function instance of the code `c` in the instance `mi`, with `np` parameters and no
results. -/
structure IsMethod (mi : ModuleInst) (fi : FuncInst H) (c : Func) (np : Nat) : Prop where
  module : fi.module = mi
  code : fi.code = .wasm c
  type : ∃ ps rs, Validation.Expand fi.type (.func ps rs) ∧ ps.length = np ∧ rs.length = 0

/-- The spec context of `max` is valid when the four methods are the quoted ones. -/
theorem maxSpecs_valid {mi : ModuleInst} {a0 a4 a5 a6 : Nat} {f0 f4 f5 f6 : FuncInst H}
    (hnd : mi.globals.Nodup) (h0 : IsMethod mi f0 simModule.funcs[0] 0)
    (h4 : IsMethod mi f4 simModule.funcs[4] 0) (h5 : IsMethod mi f5 simModule.funcs[5] 0)
    (h6 : IsMethod mi f6 simModule.funcs[6] 1) :
    (maxSpecs (H := H) mi a0 a4 a5 a6 f0 f4 f5 f6).Valid P host := by
  intro a n S hS
  rw [maxSpecs_specs] at hS
  have hex : ∀ (fi : FuncInst H) (Arg : List Val → Prop) F b,
      ∀ s args, (mspec mi fi b Arg F).pre s args → (s.funcs[b]?).isSome :=
    fun _ _ _ _ _ _ h => by rw [h.1]; rfl
  obtain ⟨ps0, rs0, he0, hp0, hr0⟩ := h0.type
  obtain ⟨ps4, rs4, he4, hp4, hr4⟩ := h4.type
  obtain ⟨ps5, rs5, he5, hp5, hr5⟩ := h5.type
  obtain ⟨ps6, rs6, he6, hp6, hr6⟩ := h6.type
  split_ifs at hS <;> simp only [Option.some.injEq, Prod.mk.injEq] at hS <;>
    obtain ⟨rfl, rfl⟩ := hS <;> subst_vars
  · exact ⟨mov_valid hnd h0.module h0.code he0 hp0 hr0, hex _ _ _ _⟩
  · exact ⟨cmp_valid hnd h4.module h4.code he4 hp4 hr4, hex _ _ _ _⟩
  · exact ⟨cmovl_valid hnd h5.module h5.code he5 hp5 hr5, hex _ _ _ _⟩
  · exact ⟨next_valid hnd h6.module h6.code he6 hp6 hr6, hex _ _ _ _⟩

/-- **The P-calls `max` meets its specification**: the methods' proofs and the modular proof
of `max` combined. -/
theorem max_valid {mi : ModuleInst} {a a0 a4 a5 a6 : Nat} {fi f0 f4 f5 f6 : FuncInst H}
    (hnd : mi.globals.Nodup)
    (hf0 : mi.funcs[0]? = some a0) (hf4 : mi.funcs[4]? = some a4) (hf5 : mi.funcs[5]? = some a5)
    (hf6 : mi.funcs[6]? = some a6)
    (h40 : a4 ≠ a0) (h50 : a5 ≠ a0) (h54 : a5 ≠ a4) (h60 : a6 ≠ a0) (h64 : a6 ≠ a4)
    (h65 : a6 ≠ a5) (h0 : IsMethod mi f0 simModule.funcs[0] 0)
    (h4 : IsMethod mi f4 simModule.funcs[4] 0) (h5 : IsMethod mi f5 simModule.funcs[5] 0)
    (h6 : IsMethod mi f6 simModule.funcs[6] 1) (h7 : IsMethod mi fi simModule.funcs[7] 0) :
    FSpecValid P host a (maxSpec mi fi a a0 a4 a5 a6 f0 f4 f5 f6) := by
  obtain ⟨ps, rs, he, hp, hr⟩ := h7.type
  exact max_valid_of hf0 hf4 hf5 hf6 h40 h50 h54 h60 h64 h65
    (maxSpecs_valid hnd h0 h4 h5 h6) h7.module h7.code he hp hr

/-- What `maxSpec`'s global file is: `rax` the signed maximum of `rdi`, `rsi`; RIP plus 10;
the other GPRs unchanged. -/
theorem max_regs (g : Nat → BitVec 64) :
    let g' := Fnext [Val.i64 4] (Fcmovl [] (Fnext [Val.i64 3]
      (Fcmp [] (Fnext [Val.i64 3] (Fmov [] g)))))
    g' 0 = (if (g 7).slt (g 6) then g 6 else g 7) ∧ g' 16 = g 16 + 10 ∧
      ∀ k, 0 < k → k < 16 → g' k = g k := by
  refine ⟨?_, ?_, fun k hk hk' => ?_⟩
  · simp only [Fnext, Fcmovl, Fcmp, Fmov, Val.i64, Function.update]
    simp only [Nat.reduceEqDiff, ↓reduceDIte]
    exact Silmaril.Sim.X86.Max.max_bits (g 7) (g 6)
  · simp only [Fnext, Fcmovl, Fcmp, Fmov, Val.i64, Function.update]
    simp
    bv_omega
  · simp only [Fnext, Fcmovl, Fcmp, Fmov, Val.i64, Function.update]
    simp [show k ≠ 0 by omega, show k ≠ 16 by omega, show k ≠ 17 by omega,
      show k ≠ 20 by omega, show k ≠ 21 by omega, show k ≠ 22 by omega]

end Silmaril.Sim.X86.Calls
