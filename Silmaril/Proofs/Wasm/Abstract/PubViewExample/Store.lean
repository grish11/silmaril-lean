module

public import Silmaril.Wasm.Abstract.PubViewExample.Defs
public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.SingleThreaded.Soundness

/-!
# The two stores: facts by kernel evaluation

Validation, allocation and the shape of the two stores are computed by kernel evaluation
(`decide +kernel`), as in `Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example`. Typing of the
stores comes from `prepare?_sound` and `Instantiate.ok`, the arity check from `storeChkB`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.PubViewExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.PubViewExample

/-! ## Executable shape checks -/

/-- The type `d` is a function type `[] → [t]`. -/
def retOneB (d : Validation.DefType) : Bool :=
  match d.funcType? with
  | some ([], [_]) => true
  | _ => false

/-- The function at `a` is Wasm code `[] → [t]` with no locals whose body is `call x`, and `x`
names the address `t'` in its module. -/
def callsB (s : Store Empty) (a t' : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm ⟨_, [], [.call x]⟩ => fi.module.funcs[x.toNat]? == some t' && retOneB fi.type
    | _ => false
  | none => false

/-- The function at `a` is Wasm code `[] → [t]` with no locals whose body is `i32.const 42`. -/
def constB (s : Store Empty) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm ⟨_, [], [.intConst .i32 c]⟩ => c == 42 && retOneB fi.type
    | _ => false
  | none => false

theorem retOneB_sound {d : Validation.DefType} (h : retOneB d = true) :
    ∃ ps rs, Validation.Expand d (.func ps rs) ∧ ps.toList = [] ∧ rs.length = 1 := by
  unfold retOneB Validation.DefType.funcType? at h
  split at h
  · rename_i t heq
    split at heq
    · rename_i ps rs hex
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      exact ⟨ps, rs, Validation.Expand.iff.mpr hex, heq.1, by simp [Validation.Ty.length, heq.2]⟩
    · cases heq
  · cases h

theorem callsB_sound {s : Store Empty} {a t' : Nat} (h : callsB s a t' = true) :
    ∃ (fi : FuncInst Empty) (fn : Func) (x : FuncIdx) (ps rs : Validation.Ty (.list .val)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧ fn.locals = [] ∧ fn.body = [.call x] ∧
      fi.module.funcs[x.toNat]? = some t' ∧ Validation.Expand fi.type (.func ps rs) ∧
      ps.toList = [] ∧ rs.length = 1 := by
  unfold callsB at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i ty x hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨ps, rs, he, hps, hrs⟩ := retOneB_sound h.2
      exact ⟨fi, _, x, ps, rs, hfi, hc, rfl, rfl, h.1, he, hps, hrs⟩
    · cases h
  · cases h

theorem constB_sound {s : Store Empty} {a : Nat} (h : constB s a = true) :
    ∃ (fi : FuncInst Empty) (fn : Func) (ps rs : Validation.Ty (.list .val)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧ fn.locals = [] ∧
      fn.body = [.intConst .i32 42] ∧ Validation.Expand fi.type (.func ps rs) ∧
      ps.toList = [] ∧ rs.length = 1 := by
  unfold constB at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i ty c hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨ps, rs, he, hps, hrs⟩ := retOneB_sound h.2
      exact ⟨fi, _, ps, rs, hfi, hc, rfl, by rw [h.1], he, hps, hrs⟩
    · cases h
  · cases h

/-! ## Kernel facts -/

theorem callMod_valid :
    ((Validation.validate? callMod).map fun mt => mt.imports.isEmpty) = some true := by
  decide +kernel

theorem inlineMod_valid :
    ((Validation.validate? inlineMod).map fun mt => mt.imports.isEmpty) = some true := by
  decide +kernel

theorem callMod_prep : ((prepare? evalConst? ({} : Store Empty) callMod []).map
    fun p => p.1.code.isEmpty && p.2.isNone) = some true := by decide +kernel

theorem inlineMod_prep : ((prepare? evalConst? ({} : Store Empty) inlineMod []).map
    fun p => p.1.code.isEmpty && p.2.isNone) = some true := by decide +kernel

theorem callStore_calls : callsB callStore 0 1 = true := by decide +kernel
theorem callStore_const : constB callStore 1 = true := by decide +kernel
theorem inlineStore_const : constB inlineStore 0 = true := by decide +kernel
theorem callStore_chk : Interp.storeChkB callStore.funcs = true := by decide +kernel
theorem inlineStore_chk : Interp.storeChkB inlineStore.funcs = true := by decide +kernel

/-- The views of the two stores are equal. -/
theorem codeView_eq : codeView callStore = codeView inlineStore := by decide +kernel

/-- The stores differ: the body of function `0`. -/
theorem callStore_ne : callsB inlineStore 0 1 = false := by decide +kernel

/-! ## Typing -/

theorem storeOk_empty : StoreOk ({} : Store Empty) := by
  constructor <;> simp

/-- The store of a valid module's instantiation, with no initialisation code and no start
function, is typed. -/
theorem prepStore_ok {m : Module}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : ((prepare? evalConst? ({} : Store Empty) m []).map
      fun p => p.1.code.isEmpty && p.2.isNone) = some true) : StoreOk (prepStore m) := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? m = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? m with _ | mt
    · simp [h] at hv
    · simp only [h, Option.map_some, Option.some.injEq] at hv
      exact ⟨mt, rfl, hv⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk m ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt,
      by rw [himp]; exact .nil⟩
  rcases hpr : prepare? evalConst? ({} : Store Empty) m [] with _ | ⟨c, st⟩
  · simp [hpr] at hp
  · have hst : st = none := by simp [hpr] at hp; exact hp.2
    subst hst
    have hI := (prepare?_sound (P := SingleThreaded.profile fun _ _ _ _ => false)
      (host := SingleThreaded.divHost) evalConst?_evalSound hpr hvalid).2
    have hc : ConfigOk c [] := Instantiate.ok SingleThreaded.divHost_ok storeOk_empty hI
    unfold prepStore
    rw [hpr]
    exact SingleThreaded.ConfigOk.storeOk hc

/-- On a typed and checked store whose function at `a` takes no parameters, the invocations
admitted by `InvOk` are those on the empty argument list. -/
theorem invOk_iff {s : Store Empty} {a : Nat} {fi : FuncInst Empty}
    {ps rs : Validation.Ty (.list .val)} (hs : StoreOk s) (hc : Interp.StoreChk s.funcs)
    (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hps : ps.toList = []) (vs : List Val) : InvOk s (a, vs) ↔ vs = [] := by
  constructor
  · rintro ⟨-, -, fi', ps', rs', hf', he', hv⟩
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    have h := Option.some.inj ((Validation.Expand.iff.mp he).symm.trans
      (Validation.Expand.iff.mp he'))
    injection h with h₁ h₂
    subst h₁
    rw [hps] at hv
    exact List.forall₂_nil_right_iff.mp hv
  · rintro rfl
    exact ⟨hs, hc, fi, ps, rs, hf, he, by rw [hps]; exact .nil⟩

end Silmaril.Proofs.Wasm.Abstract.PubViewExample
