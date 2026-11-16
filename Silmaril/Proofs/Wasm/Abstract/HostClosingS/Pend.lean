module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Core

/-!
# Session pending calls are the canonical pending calls (proofs)

A pending call carries no end, and the calls before it are answered by values or exceptions (the
reach's prefix runs end normally, and the resolved calls return), so the session and canonical
pending calls coincide:

* `reachLXPS_toH`, `reachLXP_toS`: the reaches correspond, logs mapped by `oToS`;
* `pendS_toH`, `pend_toS`: so do the pending calls, the resolved prefixes through the projection
  (`substPre_toOld`, `substPre_toS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingS

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Games.Abstract.StratSession (eraseEnd)

variable {H : Type}

/-- **A session reach is a canonical reach.** -/
theorem reachLXPS_toH {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXPS s f stk es l z) :
    ∃ l', l = l'.map oToS ∧ ReachLXP s f stk es l' z := by
  induction h with
  | call hargs hfi hty =>
    obtain ⟨l', rfl, h'⟩ := (evalLXPS_toH hargs).ok (by simp)
    exact ⟨l', rfl, .call h' hfi hty⟩
  | ind hargs hres hfi hty hy =>
    obtain ⟨l', rfl, h'⟩ := (evalLXPS_toH hargs).ok (by simp)
    exact ⟨l', rfl, .ind h' hres hfi hty hy⟩
  | ref hargs hfi hty hy =>
    obtain ⟨l', rfl, h'⟩ := (evalLXPS_toH hargs).ok (by simp)
    exact ⟨l', rfl, .ref h' hfi hty hy⟩
  | args _ ih =>
    obtain ⟨l', rfl, h'⟩ := ih
    exact ⟨l', rfl, .args h'⟩
  | callK hargs hfi hty _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hargs).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .callK h₁ hfi hty h₂⟩
  | indK hargs hres hfi hty hy _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hargs).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .indK h₁ hres hfi hty hy h₂⟩
  | refK hargs hfi hty hy _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hargs).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .refK h₁ hfi hty hy h₂⟩
  | opK hi hargs hflat _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hargs).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .opK hi h₁ hflat h₂⟩
  | block har _ ih =>
    obtain ⟨l', rfl, h'⟩ := ih
    exact ⟨l', rfl, .block har h'⟩
  | blockK har hbody hvs _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hbody).ok (ne_trap_of_blockVals hvs)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .blockK har h₁ hvs h₂⟩
  | loop har _ ih =>
    obtain ⟨l', rfl, h'⟩ := ih
    exact ⟨l', rfl, .loop har h'⟩
  | loopK har hbody _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hbody).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .loopK har h₁ h₂⟩
  | loopBack har hbody _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hbody).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .loopBack har h₁ h₂⟩
  | cond _ ih =>
    obtain ⟨l', rfl, h'⟩ := ih
    exact ⟨l', rfl, .cond h'⟩
  | arm hc hb har _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hc).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .arm h₁ hb har h₂⟩
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hc).ok (by simp)
    obtain ⟨l₂, rfl, h₂⟩ := (evalLXPS_toH harm).ok (ne_trap_of_blockVals hvs)
    obtain ⟨l₃, rfl, h₃⟩ := ih
    exact ⟨l₁ ++ l₂ ++ l₃, by simp, .ifK h₁ hb har h₂ hvs h₃⟩
  | handler har _ ih =>
    obtain ⟨l', rfl, h'⟩ := ih
    exact ⟨l', rfl, .handler har h'⟩
  | tryK har hbody hvs _ ih =>
    obtain ⟨l₁, rfl, h₁⟩ := (evalLXPS_toH hbody).ok (ne_trap_of_blockVals hvs)
    obtain ⟨l₂, rfl, h₂⟩ := ih
    exact ⟨_, by simp, .tryK har h₁ hvs h₂⟩

/-- **A canonical reach is a session reach.** -/
theorem reachLXP_toS {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXP s f stk es l z) :
    ReachLXPS s f stk es (l.map oToS) z := by
  induction h with
  | call hargs hfi hty => exact .call (evalLXPh_toS_ok hargs (by simp)) hfi hty
  | ind hargs hres hfi hty hy => exact .ind (evalLXPh_toS_ok hargs (by simp)) hres hfi hty hy
  | ref hargs hfi hty hy => exact .ref (evalLXPh_toS_ok hargs (by simp)) hfi hty hy
  | args _ ih => exact .args ih
  | callK hargs hfi hty _ ih =>
    simpa using ReachLXPS.callK (evalLXPh_toS_ok hargs (by simp)) hfi hty ih
  | indK hargs hres hfi hty hy _ ih =>
    simpa using ReachLXPS.indK (evalLXPh_toS_ok hargs (by simp)) hres hfi hty hy ih
  | refK hargs hfi hty hy _ ih =>
    simpa using ReachLXPS.refK (evalLXPh_toS_ok hargs (by simp)) hfi hty hy ih
  | opK hi hargs hflat _ ih =>
    simpa using ReachLXPS.opK hi (evalLXPh_toS_ok hargs (by simp)) hflat ih
  | block har _ ih => exact .block har ih
  | blockK har hbody hvs _ ih =>
    simpa using ReachLXPS.blockK har (evalLXPh_toS_ok hbody (ne_trap_of_blockVals hvs)) hvs ih
  | loop har _ ih => exact .loop har ih
  | loopK har hbody _ ih =>
    simpa using ReachLXPS.loopK har (evalLXPh_toS_ok hbody (by simp)) ih
  | loopBack har hbody _ ih =>
    simpa using ReachLXPS.loopBack har (evalLXPh_toS_ok hbody (by simp)) ih
  | cond _ ih => exact .cond ih
  | arm hc hb har _ ih =>
    simpa using ReachLXPS.arm (evalLXPh_toS_ok hc (by simp)) hb har ih
  | ifK hc hb har harm hvs _ ih =>
    simpa using ReachLXPS.ifK (evalLXPh_toS_ok hc (by simp)) hb har
      (evalLXPh_toS_ok harm (ne_trap_of_blockVals hvs)) hvs ih
  | handler har _ ih => exact .handler har ih
  | tryK har hbody hvs _ ih =>
    simpa using ReachLXPS.tryK har (evalLXPh_toS_ok hbody (ne_trap_of_blockVals hvs)) hvs ih

/-- **A session pending call is a canonical pending call.** -/
theorem pendS_toH {s : Store H} {a : Nat} {vs : List Val} {q : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : PendLXPS s a vs q m) : PendLXP s a vs q m := by
  induction h with
  | self hf hcode => exact .self hf hcode
  | desc hf hcode hr hq _ ih =>
    obtain ⟨l', rfl, hr'⟩ := reachLXPS_toH hr
    exact .desc hf hcode hr' (substPre_toOld le_rfl l' hq) ih
  | tail hf hcode hbody hq _ ih =>
    obtain ⟨l', rfl, h'⟩ := (evalLXPS_toH hbody).ok (by simp)
    exact .tail hf hcode h' (substPre_toOld le_rfl l' hq) ih

/-- **A canonical pending call is a session pending call.** -/
theorem pend_toS {s : Store H} {a : Nat} {vs : List Val} {q : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : PendLXP s a vs q m) : PendLXPS s a vs q m := by
  have hc : ∀ g s a (y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)),
      y ∈ Shape.close wasmHOpenXP g s a →
      ∃ y' ∈ Shape.close wasmHOpenXPS g s a, y'.1 = y.1 ∧ eraseEnd y'.2 = y.2 :=
    fun _ _ _ _ h => close_lift h
  induction h with
  | self hf hcode => exact .self hf hcode
  | desc hf hcode hr hq _ ih =>
    exact .desc hf hcode (reachLXP_toS hr) (by rw [← map_lift_hToS]; exact substPre_toS hc hq) ih
  | tail hf hcode hbody hq _ ih =>
    exact .tail hf hcode (evalLXPh_toS_ok hbody (by simp)) (by rw [← map_lift_hToS]; exact substPre_toS hc hq) ih

end Silmaril.Proofs.Wasm.Abstract.HostClosingS
