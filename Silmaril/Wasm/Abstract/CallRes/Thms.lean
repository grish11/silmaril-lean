module

public import Silmaril.Wasm.Abstract.CallRes.Defs

/-!
# Resolving indirect calls: Core 3.0 runs

* `steps_callIndirect_func`: a resolved `call_indirect x y` runs in Core 3.0 to
  `call_ref y` on the callee's function reference;
* `steps_callIndirect_trap`: an unresolved one runs to a trap;
* the same for `return_call_indirect` (`steps_returnCallIndirect_func`,
  `steps_returnCallIndirect_trap`), towards `return_call_ref y`;
* `indRes_cases`: on a defined table, the index resolves (callee or trap), or
  the entry is a non-null, non-function reference passing the cast (Core is
  stuck there).
-/

public section

namespace Silmaril.Wasm.Abstract.CallRes

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem aconst_eq (a : AddrType) (i : BitVec a.intType.width) :
    vals [.num ⟨.int a.intType, i⟩] = [aconst a i] := rfl

/-- The common prefix: `call_indirect`/`return_call_indirect` unfolds into
`table.get; ref.cast; c`. -/
theorem steps_tableGet_cast {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {a : AddrType} {i : BitVec a.intType.width} {c : Admin} {ta : Nat} {ti : TableInst} {r : Ref}
    (ht : s.table? f x = some (ta, ti)) (hr : ti.refs[i.toNat]? = some r) :
    Steps P host ⟨s, f, [aconst a i, .plain (.tableGet x), .plain (.refCast (castTo y)), c]⟩
      ⟨s, f, [.ref r, .plain (.refCast (castTo y)), c]⟩ := by
  have h := Step.ctxtInstrs (P := P) (host := host) (vs := [])
    (rest := [.plain (.refCast (castTo y)), c])
    (Step.table (TableStep.getVal (P := P) (a := a) (i := i) ht hr)) (.inr (by simp))
  exact .single h

theorem steps_cast_ok {s : Store H} {f : Frame} {y : TypeIdx} {c : Admin} {r : Ref}
    (hc : RefOk s r (f.module.instRef (castTo y))) :
    Steps P host ⟨s, f, [.ref r, .plain (.refCast (castTo y)), c]⟩ ⟨s, f, [.ref r, c]⟩ := by
  have h := Step.ctxtInstrs (P := P) (host := host) (vs := []) (rest := [c])
    (Step.reference (RefStep.castSucceed hc)) (.inr (by simp))
  exact .single h

/-- **A resolved indirect call is `call_ref` on the callee.** -/
theorem steps_callIndirect_func {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {a : AddrType} {i : BitVec a.intType.width} {fa : Nat} (h : IndRes s f x y a i (some fa)) :
    Steps P host ⟨s, f, [aconst a i, .plain (.callIndirect x y)]⟩
      ⟨s, f, [.ref (.func fa), .plain (.callRef y)]⟩ := by
  cases h with
  | func ht hr hc =>
    have h₀ := Step.ctxtInstrs (P := P) (host := host) (vs := [.num ⟨.int a.intType, i⟩])
      (rest := []) (Step.callIndirect (s := s) (f := f) (x := x) (y := y)) (.inl (by simp))
    refine .head h₀ ?_
    exact (steps_tableGet_cast ht hr).trans (steps_cast_ok hc)

/-- **An unresolved indirect call traps.** -/
theorem steps_callIndirect_trap {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {a : AddrType} {i : BitVec a.intType.width} (h : IndRes s f x y a i none) :
    Steps P host ⟨s, f, [aconst a i, .plain (.callIndirect x y)]⟩ ⟨s, f, [.trap]⟩ := by
  have h₀ := Step.ctxtInstrs (P := P) (host := host) (vs := [.num ⟨.int a.intType, i⟩])
    (rest := []) (Step.callIndirect (s := s) (f := f) (x := x) (y := y)) (.inl (by simp))
  refine .head h₀ ?_
  cases h with
  | oob ht hl =>
    have h₁ := Step.ctxtInstrs (P := P) (host := host) (vs := [])
      (rest := [.plain (.refCast (castTo y)), .plain (.callRef y)])
      (Step.table (TableStep.getOob (P := P) (a := a) (i := i) ht hl)) (.inr (by simp))
    refine .head h₁ (.single ?_)
    exact Step.trapInstrs (P := P) (host := host) (s := s) (f := f) (vs := [])
      (rest := [.plain (.refCast (castTo y)), .plain (.callRef y)]) (.inr (by simp))
  | castFail ht hr hc =>
    refine (steps_tableGet_cast ht hr).trans ?_
    have h₁ := Step.ctxtInstrs (P := P) (host := host) (vs := []) (rest := [.plain (.callRef y)])
      (Step.reference (RefStep.castFail hc)) (.inr (by simp))
    refine .head h₁ (.single ?_)
    exact Step.trapInstrs (P := P) (host := host) (s := s) (f := f) (vs := [])
      (rest := [.plain (.callRef y)]) (.inr (by simp))
  | null ht hr hc =>
    refine (steps_tableGet_cast ht hr).trans ((steps_cast_ok hc).tail ?_)
    exact Step.callRefNull (c := .plain (.callRef y)) trivial

/-- A resolved `return_call_indirect` is `return_call_ref` on the callee. -/
theorem steps_returnCallIndirect_func {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {a : AddrType} {i : BitVec a.intType.width} {fa : Nat} (h : IndRes s f x y a i (some fa)) :
    Steps P host ⟨s, f, [aconst a i, .plain (.returnCallIndirect x y)]⟩
      ⟨s, f, [.ref (.func fa), .plain (.returnCallRef y)]⟩ := by
  cases h with
  | func ht hr hc =>
    have h₀ := Step.ctxtInstrs (P := P) (host := host) (vs := [.num ⟨.int a.intType, i⟩])
      (rest := []) (Step.returnCallIndirect (s := s) (f := f) (x := x) (y := y)) (.inl (by simp))
    refine .head h₀ ?_
    exact (steps_tableGet_cast ht hr).trans (steps_cast_ok hc)

/-- An unresolved `return_call_indirect` traps, except on a null entry, which
reaches `return_call_ref` on null (it traps once the enclosing frame is
reached, `return_call_ref-frame-null`). -/
theorem steps_returnCallIndirect_trap {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {a : AddrType} {i : BitVec a.intType.width} (h : IndRes s f x y a i none) :
    Steps P host ⟨s, f, [aconst a i, .plain (.returnCallIndirect x y)]⟩ ⟨s, f, [.trap]⟩ ∨
      Steps P host ⟨s, f, [aconst a i, .plain (.returnCallIndirect x y)]⟩
        ⟨s, f, [.ref .null, .plain (.returnCallRef y)]⟩ := by
  have h₀ := Step.ctxtInstrs (P := P) (host := host) (vs := [.num ⟨.int a.intType, i⟩])
    (rest := []) (Step.returnCallIndirect (s := s) (f := f) (x := x) (y := y)) (.inl (by simp))
  cases h with
  | oob ht hl =>
    left
    refine .head h₀ ?_
    have h₁ := Step.ctxtInstrs (P := P) (host := host) (vs := [])
      (rest := [.plain (.refCast (castTo y)), .plain (.returnCallRef y)])
      (Step.table (TableStep.getOob (P := P) (a := a) (i := i) ht hl)) (.inr (by simp))
    refine .head h₁ (.single ?_)
    exact Step.trapInstrs (P := P) (host := host) (s := s) (f := f) (vs := [])
      (rest := [.plain (.refCast (castTo y)), .plain (.returnCallRef y)]) (.inr (by simp))
  | castFail ht hr hc =>
    left
    refine .head h₀ ((steps_tableGet_cast ht hr).trans ?_)
    have h₁ := Step.ctxtInstrs (P := P) (host := host) (vs := []) (rest := [.plain (.returnCallRef y)])
      (Step.reference (RefStep.castFail hc)) (.inr (by simp))
    refine .head h₁ (.single ?_)
    exact Step.trapInstrs (P := P) (host := host) (s := s) (f := f) (vs := [])
      (rest := [.plain (.returnCallRef y)]) (.inr (by simp))
  | null ht hr hc =>
    right
    exact .head h₀ ((steps_tableGet_cast ht hr).trans (steps_cast_ok hc))

/-- **Resolution is total up to stuck entries.** On a defined table, the index
resolves (callee or trap), or the entry is a non-null, non-function reference
passing the cast, where Core 3.0 has no continuation. -/
theorem indRes_cases {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {a : AddrType}
    {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst} (ht : s.table? f x = some (ta, ti)) :
    (∃ r, IndRes s f x y a i r) ∨
      ∃ r, ti.refs[i.toNat]? = some r ∧ r ≠ .null ∧ (∀ fa, r ≠ .func fa) ∧
        RefOk s r (f.module.instRef (castTo y)) := by
  classical
  cases hr : ti.refs[i.toNat]? with
  | none => exact .inl ⟨none, .oob ht (List.getElem?_eq_none_iff.1 hr)⟩
  | some r =>
    by_cases hc : RefOk s r (f.module.instRef (castTo y))
    · cases r with
      | null => exact .inl ⟨_, .null ht hr hc⟩
      | func fa => exact .inl ⟨_, .func ht hr hc⟩
      | _ => exact .inr ⟨_, rfl, by simp, by simp, hc⟩
    · exact .inl ⟨_, .castFail ht hr hc⟩

/-- **Resolution is deterministic.** -/
theorem indRes_unique {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {a : AddrType}
    {i : BitVec a.intType.width} {r₁ r₂ : Option Nat} (h₁ : IndRes s f x y a i r₁)
    (h₂ : IndRes s f x y a i r₂) : r₁ = r₂ := by
  cases h₁ <;> cases h₂ <;> (try rfl) <;> simp_all

end Silmaril.Wasm.Abstract.CallRes
