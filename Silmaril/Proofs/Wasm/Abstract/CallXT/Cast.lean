module

public import Silmaril.Wasm.Abstract.CallXT.Defs
public import Silmaril.Wasm.Validation.Subtyping.DefInv
public import Silmaril.Wasm.Execution.Core.Soundness.RefRetype
public import Silmaril.Wasm.Binaryen.Pass.DirectizeCast

/-!
Proofs for `Silmaril.Wasm.Abstract.CallXT.Thms`: **a function reference typed at
`ref null? y` has the counts of `y`** (`typeArity_of_refOk`). This discharges the
arity premise of `EvalOXT` for `call_indirect`, whose successful `ref.cast`
types the callee at `(ref null y)`, and for `call_ref` given its reference's
type.

A reference's typing chain starts at its own type `ref (defHeap fi.type)`; every
later type of the chain is the target of a `Ref_ok/sub`, hence valid, so the
chain composes (`refOk_func_sub`). Subtyping of defined function types keeps
their parameter and result counts (`Sub.defHeap_expand`, `Sub.list_length`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallXT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.CallXT

variable {H : Type}

/-- The typings of a function reference: its own type, or a valid supertype. -/
theorem refOk_func_sub {s : Store H} {a : Nat} {rt : CRefType} (h : RefOk s (.func a) rt) :
    ∃ fi, s.funcs[a]? = some fi ∧
      (rt = .ref false (.use (.dt fi.type)) ∨
        (TyOk {} rt ∧ Sub {} (.ref false (.use (.dt fi.type)) : CRefType) rt)) := by
  generalize hr : Ref.func a = r at h
  induction h with
  | func hf => cases hr; exact ⟨_, hf, .inl rfl⟩
  | @sub r rt rt' h hok hs ih =>
    obtain ⟨fi, hfi, hc⟩ := ih hr
    refine ⟨fi, hfi, .inr ⟨hok, ?_⟩⟩
    rcases hc with rfl | ⟨hok', hs'⟩
    · exact hs
    · exact Sub.trans DefInv.okEmpty hok' hs' hs
  | null | i31 | struct | array | exn | host | extern => cases hr

theorem funcType_of_expand {d : DefType} {ps rs : Ty (.list .val)} (h : Expand d (.func ps rs)) :
    DefType.funcType? d = some (ps.toList, rs.toList) := by
  simp [DefType.funcType?, Expand.iff.1 h]

theorem expand_of_funcType {d : DefType} {ps rs : List CValType}
    (h : DefType.funcType? d = some (ps, rs)) :
    ∃ ps' rs', Expand d (.func ps' rs') ∧ ps'.toList = ps ∧ rs'.toList = rs := by
  unfold DefType.funcType? at h
  split at h
  · rename_i ps' rs' he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨ps', rs', Expand.iff.2 he, h.1, h.2⟩
  · cases h

theorem expand_det {d : DefType} {c₁ c₂ : CCompType} (h₁ : Expand d c₁) (h₂ : Expand d c₂) :
    c₁ = c₂ := by
  rw [Expand.iff] at h₁ h₂; rw [h₁] at h₂; exact Option.some.inj h₂

/-- **Subtyping of defined types keeps function counts.** -/
theorem counts_of_sub {d₁ d₂ : DefType} (hs : Sub {} (.use (.dt d₁) : CHeapType) (.use (.dt d₂)))
    (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂) {ps rs : List CValType}
    (hty : DefType.funcType? d₁ = some (ps, rs)) :
    ∃ ps₂ rs₂, DefType.funcType? d₂ = some (ps₂, rs₂) ∧ ps₂.length = ps.length ∧
      rs₂.length = rs.length := by
  obtain ⟨ct₂, he₂⟩ := TyOk.exists_expand h₂
  obtain ⟨ct₁, he₁, hsub⟩ := Sub.defHeap_expand hs h₁ h₂ he₂
  obtain ⟨ps', rs', he, rfl, rfl⟩ := expand_of_funcType hty
  cases expand_det he₁ he
  cases hsub with
  | func hp hr =>
    exact ⟨_, _, funcType_of_expand he₂, (Sub.list_length hp), (Sub.list_length hr).symm⟩

/-- **A function reference typed at `ref null? y` has the counts of `y`.** -/
theorem typeArity_of_refOk {s : Store H} {a : Nat} {fi : FuncInst H} {mi : ModuleInst}
    {y : TypeIdx} {d : DefType} {n : Bool} {ps rs : List CValType}
    (hd : mi.types[y.toNat]? = some d) (hfi : s.funcs[a]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) (hdok : TyOk {} d)
    (h : RefOk s (.func a) (.ref n (.use (.dt d)))) :
    typeArity mi y = some (ps.length, rs.length) := by
  obtain ⟨fi', hfi', hc⟩ := refOk_func_sub h
  rw [hfi] at hfi'; cases hfi'
  have hheap : Sub {} (.use (.dt fi.type) : CHeapType) (.use (.dt d)) := by
    rcases hc with he | ⟨-, hs⟩
    · cases he; exact .heapRefl
    · cases hs with
      | refNonNull h => exact h
      | refNull h => exact h
  obtain ⟨ps₂, rs₂, h₂, hp, hr⟩ := counts_of_sub hheap hfiok hdok hty
  simp [typeArity, hd, h₂, hp, hr]

/-- **The arity premise of an indirect call**, from its successful cast. -/
theorem typeArity_of_cast {s : Store H} {a : Nat} {fi : FuncInst H} {mi : ModuleInst}
    {y : TypeIdx} {d : DefType} {ps rs : List CValType}
    (hd : mi.types[y.toNat]? = some d) (hfi : s.funcs[a]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hfiok : TyOk {} fi.type) (hdok : TyOk {} d)
    (h : RefOk s (.func a) (mi.instRef (Silmaril.Wasm.Abstract.CallRes.castTo y))) :
    typeArity mi y = some (ps.length, rs.length) := by
  rw [show Silmaril.Wasm.Abstract.CallRes.castTo y = ⟨true, .typeIdx y⟩ from rfl,
    Silmaril.Wasm.Binaryen.DirectizeCast.instRef_typeIdx hd] at h
  exact typeArity_of_refOk hd hfi hty hfiok hdok h

end Silmaril.Proofs.Wasm.Abstract.CallXT
