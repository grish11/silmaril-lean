module

public import Silmaril.Proofs.Wasm.Cfg.Region

@[expose] public section

/-!
# Tail calls at the function's frame

A region run ending in a pending tail call (`Out.tail W a c`) is completed by the enclosing
`FRAME`: Core replaces the frame by the callee's (`return_call_ref-frame-addr`), on the top
`ps.length` values of `W`, and the callee's run is what the oracle answers (`CallSoundA`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem callSound_of_A (h : CallSoundA P host C) : CallSound P host C :=
  fun s s₁ f a fi ps rs us fl hfi hty hn hc =>
    h s s₁ f a fi ps rs us fl (.callRefType fi.type) trivial hfi hty hn hc

theorem expand_of_funcType {d : DefType} {ps rs : List CValType}
    (hf : d.funcType? = some (ps, rs)) : Expand d (.func (Ty.ofList ps) (Ty.ofList rs)) := by
  rw [Expand.iff]
  unfold DefType.funcType? at hf
  split at hf
  next P R hex =>
    obtain ⟨hP, hR⟩ : P.toList = ps ∧ R.toList = rs := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hf
    rw [← hP, ← hR, Ty.ofList_toList, Ty.ofList_toList]
    exact hex
  next => cases hf

theorem isCallRef_retToCallIn {c : Admin} (h : c.IsReturnCallRef) (m : ModuleInst) :
    (c.retToCallIn m).IsCallRef := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · simp only [Admin.retToCallIn]; split <;> trivial
  · trivial
  · exact h.elim

/-- **A pending tail call completed by the frame**: when a frame's body ends in a pending tail
call of the function at `a`, Core leaves the frame and calls the callee on the top
`ps.length` values (`return_call_ref-frame-addr`). With an oracle sound for every `call_ref`
form (`CallSoundA`), the frame runs to the callee's answer: its top `rs.length` results, a trap,
or its exception, in the callee's final store and the outer frame. -/
theorem frame_tail_sound (hC : CallSoundA P host C) {s s₂ s₃ : Store H} {f fi fi₂ : Frame}
    {n : Nat} {inner : List Admin} {W W₀ args : List Val} {a : Nat} {c : Admin}
    {fn : FuncInst H} {ps rs : List CValType} {fl : Binaryen.Flow}
    (h : RunC P host C s fi [] inner s₂ fi₂ (.tail W a c))
    (hfn : s₂.funcs[a]? = some fn) (hty : DefType.funcType? fn.type = some (ps, rs))
    (hW : W = W₀ ++ args) (hn : args.length = ps.length) (hcall : C s₂ a args (s₃, fl)) :
    (∀ vs, fl.retVals = some vs → Steps P host ⟨s, f, [.frame n fi inner]⟩
        ⟨s₃, f, vals (vs.take rs.length).reverse⟩) ∧
    (fl = .trap → Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s₃, f, [.trap]⟩) ∧
    (∀ t, fl = .throw t → Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s₃, f, throwing t⟩) := by
  subst hW
  obtain ⟨c', hs, hc, rest, rfl⟩ := soundC hC h
  have h1 := steps_frame (f := f) n (by simpa [vals] using hs)
  have h2 : Step P host
      ⟨s₂, f, [.frame n fi₂ (vals W₀ ++ vals args ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s₂, f, vals args ++ [.ref (.func a), c.retToCallIn fi₂.module]⟩ :=
    Step.returnCallRefFrameAddr hc hfn (expand_of_funcType hty) (by simp [Ty.length_ofList, hn])
  have hpre : Steps P host ⟨s, f, [.frame n fi inner]⟩
      ⟨s₂, f, vals args ++ [.ref (.func a), c.retToCallIn fi₂.module]⟩ :=
    h1.tail (by simpa [vals] using h2)
  obtain ⟨h3, h4, h5⟩ := hC s₂ s₃ f a fn ps rs args fl _ (isCallRef_retToCallIn hc fi₂.module)
    hfn hty hn hcall
  exact ⟨fun vs hv => hpre.trans (h3 vs hv), fun ht => hpre.trans (h4 ht),
    fun t ht => hpre.trans (h5 t ht)⟩

end Silmaril.Wasm.Cfg.Proofs.Region
