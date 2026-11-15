module

public import Silmaril.Proofs.Wasm.Cfg.Machine
public import Silmaril.Proofs.Wasm.Cfg.RegionTail

@[expose] public section

/-!
# Machine runs with tail calls, at the function's frame

`EndsC` without an oracle is `Ends` (`endsC_noCall`). A machine run from the CFG entry that ends
by a tail call is a Core 3.0 run of the function's `FRAME` to the sink's code
(`frame_tail_initial`): Core replaces the frame by the callee's, and the callee's run is what
the oracle answered.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Machine

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- With no call answered, `EndsC` is `Ends` in the state's own store and frame. -/
theorem endsC_noCall {st : MState H} {s₂ : Store H} {f₂ : Frame} {o : Out}
    (h : EndsC noCall st s₂ f₂ o) : Ends st o ∧ st.store = s₂ ∧ st.frame = f₂ := by
  cases o with
  | tail W a c =>
    obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hc, -⟩ := h
    exact hc.elim
  | _ => exact h

/-- The code of the sink a tail call's answer ends in. -/
theorem codeOf_tailEnd {body : Expr} {rs : Nat} {s : Store H} {f : Frame} {fl : Binaryen.Flow}
    {st : MState H} (h : tailEnd rs s f fl = some st) :
    st.store = s ∧
      ((∃ vs, fl.retVals = some vs ∧ codeOf body st = some (vals (vs.take rs).reverse)) ∨
        (fl = .trap ∧ codeOf body st = some [.trap]) ∨
        (∃ t, fl = .throw t ∧ codeOf body st = some (throwing t))) := by
  unfold tailEnd at h
  split at h
  · cases h; exact ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
  · cases h; exact ⟨rfl, .inr (.inr ⟨_, rfl, by simp [codeOf]⟩)⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨vs, hv, rfl⟩ := h
    exact ⟨rfl, .inl ⟨vs, hv, by simp [codeOf]⟩⟩

/-- **A run from the CFG entry that ends by a tail call is a Core run of the function's frame**:
the frame `FRAME_n{fi} (LABEL_n{} body)` runs, in any outer frame `f`, to the code of the sink
the machine reached (the callee's results, its trap or its exception), in the sink's store.
Under the named hypothesis `CallSoundA` on the oracle. -/
theorem frame_tail_initial (hC : CallSoundA P host C) {body : Expr} {s : Store H} {fi : Frame}
    {st' : MState H} {s₂ : Store H} {f₂ : Frame} {W : List Val} {a : Nat} {c : Admin}
    (hE : EndsC C st' s₂ f₂ (.tail W a c))
    (hR : RunC P host C s fi [] (expression body) s₂ f₂ (.tail W a c)) (n : Nat) (f : Frame)
    {X : List Admin} (hX : codeOf body st' = some X) :
    Steps P host ⟨s, f, [.frame n fi [.label n [] (expression body)]]⟩ ⟨st'.store, f, X⟩ := by
  obtain ⟨fn, ps, rs, W₀, args, fl, s₃, hfn, hty, hW, hn, hcall, hend⟩ := hE
  have hlab : RunC P host C s fi [] [.label n [] (expression body)] s₂ f₂ (.tail W a c) := by
    simpa using (RunC.labelTail (P := P) (host := host) (C := C) (vs := []) (n := n) (cont := [])
      (code := []) hR)
  obtain ⟨h1, h2, h3⟩ := Proofs.Region.frame_tail_sound (f := f) (n := n) hC hlab hfn hty hW hn
    hcall
  obtain ⟨hs, ⟨vs, hv, hc⟩ | ⟨ht, hc⟩ | ⟨t, ht, hc⟩⟩ := codeOf_tailEnd (body := body) hend
  · rw [hX] at hc; cases hc; rw [hs]; exact h1 vs hv
  · rw [hX] at hc; cases hc; rw [hs]; exact h2 ht
  · rw [hX] at hc; cases hc; rw [hs]; exact h3 t ht

end Silmaril.Wasm.Cfg.Proofs.Machine
