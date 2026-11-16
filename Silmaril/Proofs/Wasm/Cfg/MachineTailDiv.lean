module

public import Silmaril.Proofs.Wasm.Cfg.MachineDivC
public import Silmaril.Proofs.Wasm.Cfg.MachineTail

@[expose] public section

/-!
# Divergence through a tail callee, at the function's frame (proofs)

A tail call replaces the function's frame (`return_call_ref-frame-addr`), so divergence of its
callee is divergence of the function's `FRAME`, not of its body. A region run ending in a pending
tail call (`Out.tail`) is a Core run of the frame to the callee's call, outside the frame
(`frame_tail_div`), and that call diverges when `D` names it (`DivCallSound`). From the CFG entry,
`MDivT` (body divergence `MDivC`, or a finite run to a block ending in a tail call of a diverging
callee, `TailCallDiv`) is Core 3.0 divergence of the function's frame
`FRAME_n{fi} (LABEL_n{} body)` in any outer frame (`mdivT_frame_initial`). The caller's pending
code and handlers are not run: the frame step discards them.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineTailDiv

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Cfg.Proofs.Machine

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem diverges_frame {s : Store H} {f fi : Frame} {X : List Admin} (n : Nat)
    (h : Diverges P host ⟨s, fi, X⟩) : Diverges P host ⟨s, f, [.frame n fi X]⟩ :=
  InfiniteTrace.map (R := Step P host) (S := Step P host)
    (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtFrame hs) h

/-- **A pending tail call of a diverging callee makes the frame diverge**: a region run of the
frame's code ending in a pending tail call of `a` on `W₀ ++ args` runs in Core to the frame,
which steps to the call of `a` on `args` outside it (`return_call_ref-frame-addr`), and that call
diverges when `D` names it. -/
theorem frame_tail_div (hC : CallSoundA P host C) {D : Store H → Nat → List Val → Prop}
    (hD : DivCallSound P host D) {s s₂ : Store H} {f fi fi₂ : Frame} {n : Nat}
    {inner : List Admin} {W W₀ args : List Val} {a : Nat} {c : Admin} {fn : FuncInst H}
    {ps rs : List CValType} (h : RunC P host C s fi [] inner s₂ fi₂ (.tail W a c))
    (hfn : s₂.funcs[a]? = some fn) (hty : DefType.funcType? fn.type = some (ps, rs))
    (hW : W = W₀ ++ args) (hn : args.length = ps.length) (hd : D s₂ a args) :
    Diverges P host ⟨s, f, [.frame n fi inner]⟩ := by
  subst hW
  obtain ⟨c', hs, hc, rest, rfl⟩ := Proofs.Region.soundC hC h
  have h1 := Proofs.Region.steps_frame (f := f) n (by simpa [vals] using hs)
  have h2 : Step P host
      ⟨s₂, f, [.frame n fi₂ (vals W₀ ++ vals args ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s₂, f, vals args ++ [.ref (.func a), c.retToCallIn fi₂.module]⟩ :=
    Step.returnCallRefFrameAddr hc hfn (Proofs.Region.expand_of_funcType hty)
      (by simp [Ty.length_ofList, hn])
  have hpre : Steps P host ⟨s, f, [.frame n fi inner]⟩
      ⟨s₂, f, vals args ++ [.ref (.func a), c.retToCallIn fi₂.module]⟩ :=
    h1.tail (by simpa [vals] using h2)
  exact Proofs.Region.steps_div hpre (hD s₂ f a fn ps rs args _
    (Proofs.Region.isCallRef_retToCallIn hc fi₂.module) hfn hty hn hd)

/-- The CFG entry, when it is not a sink, satisfies the invariant and stands for the body. -/
theorem initial_code {body : Expr} {s : Store H} {f : Frame}
    (hns : ¬ (initial body s f).node.IsSink) :
    MInv body (initial body s f) ∧ codeOf body (initial body s f) = some (expression body) := by
  have hinit : initial body s f = goto (entry body [] 0) ([] : List SeqStep).length [] [] s f := by
    simp [initial, goto, popL, cfgEntry]
  have hok : MInv body (initial body s f) := by rw [hinit]; exact entry_ok (p := []) trivial
  obtain ⟨Y, hY⟩ := codeOf_of_ok hok
  have hYe : Y = expression body := by
    rw [hinit] at hY hns
    unfold entry at hY hns
    split at hY
    · simp [goto, depthT, popL, codeOf, codeAt, seqAt, restAt_zero, wrap, vals] at hY
      exact hY.symm
    · rename_i hl
      exfalso; apply hns; simp [goto, cont, contRev, Target.IsSink, hl]
  subst hYe
  exact ⟨hok, hY⟩

/-- **A block ending in a tail call of a diverging callee makes the frame diverge**, for the code
the block's state stands for. -/
theorem tailCallDiv_frame (hC : CallSoundA P host C) {D : Store H → Nat → List Val → Prop}
    (hD : DivCallSound P host D) {body : Expr} {st : MState H} {X : List Admin}
    (hX : codeOf body st = some X) (h : TailCallDiv P host C D body st) (n : Nat) (f : Frame) :
    Diverges P host ⟨st.store, f, [.frame n st.frame [.label n [] X]]⟩ := by
  obtain ⟨node, stk, ls, s, fr⟩ := st
  obtain ⟨b, sg, i, stk₁, s₁, s₂, f₁, f₂, W, a, c, fi, ps, rs, W₀, args, hn, hb, ht, -, hr, hth,
    hfi, hty, hW, hlen, hd⟩ := h
  simp only at hn hr hW; subst hn
  have hR := tail_sound hb ht hr hth (by simpa [codeOf] using hX)
  have hlab : RunC P host C s fr [] [.label n [] X] s₂ f₂ (.tail (brVals ls.length ls W) a c) := by
    simpa using (RunC.labelTail (P := P) (host := host) (C := C) (vs := []) (n := n) (cont := [])
      (code := []) hR)
  exact frame_tail_div hC hD hlab hfi hty hW hlen hd

/-- **Soundness of frame divergence from the CFG entry**: `MDivT` from the initial state is
Core 3.0 divergence of the function's frame `FRAME_n{fi} (LABEL_n{} body)`, in any outer frame. -/
theorem mdivT_frame_initial (hC : CallSoundA P host C) {D : Store H → Nat → List Val → Prop}
    (hD : DivCallSound P host D) {body : Expr} {s : Store H} {fi : Frame}
    (h : MDivT P host C D body (initial body s fi)) (n : Nat) (f : Frame) :
    Diverges P host ⟨s, f, [.frame n fi [.label n [] (expression body)]]⟩ := by
  rcases h with h | ⟨st', hrun, hd⟩
  · exact diverges_frame n (Proofs.Region.diverges_label n []
      (Proofs.MachineDivC.mdivC_core_initial hC hD h))
  · have hns' : ¬ st'.node.IsSink := by
      obtain ⟨b, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, -⟩ := hd
      rw [hn]; simp [Target.IsSink]
    have hns : ¬ (initial body s fi).node.IsSink := by
      rcases hrun.cases_head with rfl | ⟨_, h₁, _⟩
      · exact hns'
      · exact Proofs.MachineDivC.not_sink_of_step h₁
    obtain ⟨hok, hX⟩ := initial_code hns
    obtain ⟨-, Y, hY, hsteps⟩ := Proofs.MachineDivC.run_core hC hrun hns' hok hX
    have h1 := Proofs.Region.steps_frame (f := f) n
      (Proofs.Region.steps_label (P := P) (host := host) n [] hsteps)
    exact Proofs.Region.steps_div (by simpa [initial] using h1) (tailCallDiv_frame hC hD hY hd n f)

end Silmaril.Wasm.Cfg.Proofs.MachineTailDiv
