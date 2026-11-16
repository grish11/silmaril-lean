module

public import Silmaril.Proofs.Wasm.Cfg.MachineTailDiv
public import Silmaril.Proofs.Wasm.Cfg.MachineComplete
public import Silmaril.Proofs.Wasm.Cfg.RegionDivC
public import Silmaril.Proofs.Wasm.Cfg.BridgeBwdTree
public import Silmaril.Proofs.Wasm.Cfg.MachineDiv
public import Silmaril.Proofs.Wasm.Cfg.RegionAtom

@[expose] public section

/-!
# Frame divergence is machine frame divergence (proofs): completeness

A diverging Core run of a function's frame `FRAME_n{F} (LABEL_n{} body)` either diverges inside
the frame forever, which is divergence of the body (inside its label: a label exit stops), or
leaves the frame. The frame's exits stop (values, `return`, a trap, an exception, a tail call of
null), except a tail call of a function (`return_call_ref-frame-addr`), whose call then
diverges. In the first case the body diverges, so `MDivC` holds (`core_div_initialC`). In the
second, the body runs in the region semantics to the pending tail call (`run_completeC`), the
machine reaches the block of that tail call without needing an answer
(`run_complete_tail_block`), and the callee diverges, which `D` names (`DivCallComplete`, its
guard at the tail call by `TailGuarded`): `TailCallDiv`. So Core frame divergence is `MDivT`
(`frame_div_complete`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineFrameDiv

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Cfg.Proofs.Machine Silmaril.Wasm.Cfg.Proofs.Region

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- **Leaving a frame**: a diverging frame diverges inside, or runs inside to an exit after which
it diverges. -/
theorem frame_exit {s : Store H} {g F : Frame} {n : Nat} {X : List Admin}
    (hd : Diverges P host ⟨s, g, [.frame n F X]⟩) :
    Diverges P host ⟨s, F, X⟩ ∨
      ∃ a : Config H, Steps P host ⟨s, F, X⟩ a ∧ ∃ out, FrameExit a.store a.frame n a.code out ∧
        Diverges P host ⟨a.store, g, out⟩ := by
  let plug : Config H → Config H := fun x => ⟨x.store, g, [.frame n x.frame x.code]⟩
  let bd : Config H → Config H → Prop := fun a b =>
    ∃ out, FrameExit a.store a.frame n a.code out ∧ b = ⟨a.store, g, out⟩
  have peel : ∀ a b, Step P host (plug a) b → (∃ next, Step P host a next ∧ b = plug next) ∨ bd a b := by
    intro a b hs
    rcases a with ⟨sa, fa, xa⟩
    rcases Step.frame_inv hs with ⟨s', f', is', hs', rfl⟩ | ⟨out, hx, rfl⟩
    · exact .inl ⟨⟨s', f', is'⟩, hs', by simp [plug]⟩
    · exact .inr ⟨out, hx, rfl⟩
  have hd' : InfiniteTrace (Step P host) (plug ⟨s, F, X⟩) := hd
  rcases InfiniteTrace.context_decompose (Step P host) (Step P host) plug bd peel hd' with
    hin | ⟨a, b, hr, ⟨out, hx, rfl⟩, hb⟩
  · exact .inl hin
  · exact .inr ⟨a, hr, out, hx, hb⟩

theorem vals_not_div {s : Store H} {f : Frame} {vs : List Val} :
    ¬ Diverges P host ⟨s, f, vals vs⟩ := fun h => by
  obtain ⟨_, hs, -⟩ := h.unfold
  exact Sim.Step.not_vals hs

/-- **Inside a function label, a body that leaves the label does not diverge**: the label's
exits stop outside any frame. -/
theorem label_exit_not_div {s : Store H} {f : Frame} {n : Nat} {X out : List Admin}
    (hx : LabelExit n [] X out) (hb : Diverges P host ⟨s, f, vals [] ++ out ++ []⟩) :
    False := by
  cases hx with
  | vals ws => exact vals_not_div (by simpa using hb)
  | brZero hl hn => exact vals_not_div (by simpa [expression] using hb)
  | @brSucc us l rest _ =>
    obtain ⟨c', hs, -⟩ := hb.unfold
    exact br_stuck_seq (vs := us) (rest := []) (by simpa using hs)
  | @ret us rest =>
    obtain ⟨c', hs, -⟩ := hb.unfold
    exact ret_stuck_seq (vs := us) (rest := []) (by simpa using hs)
  | @returnCall us c rest hc' => exact retCall_not_div (vs := us) (es := []) hc' (by simpa using hb)
  | throw a => exact throwForm_not_div ⟨[], a, [], by simp⟩ hb
  | trap => exact trapForm_not_div ⟨[], [], by simp⟩ hb

/-- A region run of values ends normally. -/
theorem run_vals_out {s s' : Store H} {f f' : Frame} {ws us : List Val} {o : Out}
    (h : RunC P host C s f ws (vals us) s' f' o) : ∃ vs, o = .normal vs := by
  have h' := run_vals_inv (code := []) (by simpa using h)
  exact ⟨_, (run_nil_inv h').1⟩

/-- **A function label ending in a pending tail call**: its body does, over the same values. -/
theorem label_tail_inv {s s' : Store H} {f f' : Frame} {n : Nat} {inner : List Admin}
    {W : List Val} {a : Nat} {c : Admin}
    (h : RunC P host C s f [] [.label n [] inner] s' f' (.tail W a c)) :
    RunC P host C s f [] inner s' f' (.tail W a c) := by
  rcases Bridge.run_label_inv h with ⟨s₁, f₁, us, -, h₂⟩ | ⟨s₁, f₁, us₁, us₂, -, -, h₂⟩ |
    ⟨oi, hin, hx⟩
  · cases (run_nil_inv h₂).1
  · obtain ⟨vs, he⟩ := run_vals_out (ws := []) (by simpa [expression] using h₂); simp at he
  · cases oi with
    | tail us a' c' =>
      simp only [Bridge.LabelExit, Out.tail.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      simpa using hin
    | br l us => cases l <;> simp [Bridge.LabelExit] at hx
    | _ => simp [Bridge.LabelExit] at hx

/-- **Completeness of frame divergence**: under a complete oracle and divergence predicate, their
guard holding at every call and every tail call the run reaches and pending tail calls well
placed, a diverging Core run of the function's frame `FRAME_n{F} (LABEL_n{} body)` (any outer
frame `g`) of a body of the fragment with calls is `MDivT` from the CFG entry. -/
theorem frame_div_complete {G D : Store H → Nat → List Val → Prop}
    (hC : CallCompleteG P host G C) (hD : DivCallComplete P host G D) {body : Expr}
    {s : Store H} {g F : Frame} {n : Nat} (hF : FragC (expression body))
    (hG : GuardedCalls P host G ⟨s, F, [.label n [] (expression body)]⟩)
    (hW : TailsOk P host ⟨s, F, [.label n [] (expression body)]⟩)
    (hGt : TailGuarded P host G ⟨s, F, [.label n [] (expression body)]⟩)
    (h : Diverges P host ⟨s, g, [.frame n F [.label n [] (expression body)]]⟩) :
    MDivT P host C D body (initial body s F) := by
  have hFl : FragC [.label n [] (expression body)] := fun x hx => by
    simp at hx; subst hx; exact .label (by simp) hF
  rcases frame_exit h with hin | ⟨a, hr, out, hx, hb⟩
  · -- the frame diverges inside: the body diverges
    rcases label_exit (vs := []) (code := []) (by simpa using hin) with hbody | ⟨a, -, out, hx, hb⟩
    · have hGT := gt_label (P := P) (host := host) (G := G) ⟨hG, hW⟩
      exact .inl (MachineDiv.run_divC_initial (div_completeC (vs := []) atom_term hC hD hF
        (by simpa using hGT.1) (by simpa using hGT.2) (by simpa using hbody)))
    · exact (label_exit_not_div hx hb).elim
  · -- the frame is left: only a tail call of a function diverges after it
    obtain ⟨sa, fa, xa⟩ := a
    cases hx with
    | vals hn => exact (vals_not_div hb).elim
    | ret hn => exact (vals_not_div hb).elim
    | trap => exact (trapForm_not_div ⟨[], [], rfl⟩ hb).elim
    | throw t => exact (throwForm_not_div ⟨[], t, [], by simp⟩ hb).elim
    | returnCallNull hc => exact (trapForm_not_div ⟨[], [], rfl⟩ hb).elim
    | @returnCallAddr vs' vs a c rest fn ps rs hc hf he hn =>
      have hends : (Out.tail (vs' ++ vs) a c).Ends
          (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) := ⟨hc, rest, by simp⟩
      have hrun := Region.run_completeC hC hG hW hFl hr hends
      have hbody := label_tail_inv hrun
      obtain ⟨st₁, hr₁, b, sg, i, stk₁, s₁, f₁, W, hnb, hb', ht, hi, hpre, hth, hbr⟩ :=
        MachineComplete.run_complete_tail_block hbody
      have hGa := hGt _ vs' vs a c rest fn ps rs hr (by simp) hc hf he hn
      have hty := funcType_of_expand he
      have hDa := hD sa g a fn _ _ vs (c.retToCallIn fa.module) hGa
        (isCallRef_retToCallIn hc fa.module) hf hty hn hb
      exact .inr ⟨st₁, hr₁, b, sg, i, stk₁, s₁, sa, f₁, fa, W, a, c, fn, _, _, vs', vs, hnb, hb', ht,
        hi, hpre, hth, hf, hty, hbr, hn, hDa⟩

end Silmaril.Wasm.Cfg.Proofs.MachineFrameDiv
