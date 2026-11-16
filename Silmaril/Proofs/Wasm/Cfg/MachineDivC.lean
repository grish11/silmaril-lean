module

public import Silmaril.Proofs.Wasm.Cfg.MachineCore
public import Silmaril.Proofs.Wasm.Cfg.RegionDiv

@[expose] public section

/-!
# Divergence of the machine with calls, against Core 3.0: soundness

`MDivC` (an infinite `MStepC` run, or a finite run to a block whose body reaches a call that
`D` says diverges) is Core 3.0 divergence of the code the start state stands for, when `C` is
Core-sound (`CallSound`) and `D` is (`DivCallSound`). An infinite run is one by `core_infinite`
(the anti-stutter measure is unchanged: an answered call only adds Core steps). A finite run to
a non-sink state is a Core run between the codes the states stand for (`msim`); the diverging
call then lifts through the block's code, its values and continuation, and the label and handler
frames of the label invariant (`wrap_div`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineDivC

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Cfg.Proofs.MachineCore

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- **Divergence lifts through the label frames** of the label invariant. -/
theorem wrap_div {body : Expr} {s : Store H} {f : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner X : List Admin},
      wrap body rp ls inner = some X → Diverges P host ⟨s, f, inner⟩ → Diverges P host ⟨s, f, X⟩
  | [], [], _, _, hX, h => by
    simp only [wrap, Option.some.injEq] at hX; subst hX; exact h
  | [], _ :: _, _, _, hX, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, hX, _ => by simp [wrap] at hX
  | (m, a) :: rp, L :: ls, inner, X, hX, h => by
    simp only [wrap, Option.bind_eq_bind] at hX
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some] at hX
          refine wrap_div rp ls hX ?_
          have hl := Proofs.Region.diverges_label (P := P) (host := host) L.arity (if L.loop then [t] else []) h
          have hx : Diverges P host
              ⟨s, f, [if L.tryT then Admin.handler L.arity L.catches
                [.label L.arity (if L.loop then [t] else []) inner]
                else .label L.arity (if L.loop then [t] else []) inner]⟩ := by
            cases L.tryT
            · simpa using hl
            · simpa using Proofs.Region.diverges_handler (P := P) (host := host) L.arity L.catches hl
          simpa using Proofs.Region.diverges_in (P := P) (host := host) L.outer (expression (restAt pc (m + 1))) hx

/-- A machine state with a step is at a block, so it is not a sink. -/
theorem not_sink_of_step {body : Expr} {st st₁ : MState H} (h : MStepC P host C body st st₁) :
    ¬ st.node.IsSink := by
  obtain ⟨b, hb⟩ := Proofs.Machine.mstep_from_block h
  rw [hb]; simp [Target.IsSink]

/-- **A finite machine run to a non-sink state is a Core run** between the codes the two states
stand for, the invariant kept. -/
theorem run_core (hC : CallSoundA P host C) {body : Expr} {st st' : MState H}
    (h : Relation.ReflTransGen (MStepC P host C body) st st') (hns : ¬ st'.node.IsSink) :
    ∀ {X : List Admin}, MInv body st → codeOf body st = some X →
      MInv body st' ∧ ∃ Y, codeOf body st' = some Y ∧
        Steps P host ⟨st.store, st.frame, X⟩ ⟨st'.store, st'.frame, Y⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hok hX => ⟨hok, _, hX, .refl⟩
  | @head st st₁ hs hrest ih =>
    intro X hok hX
    have hok₁ := (Proofs.Machine.mstep_sound hs hok hX).1
    obtain ⟨Y, hY⟩ := Proofs.Machine.codeOf_of_ok hok₁
    have hns₁ : ¬ st₁.node.IsSink := by
      rcases hrest.cases_head with rfl | ⟨_, h₁, _⟩
      · exact hns
      · exact not_sink_of_step h₁
    obtain ⟨hok', Z, hZ, hsteps⟩ := ih hok₁ hY
    exact ⟨hok', Z, hZ, (msim hC hs hok hX hY hns₁).1.trans hsteps⟩

/-- **A block whose body reaches a diverging call diverges in Core**: the code its state stands
for runs to the call, which diverges, inside the block's continuation and label frames. -/
theorem bodyCallDiv_core (hC : CallSoundA P host C) {D : Store H → Nat → List Val → Prop}
    (hD : DivCallSound P host D) {body : Expr} {st : MState H} {X : List Admin}
    (hX : codeOf body st = some X) (h : BodyCallDiv P host C D body st) :
    Diverges P host ⟨st.store, st.frame, X⟩ := by
  obtain ⟨node, stk, ls, s, f⟩ := st
  obtain ⟨b, sg, pre, post, x, s₁, f₁, ws, us, a, fi, ps, rs, hn, hb, hbody, hr, hfi, hty, hlen,
    hd⟩ := h
  simp only at hn hr; subst hn
  obtain ⟨c, hc, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only [codeOf, codeAt, hc, Option.bind_eq_bind, Option.bind_some] at hX
  set R := expression (post ++ sg.term.toList ++ restAt c (b.idx + 1)) with hR
  have hcode : vals stk ++ expression (restAt c b.idx) =
      vals stk ++ expression pre ++ .plain (.call x) :: R := by
    rw [Proofs.Machine.restAt_cons hsg]
    simp [Segment.instrs, hbody, expression, hR, List.append_assoc]
  obtain ⟨c', hs, he⟩ := Proofs.Region.soundC hC hr
  simp only [Out.Ends] at he; subst he
  have h1 : Steps P host ⟨s, f, vals stk ++ expression pre ++ .plain (.call x) :: R⟩
      ⟨s₁, f₁, vals (ws ++ us) ++ .plain (.call x) :: R⟩ := by
    simpa [List.append_assoc] using Proofs.Region.steps_in [] (.plain (.call x) :: R) hs
  have h2 := Proofs.Region.call_head (P := P) (host := host) (ws := ws) (us := us) (code := R) hfi
  have h3 : Diverges P host ⟨s₁, f₁, vals ws ++ (vals us ++ [.ref (.func a),
      .callRefType fi.type]) ++ R⟩ :=
    Proofs.Region.diverges_in ws R (hD s₁ f₁ a fi ps rs us _ trivial (Proofs.Region.func?_inv hfi).2 hty hlen hd)
  have hdiv : Diverges P host ⟨s, f, vals stk ++ expression (restAt c b.idx)⟩ := by
    rw [hcode]; exact InfiniteTrace.of_steps h1 (InfiniteTrace.fold h2 h3)
  exact wrap_div _ _ hX hdiv

/-- **Soundness of machine divergence with calls**: from a state satisfying the invariant,
`MDivC` is Core 3.0 divergence of the code the state stands for. -/
theorem mdivC_core (hC : CallSoundA P host C) {D : Store H → Nat → List Val → Prop}
    (hD : DivCallSound P host D) {body : Expr} {st : MState H} {X : List Admin}
    (hok : MInv body st) (hX : codeOf body st = some X) (h : MDivC P host C D body st) :
    Diverges P host ⟨st.store, st.frame, X⟩ := by
  rcases h with h | ⟨st', hrun, hd⟩
  · exact core_infinite hC hok hX h
  · have hns : ¬ st'.node.IsSink := by
      obtain ⟨b, _, _, _, _, _, _, _, _, _, _, _, _, hn, -⟩ := hd
      rw [hn]; simp [Target.IsSink]
    obtain ⟨-, Y, hY, hsteps⟩ := run_core hC hrun hns hok hX
    exact InfiniteTrace.of_steps hsteps (bodyCallDiv_core hC hD hY hd)

open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **Soundness from the CFG entry**: `MDivC` from the initial state is Core 3.0 divergence of
the body. -/
theorem mdivC_core_initial (hC : CallSoundA P host C) {D : Store H → Nat → List Val → Prop}
    (hD : DivCallSound P host D) {body : Expr} {s : Store H} {f : Frame}
    (h : MDivC P host C D body (initial body s f)) :
    Diverges P host ⟨s, f, expression body⟩ := by
  have hinit : initial body s f = goto (entry body [] 0) ([] : List SeqStep).length [] [] s f := by
    simp [initial, goto, popL, cfgEntry]
  have hok : MInv body (initial body s f) := by rw [hinit]; exact entry_ok (p := []) trivial
  have hns : ¬ (initial body s f).node.IsSink := by
    rcases h with h | ⟨st', hrun, hd⟩
    · exact MachineCore.not_sink_of_infinite h
    · rcases hrun.cases_head with rfl | ⟨_, h₁, _⟩
      · obtain ⟨b, _, _, _, _, _, _, _, _, _, _, _, _, hn, -⟩ := hd
        rw [hn]; simp [Target.IsSink]
      · exact not_sink_of_step h₁
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
  simpa [initial] using mdivC_core hC hD hok hY h

end Silmaril.Wasm.Cfg.Proofs.MachineDivC
