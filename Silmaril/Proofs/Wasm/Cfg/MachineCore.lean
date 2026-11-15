module

public import Silmaril.Proofs.Wasm.Cfg.Machine
import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-!
# Machine steps as Core 3.0 runs: the context layer

Towards the converse of divergence (an infinite machine run is a diverging Core run): the
region code a machine state stands for (`codeAt`/`wrap`) reduces in Core 3.0 inside its label
frames, and a block's body run is a Core run of the block's code up to its terminator.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineCore

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem steps_handler {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cs : List Catch) (h : Steps P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps P host ⟨s, f, [.handler n cs X]⟩ ⟨s', f', [.handler n cs Y]⟩ :=
  Steps.handler h

theorem steps_label {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cont : List Instr) (h : Steps P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps P host ⟨s, f, [.label n cont X]⟩ ⟨s', f', [.label n cont Y]⟩ :=
  Steps.label h

/-- **Core runs lift through the label frames** of the label invariant. -/
theorem wrap_steps {body : Expr} {s s' : Store H} {f f' : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner inner' X X' : List Admin},
      wrap body rp ls inner = some X → wrap body rp ls inner' = some X' →
      Steps P host ⟨s, f, inner⟩ ⟨s', f', inner'⟩ → Steps P host ⟨s, f, X⟩ ⟨s', f', X'⟩
  | [], [], _, _, _, _, hX, hX', h => by
    simp only [wrap, Option.some.injEq] at hX hX'; subst hX hX'; exact h
  | [], _ :: _, _, _, _, _, hX, _, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, _, hX, _, _ => by simp [wrap] at hX
  | (m, a) :: rp, L :: ls, inner, inner', X, X', hX, hX', h => by
    simp only [wrap, Option.bind_eq_bind] at hX hX'
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some] at hX hX'
          refine wrap_steps rp ls hX hX' ?_
          have hl := steps_label (P := P) (host := host) L.arity (if L.loop then [t] else []) h
          have hx : Steps P host
              ⟨s, f, [if L.tryT then Admin.handler L.arity L.catches
                [.label L.arity (if L.loop then [t] else []) inner]
                else .label L.arity (if L.loop then [t] else []) inner]⟩
              ⟨s', f', [if L.tryT then Admin.handler L.arity L.catches
                [.label L.arity (if L.loop then [t] else []) inner']
                else .label L.arity (if L.loop then [t] else []) inner']⟩ := by
            cases L.tryT
            · simpa using hl
            · simpa using steps_handler (P := P) (host := host) L.arity L.catches hl
          simpa using Steps.ctxtInstrs (vs := L.outer) (rest := expression (restAt pc (m + 1))) hx

/-- **A block's body run is a Core run of its code up to the terminator.** -/
theorem body_steps {c : List Instr} {i : Nat} {sg : Segment} {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} (hsg : (segment c)[i]? = some sg)
    (hr : Run P host s f stk (expression sg.body) s₁ f₁ (.normal stk₁)) :
    Steps P host ⟨s, f, vals stk ++ expression (restAt c i)⟩
      ⟨s₁, f₁, vals stk₁ ++ expression (sg.term.toList ++ restAt c (i + 1))⟩ := by
  obtain ⟨c', hs, he⟩ := Proofs.Region.sound hr
  simp only [Out.Ends] at he; subst he
  rw [Proofs.Machine.restAt_cons hsg]
  have h2 := Steps.ctxtInstrs (vs := []) (rest := expression (sg.term.toList ++ restAt c (i + 1)))
    (by simpa using hs)
  simpa [Segment.instrs, expression, List.append_assoc] using h2


theorem trans_label {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cont : List Instr) (h : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.label n cont X]⟩ ⟨s', f', [.label n cont Y]⟩ :=
  Relation.TransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b hs => by rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtLabel hs) _ _ h

theorem trans_handler {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cs : List Catch) (h : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.handler n cs X]⟩ ⟨s', f', [.handler n cs Y]⟩ :=
  Relation.TransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b hs => by rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtHandler hs) _ _ h

theorem trans_in {s s' : Store H} {f f' : Frame} {X Y : List Admin} (vs : List Val)
    (code : List Admin) (h : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Relation.TransGen (Step P host) ⟨s, f, vals vs ++ X ++ code⟩ ⟨s', f', vals vs ++ Y ++ code⟩ :=
  Relation.TransGen.lift
    (fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ code⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Proofs.Region.step_in vs code hs) _ _ h

/-- **At least one Core step lifts through the label frames.** -/
theorem wrap_trans {body : Expr} {s s' : Store H} {f f' : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) {inner inner' X X' : List Admin},
      wrap body rp ls inner = some X → wrap body rp ls inner' = some X' →
      Relation.TransGen (Step P host) ⟨s, f, inner⟩ ⟨s', f', inner'⟩ →
      Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', X'⟩
  | [], [], _, _, _, _, hX, hX', h => by
    simp only [wrap, Option.some.injEq] at hX hX'; subst hX hX'; exact h
  | [], _ :: _, _, _, _, _, hX, _, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, _, hX, _, _ => by simp [wrap] at hX
  | (m, a) :: rp, L :: ls, inner, inner', X, X', hX, hX', h => by
    simp only [wrap, Option.bind_eq_bind] at hX hX'
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some] at hX hX'
          refine wrap_trans rp ls hX hX' ?_
          have hl := trans_label (P := P) (host := host) L.arity (if L.loop then [t] else []) h
          have hx : Relation.TransGen (Step P host)
              ⟨s, f, [if L.tryT then Admin.handler L.arity L.catches
                [.label L.arity (if L.loop then [t] else []) inner]
                else .label L.arity (if L.loop then [t] else []) inner]⟩
              ⟨s', f', [if L.tryT then Admin.handler L.arity L.catches
                [.label L.arity (if L.loop then [t] else []) inner']
                else .label L.arity (if L.loop then [t] else []) inner']⟩ := by
            cases L.tryT
            · simpa using hl
            · simpa using trans_handler (P := P) (host := host) L.arity L.catches hl
          simpa using trans_in (P := P) (host := host) L.outer (expression (restAt pc (m + 1))) hx


/-- Leaving one finished label frame is at least one Core step (`label-vals`, and
`handler-vals` for a `try_table`). -/
theorem pop_trans {s : Store H} {f : Frame} (L : LFrame) (cont : List Instr) (W : List Val)
    (rest : List Admin) :
    Relation.TransGen (Step P host)
      ⟨s, f, vals L.outer ++ (if L.tryT then Admin.handler L.arity L.catches
        [.label L.arity cont (vals W)] else .label L.arity cont (vals W)) :: rest⟩
      ⟨s, f, vals (L.outer ++ W) ++ rest⟩ := by
  have hx : Relation.TransGen (Step P host)
      ⟨s, f, [if L.tryT then Admin.handler L.arity L.catches
        [.label L.arity cont (vals W)] else .label L.arity cont (vals W)]⟩ ⟨s, f, vals W⟩ := by
    cases L.tryT
    · exact .single .labelVals
    · exact .head (Step.ctxtHandler .labelVals) (.single .handlerVals)
  simpa using trans_in (P := P) (host := host) L.outer rest hx

open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **Leaving finished sequences is a Core run**, of at least one step when a frame is left:
`goto` to `contRev` (popping frames with `popL`) lands on the code Core reaches by
`label-vals`/`handler-vals`. -/
theorem cont_core {body : Expr} {s : Store H} {f : Frame} :
    ∀ (rp : List SeqStep) (ls : List LFrame) (W : List Val) {X Y : List Admin},
      wrap body rp ls (vals W) = some X →
      codeOf body (goto (contRev body rp) rp.length ls W s f) = some Y →
      Steps P host ⟨s, f, X⟩ ⟨s, f, Y⟩ ∧
        (rp ≠ [] → Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s, f, Y⟩)
  | [], [], W, X, Y, hX, hY => by
    simp [wrap] at hX; subst hX
    simp [codeOf, goto, contRev, depthT, popL] at hY; subst hY
    exact ⟨.refl, fun h => absurd rfl h⟩
  | [], _ :: _, _, _, _, hX, _ => by simp [wrap] at hX
  | _ :: _, [], _, _, _, hX, _ => by simp [wrap] at hX
  | (m, a) :: rp, L :: ls, W, X, Y, hX, hY => by
    have hX0 := hX
    simp only [wrap, Option.bind_eq_bind] at hX0
    cases hpc : seqAt body rp.reverse with
    | none => simp [hpc] at hX0
    | some pc =>
      cases hsg : (segment pc)[m]? with
      | none => simp [hpc, hsg] at hX0
      | some sg =>
        cases ht : sg.term with
        | none => simp [hpc, hsg, ht] at hX0
        | some t =>
          simp only [hpc, hsg, ht, Option.bind_some] at hX0
          cases hw : wrap body rp ls (vals (L.outer ++ W) ++ expression (restAt pc (m + 1))) with
          | none =>
            have := (wrap_isSome body rp ls (vals (L.outer ++ W) ++ expression (restAt pc (m + 1))) _).trans (congrArg Option.isSome hX0)
            rw [hw] at this; simp at this
          | some Z =>
            have h1 : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s, f, Z⟩ :=
              wrap_trans rp ls hX0 hw (pop_trans L _ W _)
            have hcont := depth_contRev body rp
            unfold contRev at hY
            split at hY
            · simp only [goto, depthT, List.length_cons, codeOf, codeAt, List.reverse_reverse,
                List.length_reverse] at hY
              rw [show rp.length + 1 - rp.length = 1 by omega] at hY
              simp [popL, hpc] at hY
              rw [vals_append, List.append_assoc, hY] at hw; cases hw
              exact ⟨h1.to_reflTransGen, fun _ => h1⟩
            · rename_i hl
              have hrest := restAt_none hpc (by simpa using hl)
              rw [hrest] at hw
              have hY' : codeOf body (goto (contRev body rp) rp.length ls (L.outer ++ W) s f) =
                  some Y := by
                simp only [goto, List.length_cons] at hY ⊢
                rw [show rp.length + 1 - depthT (contRev body rp) =
                  (rp.length - depthT (contRev body rp)) + 1 by omega] at hY
                simpa [popL] using hY
              have h2 := (cont_core rp ls (L.outer ++ W) (by simpa [expression] using hw) hY').1
              exact ⟨(Relation.TransGen.trans_left h1 h2).to_reflTransGen,
                fun _ => Relation.TransGen.trans_left h1 h2⟩


open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **Advancing to the next position of a sequence is a Core run** from the code the block
stood for, with values `stk₁` left before the rest of the sequence. It is at least one step
unless the machine stays in the same sequence (the next block exists) or reaches `exit`. -/
theorem advance_core {body : Expr} {b : BlockId} {c : List Instr} {stk stk₁ : List Val}
    {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {X Y : List Admin}
    (hc : seqAt body b.seq = some c)
    (hin : Steps P host ⟨s, f, vals stk ++ expression (restAt c b.idx)⟩
      ⟨s₁, f₁, vals stk₁ ++ expression (restAt c (b.idx + 1))⟩)
    (hX : codeAt body b stk ls = some X)
    (hY : codeOf body (goto (entry body b.seq (b.idx + 1)) b.seq.length ls stk₁ s₁ f₁) = some Y) :
    Steps P host ⟨s, f, X⟩ ⟨s₁, f₁, Y⟩ ∧
      (Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s₁, f₁, Y⟩ ∨
        entry body b.seq (b.idx + 1) = .block ⟨b.seq, b.idx + 1⟩ ∨
        entry body b.seq (b.idx + 1) = .exit) := by
  simp only [codeAt, hc, Option.bind_some] at hX
  cases hw : wrap body b.seq.reverse ls (vals stk₁ ++ expression (restAt c (b.idx + 1))) with
  | none =>
    have := (wrap_isSome body b.seq.reverse ls (vals stk₁ ++ expression (restAt c (b.idx + 1)))
      _).trans (congrArg Option.isSome hX)
    rw [hw] at this; simp at this
  | some Z =>
    have h1 := wrap_steps (P := P) (host := host) _ _ hX hw hin
    unfold entry at hY ⊢
    split at hY
    · rename_i hl
      simp [goto, depthT, popL, codeOf, codeAt, hc] at hY
      rw [hY] at hw; cases hw
      exact ⟨h1, Or.inr (Or.inl (by simp [hl]))⟩
    · rename_i hl
      have hrest := restAt_none hc (by simpa using hl)
      rw [hrest] at hw
      have hY' : codeOf body (goto (contRev body b.seq.reverse) b.seq.reverse.length ls stk₁
          s₁ f₁) = some Y := by simpa [cont] using hY
      obtain ⟨h2, h3⟩ := cont_core (P := P) (host := host) _ ls stk₁
        (by simpa [expression] using hw) hY'
      refine ⟨h1.trans h2, ?_⟩
      cases hq : b.seq.reverse with
      | nil =>
        right; right
        have : b.seq = [] := by simpa using hq
        have hl' := hl
        rw [this] at hl'
        simp [this, cont, contRev]
        simpa using hl'
      | cons x q =>
        left
        exact Relation.TransGen.trans_right h1 (h3 (by simp [hq]))

end Silmaril.Wasm.Cfg.Proofs.MachineCore
