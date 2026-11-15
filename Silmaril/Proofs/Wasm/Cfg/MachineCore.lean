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


open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- The code at a sequence position runs in Core to the code of the state `goto (entry …)`
lands on (the block there, or the continuation of a finished sequence). -/
theorem entry_core {body : Expr} {q : List SeqStep} {c : List Instr} {i : Nat}
    {ls : List LFrame} {W : List Val} {s : Store H} {f : Frame} {Z Y : List Admin}
    (hc : seqAt body q = some c)
    (hZ : wrap body q.reverse ls (vals W ++ expression (restAt c i)) = some Z)
    (hY : codeOf body (goto (entry body q i) q.length ls W s f) = some Y) :
    Steps P host ⟨s, f, Z⟩ ⟨s, f, Y⟩ := by
  unfold entry at hY
  split at hY
  · simp [goto, depthT, popL, codeOf, codeAt, hc] at hY
    rw [hY] at hZ; cases hZ; exact .refl
  · rename_i hl
    rw [restAt_none hc (by simpa using hl)] at hZ
    exact (cont_core (P := P) (host := host) q.reverse ls W (by simpa [expression] using hZ)
      (by simpa [cont] using hY)).1

theorem labelPred_toNat (x : LabelIdx) : (labelPred x).toNat = x.toNat - 1 := rfl


theorem kind_loop_false' {t : Instr} {bt : BlockType} {lp : Bool} {cs : List Catch}
    (h : StructKind t bt lp true cs) : lp = false := by
  cases h; rfl

open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **A branch is a Core run of at least one step** to the code of the state the machine's
branch steps go to: `br-label-succ`/`br-handler` leave the frames below the target, carrying
the frames' outer values (`brVals`), and `br-label-zero` (with `handler-vals`, and Core's
`loop` rule for a `loop` label) ends at the target. -/
theorem br_core {body : Expr} {s : Store H} {f : Frame} :
    ∀ (k : Nat) (rp : List SeqStep) (ls : List LFrame) {U : List Val} {rest X Y : List Admin}
      {L : LFrame} {x : LabelIdx}, x.toNat = k →
      wrap body rp ls (vals U ++ .plain (.br x) :: rest) = some X → FramesOk body rp ls →
      ls[k]? = some L → L.arity ≤ (brVals k ls U).length →
      (L.loop = true → ∃ t₁ t₂, f.module.blockType? L.bt = some (t₁, t₂) ∧ t₁.length = L.arity) →
      codeOf body (if L.loop then
          goto ((labelsRev body rp).getD k .invalid) (rp.length - k) (L :: ls.drop (k + 1))
            (topVals L.arity (brVals k ls U)) s f
        else
          goto ((labelsRev body rp).getD k .invalid) (rp.length - (k + 1)) (ls.drop (k + 1))
            (L.outer ++ topVals L.arity (brVals k ls U)) s f) = some Y →
      Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s, f, Y⟩
  | _, [], [], _, _, _, _, _, _, _, _, _, hL, _, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [FramesOk] at hok
  | _, _ :: _, [], _, _, _, _, _, _, _, _, _, hL, _, _, _ => by simp at hL
  | k, (m, a) :: rp, L₀ :: ls, U, rest, X, Y, L, x, hx, hX, hok, hL, har, hlbt, hY => by
    have hok0 := hok
    obtain ⟨⟨pc, sg, t, c', hpc, hsg, ht, harm', hkind'⟩, hok'⟩ := hok
    have hX0 := hX
    simp only [wrap, hpc, hsg, ht, Option.bind_eq_bind, Option.bind_some] at hX0
    set R := expression (restAt pc (m + 1)) with hR
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
      subst hL
      simp only [brVals] at har hY
      set U₂ := topVals L₀.arity U with hU₂
      have hsplit : vals U = vals (U.take (U.length - L₀.arity)) ++ vals U₂ := by
        rw [← vals_append, hU₂, topVals, List.take_append_drop]
      have hn : U₂.length = L₀.arity := by simp [hU₂, topVals]; omega
      have hz : Step P host
          ⟨s, f, [.label L₀.arity (if L₀.loop then [t] else []) (vals U ++ .plain (.br x) :: rest)]⟩
          ⟨s, f, vals U₂ ++ expression (if L₀.loop then [t] else [])⟩ := by
        have := Step.brLabelZero (P := P) (host := host) (s := s) (f := f) (n := L₀.arity)
          (cont := if L₀.loop then [t] else []) (vs' := U.take (U.length - L₀.arity))
          (vs := U₂) (l := x) (rest := rest) hx hn
        simpa [hsplit, List.append_assoc] using this
      have hframe : Relation.TransGen (Step P host)
          ⟨s, f, [if L₀.tryT then Admin.handler L₀.arity L₀.catches
            [.label L₀.arity (if L₀.loop then [t] else []) (vals U ++ .plain (.br x) :: rest)]
            else .label L₀.arity (if L₀.loop then [t] else []) (vals U ++ .plain (.br x) :: rest)]⟩
          ⟨s, f, vals U₂ ++ expression (if L₀.loop then [t] else [])⟩ := by
        cases hT : L₀.tryT
        · simpa using Relation.TransGen.single hz
        · have hlp : L₀.loop = false := by rw [hT] at hkind'; exact kind_loop_false' hkind'
          simp only [hlp, Bool.false_eq_true, ↓reduceIte, expression, List.map_nil,
            List.append_nil] at hz ⊢
          exact .head (Step.ctxtHandler hz) (.single .handlerVals)
      have h1 := trans_in (P := P) (host := host) L₀.outer R hframe
      have hlev := levelLoop_of_framesOk (L := L₀) 0 ((m, a) :: rp) (L₀ :: ls) hok0 (by simp)
      simp only [levelLoop, List.drop_zero] at hlev
      cases hlp : L₀.loop
      · simp only [hlp, Bool.false_eq_true, ↓reduceIte, expression, List.map_nil,
          List.append_nil] at h1 hY hX0
        cases hw : wrap body rp ls (vals (L₀.outer ++ U₂) ++ R) with
        | none =>
          have := (wrap_isSome body rp ls (vals (L₀.outer ++ U₂) ++ R) _).trans
            (congrArg Option.isSome hX0)
          rw [hw] at this; simp at this
        | some Z =>
          have h2 := wrap_trans (P := P) (host := host) rp ls hX0 hw
            (by simpa [List.append_assoc] using h1)
          simp only [labelsRev, hlev, hlp, Bool.false_eq_true, ↓reduceIte,
            List.getD_cons_zero, List.length_cons, Nat.add_sub_cancel, List.drop_one,
            List.tail_cons] at hY
          rw [show contRev body ((m, a) :: rp) = entry body rp.reverse (m + 1) by
            simp [contRev, entry, cont]] at hY
          have h3 := entry_core (P := P) (host := host) (q := rp.reverse) (i := m + 1)
            (W := L₀.outer ++ U₂) hpc (by rw [List.reverse_reverse]; exact hw)
            (by simpa using hY)
          exact Relation.TransGen.trans_left h2 h3
      · obtain ⟨cb, rfl, hT, -⟩ := Proofs.Machine.structKind_loop (hlp ▸ hkind')
        have ha : a = 0 := by rcases a with _ | _ | a <;> simp_all [armOf]
        subst ha
        obtain ⟨t₁, t₂, hbt, hlen⟩ := hlbt hlp
        simp only [hlp, hT, ↓reduceIte, Bool.false_eq_true] at h1 hY hX0
        have hloop : Step P host ⟨s, f, vals U₂ ++ [.plain (.loop L₀.bt cb)]⟩
            ⟨s, f, [.label L₀.arity [.loop L₀.bt cb] (vals U₂ ++ expression cb)]⟩ := by
          simpa [hlen] using Step.loop (P := P) (host := host) (s := s) (f := f)
            (body := cb) hbt (by rw [hn, hlen])
        have h1' := Relation.TransGen.tail h1 (Proofs.Region.step_in L₀.outer R hloop)
        have hq : seqAt body (rp.reverse ++ [(m, 0)]) = some cb := by
          rw [seqAt_append]; simp [hpc, hsg, ht, armOf]
        have hweq : wrap body ((m, 0) :: rp) (L₀ :: ls) (vals U₂ ++ expression (restAt cb 0)) =
            wrap body rp ls (vals L₀.outer ++
              .label L₀.arity [.loop L₀.bt cb] (vals U₂ ++ expression cb) :: R) := by
          simp [wrap, hpc, hsg, ht, hT, hlp, restAt_zero, hR]
        cases hw : wrap body rp ls (vals L₀.outer ++
              .label L₀.arity [.loop L₀.bt cb] (vals U₂ ++ expression cb) :: R) with
        | none =>
          have := (wrap_isSome body rp ls (vals L₀.outer ++
              .label L₀.arity [.loop L₀.bt cb] (vals U₂ ++ expression cb) :: R) _).trans
            (congrArg Option.isSome hX0)
          rw [hw] at this; simp at this
        | some Z =>
          have h2 := wrap_trans (P := P) (host := host) rp ls hX0 hw
            (by simpa [List.append_assoc] using h1')
          have hil : isLoopAt body rp.reverse m = true := hlev.trans hlp
          simp only [labelsRev, hil, ↓reduceIte, List.getD_cons_zero, List.length_cons,
            Nat.sub_zero, List.drop_one, List.tail_cons] at hY
          have h3 := entry_core (P := P) (host := host) (q := rp.reverse ++ [(m, 0)]) (i := 0)
            (ls := L₀ :: ls) (W := U₂) hq (by simpa [hweq] using hw) (by simpa using hY)
          exact Relation.TransGen.trans_left h2 h3
    | succ k =>
      simp only [List.getElem?_cons_succ] at hL
      have hx0 : 0 < x.toNat := by omega
      have hx' : (labelPred x).toNat = k := by simp [labelPred_toNat, hx]
      have hz : Step P host
          ⟨s, f, [.label L₀.arity (if L₀.loop then [t] else []) (vals U ++ .plain (.br x) :: rest)]⟩
          ⟨s, f, vals U ++ [.plain (.br (labelPred x))]⟩ := by
        simpa [List.append_assoc] using Step.brLabelSucc (P := P) (host := host) (s := s) (f := f)
          (n := L₀.arity) (cont := if L₀.loop then [t] else []) (vs := U) (rest := rest) hx0
      have hframe : Relation.TransGen (Step P host)
          ⟨s, f, [if L₀.tryT then Admin.handler L₀.arity L₀.catches
            [.label L₀.arity (if L₀.loop then [t] else []) (vals U ++ .plain (.br x) :: rest)]
            else .label L₀.arity (if L₀.loop then [t] else []) (vals U ++ .plain (.br x) :: rest)]⟩
          ⟨s, f, vals U ++ [.plain (.br (labelPred x))]⟩ := by
        cases L₀.tryT
        · simpa using Relation.TransGen.single hz
        · have hb := Step.brHandler (P := P) (host := host) (s := s) (f := f)
            (n := L₀.arity) (cs := L₀.catches) (vs := U) (l := labelPred x) (rest := [])
          simp only [List.append_nil] at hb
          exact .head (Step.ctxtHandler hz) (.single hb)
      have h1 := trans_in (P := P) (host := host) L₀.outer R hframe
      cases hw : wrap body rp ls (vals (L₀.outer ++ U) ++ .plain (.br (labelPred x)) :: R) with
      | none =>
        have := (wrap_isSome body rp ls (vals (L₀.outer ++ U) ++ .plain (.br (labelPred x)) :: R)
          _).trans (congrArg Option.isSome hX0)
        rw [hw] at this; simp at this
      | some Z =>
        have h2 := wrap_trans (P := P) (host := host) rp ls hX0 hw
          (by simpa [List.append_assoc] using h1)
        have hY' := hY
        simp only [labelsRev, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
          brVals] at hY'
        rw [show rp.length + 1 - (k + 1 + 1) = rp.length - (k + 1) by omega,
          show rp.length + 1 - (k + 1) = rp.length - k by omega] at hY'
        exact Relation.TransGen.trans_left h2 (br_core k rp ls hx' hw hok' hL
          (by simpa [brVals] using har) hlbt hY').to_reflTransGen


/-- **Entering a structured terminator is at least one Core step** (`block`, `loop`,
`try_table`; `if` first picks its arm): the label frame the machine pushes. -/
theorem enter_step {s : Store H} {f : Frame} {i : Instr} {bt : BlockType} {loop tryT : Bool}
    {cs : List Catch} {stk₁ ws us : List Val} {a : Nat} {c' : List Instr}
    {t₁ t₂ : List Validation.CValType} {R : List Admin}
    (hkind : StructKind i bt loop tryT cs) (harm : armOf i a = some c')
    (hcond : CondArm i stk₁ a ws us)
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length) :
    Relation.TransGen (Step P host) ⟨s, f, vals stk₁ ++ .plain i :: R⟩
      ⟨s, f, vals ws ++
        (if tryT then Admin.handler (labelArity loop t₁ t₂) cs
            [.label (labelArity loop t₁ t₂) (if loop then [i] else []) (vals us ++ expression c')]
          else .label (labelArity loop t₁ t₂) (if loop then [i] else [])
            (vals us ++ expression c')) :: R⟩ := by
  have lift : ∀ {X Y : List Admin}, Step P host ⟨s, f, vals us ++ X⟩ ⟨s, f, Y⟩ →
      Step P host ⟨s, f, vals (ws ++ us) ++ X ++ R⟩ ⟨s, f, vals ws ++ Y ++ R⟩ := by
    intro X Y h
    simpa [List.append_assoc] using Proofs.Region.step_in ws R h
  cases hkind with
  | @block _ b =>
    cases hcond with
    | plain _ =>
      simp only [armOf, Option.some.injEq] at harm; subst harm
      simpa [labelArity, List.append_assoc] using
        Relation.TransGen.single (lift (Step.block (body := b) hbt hm))
  | @loop _ b =>
    cases hcond with
    | plain _ =>
      simp only [armOf, Option.some.injEq] at harm; subst harm
      simpa [labelArity, List.append_assoc] using
        Relation.TransGen.single (lift (Step.loop (body := b) hbt hm))
  | @tryTable _ _ b =>
    cases hcond with
    | plain _ =>
      simp only [armOf, Option.some.injEq] at harm; subst harm
      simpa [labelArity, List.append_assoc] using
        Relation.TransGen.single (lift (Step.tryTable (body := b) hbt hm))
  | @if_ _ te ee =>
    cases hcond with
    | plain hi => exact absurd rfl (hi _ _ _)
    | @ifTrue _ _ _ _ _ k hk =>
      simp only [armOf, Option.some.injEq] at harm; subst harm
      have h1 : Step P host ⟨s, f, vals (ws ++ us ++ [.i32 k]) ++ .plain (.if_ bt te ee) :: R⟩
          ⟨s, f, vals (ws ++ us) ++ [.plain (.block bt te)] ++ R⟩ := by
        simpa [List.append_assoc, constI32] using
          Proofs.Region.step_in (ws ++ us) R (Step.ifTrue (P := P) (host := host) (s := s) (f := f)
            (bt := bt) (b₁ := te) (b₂ := ee) hk)
      exact .head h1 (by simpa [labelArity, List.append_assoc] using
        Relation.TransGen.single (lift (Step.block (body := te) hbt hm)))
    | ifFalse =>
      simp only [armOf, Option.some.injEq] at harm; subst harm
      have h1 : Step P host ⟨s, f, vals (ws ++ us ++ [.i32 0]) ++ .plain (.if_ bt te ee) :: R⟩
          ⟨s, f, vals (ws ++ us) ++ [.plain (.block bt ee)] ++ R⟩ := by
        simpa [List.append_assoc, constI32] using
          Proofs.Region.step_in (ws ++ us) R (Step.ifFalse (P := P) (host := host) (s := s) (f := f)
            (bt := bt) (b₁ := te) (b₂ := ee))
      exact .head h1 (by simpa [labelArity, List.append_assoc] using
        Relation.TransGen.single (lift (Step.block (body := ee) hbt hm)))


theorem steps_trans_of_ne {c c' : Config H} (h : Steps P host c c') (hne : c ≠ c') :
    Relation.TransGen (Step P host) c c' := by
  rcases h.cases_head with rfl | ⟨d, hd, hdc⟩
  · exact absurd rfl hne
  · exact Relation.TransGen.head' hd hdc

/-- Throwing with code after it: the rest is discarded (`throw_ref-instrs`). -/
theorem throwing_rest {s : Store H} {f : Frame} (a : Nat) (vs : List Val) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .single (Step.throwRefInstrs hne)
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using (Relation.ReflTransGen.refl : Steps P host ⟨s, f, throwing a⟩ _)

open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **A caught exception is a Core run of at least one step** to the code of the machine's
catch target: `throw_ref` propagates out of the frames below the catching handler (`label`,
passing handlers), the handler's first matching clause branches, and the branch continues as in
`br_core`. -/
theorem throw_core {body : Expr} {s : Store H} {f : Frame} {a : Nat} {us : List Val}
    {l : LabelIdx} :
    ∀ (j : Nat) (rp : List SeqStep) (ls : List LFrame) {rest X Y : List Admin} {L L' : LFrame},
      wrap body rp ls (throwing a ++ rest) = some X → FramesOk body rp ls →
      (∀ (k : Nat) (L : LFrame), k < j → ls[k]? = some L → L.tryT = true →
        Catches s f a L.catches none) →
      ls[j]? = some L → L.tryT = true → Catches s f a L.catches (some (us, l)) →
      ls[j + 1 + l.toNat]? = some L' →
      L'.arity ≤ (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us)).length →
      (L'.loop = true → ∃ t₁ t₂, f.module.blockType? L'.bt = some (t₁, t₂) ∧
        t₁.length = L'.arity) →
      codeOf body (if L'.loop then
          goto ((labelsRev body rp).getD (j + 1 + l.toNat) .invalid) (rp.length - (j + 1 + l.toNat))
            (L' :: ls.drop (j + 1 + l.toNat + 1))
            (topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s f
        else
          goto ((labelsRev body rp).getD (j + 1 + l.toNat) .invalid)
            (rp.length - (j + 1 + l.toNat + 1)) (ls.drop (j + 1 + l.toNat + 1))
            (L'.outer ++ topVals L'.arity (brVals l.toNat (ls.drop (j + 1)) (L.outer ++ us))) s f) =
        some Y →
      Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s, f, Y⟩
  | _, [], [], _, _, _, _, _, _, _, _, hL, _, _, _, _, _, _ => by simp at hL
  | _, [], _ :: _, _, _, _, _, _, _, hok, _, _, _, _, _, _, _, _ => by simp [FramesOk] at hok
  | _, _ :: _, [], _, _, _, _, _, _, _, _, hL, _, _, _, _, _, _ => by simp at hL
  | j, (m, a') :: rp, L₀ :: ls, rest, X, Y, L, L', hX, hok, hpass, hL, hT, hc, hL', har, hlbt,
      hY => by
    obtain ⟨⟨pc, sg, t, c', hpc, hsg, ht, harm', hkind'⟩, hok'⟩ := hok
    have hX0 := hX
    simp only [wrap, hpc, hsg, ht, Option.bind_eq_bind, Option.bind_some] at hX0
    set R := expression (restAt pc (m + 1)) with hR
    have hin : Steps P host ⟨s, f, throwing a ++ rest⟩ ⟨s, f, throwing a⟩ := by
      simpa using throwing_rest (P := P) (host := host) (s := s) (f := f) a [] rest
    have hlab : Steps P host
        ⟨s, f, [.label L₀.arity (if L₀.loop then [t] else []) (throwing a ++ rest)]⟩
        ⟨s, f, throwing a⟩ :=
      (steps_label (P := P) (host := host) _ _ hin).trans (.single .throwRefLabel)
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
      subst hL
      have hlp : L₀.loop = false := by rw [hT] at hkind'; exact kind_loop_false' hkind'
      simp only [hT, hlp, ↓reduceIte, Bool.false_eq_true] at hX0 hlab
      have hh : Steps P host ⟨s, f, [.handler L₀.arity L₀.catches
            [.label L₀.arity [] (throwing a ++ rest)]]⟩ ⟨s, f, vals us ++ [.plain (.br l)]⟩ :=
        (steps_handler (P := P) (host := host) _ _ hlab).trans
          (by simpa [Proofs.Region.catchCode] using Proofs.Region.catches_steps (n := L₀.arity) hc)
      have hh' : Relation.TransGen (Step P host) ⟨s, f, [.handler L₀.arity L₀.catches
            [.label L₀.arity [] (throwing a ++ rest)]]⟩ ⟨s, f, vals us ++ [.plain (.br l)]⟩ := by
        refine steps_trans_of_ne hh ?_
        intro he
        have := congrArg (fun c : Config H => c.code.getLast?) he
        simp at this
      have h1 := trans_in (P := P) (host := host) L₀.outer R hh'
      cases hw : wrap body rp ls (vals (L₀.outer ++ us) ++ .plain (.br l) :: R) with
      | none =>
        have := (wrap_isSome body rp ls (vals (L₀.outer ++ us) ++ .plain (.br l) :: R) _).trans
          (congrArg Option.isSome hX0)
        rw [hw] at this; simp at this
      | some Z =>
        have h2 := wrap_trans (P := P) (host := host) rp ls hX0 hw
          (by simpa [List.append_assoc] using h1)
        have hL'' : ls[l.toNat]? = some L' := by
          simpa [show 0 + 1 + l.toNat = l.toNat + 1 by omega] using hL'
        have hY' := hY
        rw [show 0 + 1 + l.toNat = l.toNat + 1 by omega] at hY'
        simp only [labelsRev, List.getD_cons_succ, List.length_cons, List.drop_succ_cons,
          List.drop_zero] at hY' har
        rw [show rp.length + 1 - (l.toNat + 1 + 1) = rp.length - (l.toNat + 1) by omega,
          show rp.length + 1 - (l.toNat + 1) = rp.length - l.toNat by omega] at hY'
        exact Relation.TransGen.trans_left h2
          (br_core l.toNat rp ls rfl hw hok' hL'' (by simpa using har) hlbt hY').to_reflTransGen
    | succ j =>
      simp only [List.getElem?_cons_succ] at hL
      -- frame 0 lets the exception pass
      have hpass0 : Steps P host
          ⟨s, f, [if L₀.tryT then Admin.handler L₀.arity L₀.catches
            [.label L₀.arity (if L₀.loop then [t] else []) (throwing a ++ rest)]
            else .label L₀.arity (if L₀.loop then [t] else []) (throwing a ++ rest)]⟩
          ⟨s, f, throwing a⟩ := by
        cases hT0 : L₀.tryT
        · simpa using hlab
        · have hcn := hpass 0 L₀ (by omega) (by simp) hT0
          simpa [Proofs.Region.catchCode] using
            (steps_handler (P := P) (host := host) _ _ hlab).trans
              (Proofs.Region.catches_steps (n := L₀.arity) hcn)
      have hne : (⟨s, f, [if L₀.tryT then Admin.handler L₀.arity L₀.catches
            [.label L₀.arity (if L₀.loop then [t] else []) (throwing a ++ rest)]
            else .label L₀.arity (if L₀.loop then [t] else []) (throwing a ++ rest)]⟩ :
            Config H) ≠ ⟨s, f, throwing a⟩ := by
        intro he; have := congrArg (fun c : Config H => c.code.length) he
        simp at this
      have h1 := trans_in (P := P) (host := host) L₀.outer R (steps_trans_of_ne hpass0 hne)
      have h1' := Relation.TransGen.trans_left h1
        (throwing_rest (P := P) (host := host) (s := s) (f := f) a L₀.outer R)
      cases hw : wrap body rp ls (throwing a ++ []) with
      | none =>
        have := (wrap_isSome body rp ls (throwing a ++ []) _).trans (congrArg Option.isSome hX0)
        rw [hw] at this; simp at this
      | some Z =>
        have h2 := wrap_trans (P := P) (host := host) rp ls hX0 hw
          (by simpa [List.append_assoc] using h1')
        have hY' := hY
        rw [show j + 1 + 1 + l.toNat = (j + 1 + l.toNat) + 1 by omega] at hY' hL'
        simp only [labelsRev, List.getD_cons_succ, List.length_cons,
          List.drop_succ_cons] at hY' har hL'
        have e1 : rp.length + 1 - (j + 1 + l.toNat + 1 + 1) = rp.length - (j + 1 + l.toNat + 1) := by
          omega
        have e2 : rp.length + 1 - (j + 1 + l.toNat + 1) = rp.length - (j + 1 + l.toNat) := by
          omega
        rw [e1, e2] at hY'
        exact Relation.TransGen.trans_left h2 (throw_core j rp ls hw hok'
          (fun k L₁ hk hL₁ hT₁ => hpass (k + 1) L₁ (by omega) (by simpa using hL₁) hT₁)
          hL hT hc hL' (by simpa using har) hlbt hY').to_reflTransGen

end Silmaril.Wasm.Cfg.Proofs.MachineCore
