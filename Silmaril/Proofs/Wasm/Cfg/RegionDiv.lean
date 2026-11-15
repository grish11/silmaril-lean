module

public import Silmaril.Proofs.Wasm.Cfg.Region

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (Det.famOf)

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {D : Store H → Nat → List Val → Prop}

abbrev Rel4 (H : Type) := Store H → Frame → List Val → List Admin → Prop

/-! ## The greatest fixed point -/

theorem DivFC.mono {R S : Rel4 H} (hRS : ∀ s f vs c, R s f vs c → S s f vs c)
    {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : DivFC P host C D R s f vs code) : DivFC P host C D S s f vs code := by
  cases h with
  | val hv h => exact .val hv (hRS _ _ _ _ h)
  | simple hi h₁ h => exact .simple hi h₁ (hRS _ _ _ _ h)
  | brIf h => exact .brIf (hRS _ _ _ _ h)
  | brData hb h => exact .brData hb (hRS _ _ _ _ h)
  | block hbt hm h => exact .block hbt hm (hRS _ _ _ _ h)
  | loop hbt hm h => exact .loop hbt hm (hRS _ _ _ _ h)
  | if_ h => exact .if_ (hRS _ _ _ _ h)
  | labelIn h => exact .labelIn (hRS _ _ _ _ h)
  | tryTable hbt hm h => exact .tryTable hbt hm (hRS _ _ _ _ h)
  | handlerIn h => exact .handlerIn (hRS _ _ _ _ h)
  | handlerNormal hin h => exact .handlerNormal hin (hRS _ _ _ _ h)
  | labelNormal hin h => exact .labelNormal hin (hRS _ _ _ _ h)
  | labelBr0 hin hn h => exact .labelBr0 hin hn (hRS _ _ _ _ h)
  | call hfi hty hn hcall hvs h => exact .call hfi hty hn hcall hvs (hRS _ _ _ _ h)
  | callDiv hfi hty hn hD => exact .callDiv hfi hty hn hD

theorem runDiv_unfold {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : RunDivC P host C D s f vs code) : DivFC P host C D (RunDivC P host C D) s f vs code := by
  obtain ⟨R, hR, hx⟩ := h
  exact DivFC.mono (fun s f vs c hc => ⟨R, hR, hc⟩) (hR _ _ _ _ hx)

/-- Coinduction up to `RunDivC`. -/
theorem runDiv_coind (X : Rel4 H)
    (hX : ∀ s f vs c, X s f vs c → DivFC P host C D (fun s f vs c => X s f vs c ∨ RunDivC P host C D s f vs c)
      s f vs c)
    {s : Store H} {f : Frame} {vs : List Val} {code : List Admin} (h : X s f vs code) :
    RunDivC P host C D s f vs code := by
  refine ⟨fun s f vs c => X s f vs c ∨ RunDivC P host C D s f vs c, ?_, .inl h⟩
  rintro s f vs c (hc | hc)
  · exact hX _ _ _ _ hc
  · exact DivFC.mono (fun _ _ _ _ h => .inr h) (runDiv_unfold hc)

theorem runDiv_vals {s : Store H} {f : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin},
      RunDivC P host C D s f (vs ++ ws) code → RunDivC P host C D s f vs (vals ws ++ code)
  | [], _, h => by simpa [vals] using h
  | w :: ws, code, h => by
    have ih := runDiv_vals (vs := vs ++ [w]) (ws := ws) (code := code) (by simpa using h)
    refine runDiv_coind (fun s' f' vs' c => s' = s ∧ f' = f ∧ vs' = vs ∧
      c = vals (w :: ws) ++ code) ?_ ⟨rfl, rfl, rfl, rfl⟩
    rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
    simp only [vals, List.map_cons, List.cons_append]
    exact .val (Admin.val?_toAdmin w) (.inr ih)

theorem runDiv_label {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cont : List Instr}
    {inner code : List Admin} (h : RunDivC P host C D s f [] inner) :
    RunDivC P host C D s f vs (.label n cont inner :: code) := by
  refine runDiv_coind (fun s' f' vs' c => s' = s ∧ f' = f ∧ vs' = vs ∧
    c = .label n cont inner :: code) ?_ ⟨rfl, rfl, rfl, rfl⟩
  rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  exact .labelIn (.inr h)

theorem runDiv_handler {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cs : List Catch}
    {inner code : List Admin} (h : RunDivC P host C D s f [] inner) :
    RunDivC P host C D s f vs (.handler n cs inner :: code) := by
  refine runDiv_coind (fun s' f' vs' c => s' = s ∧ f' = f ∧ vs' = vs ∧
    c = .handler n cs inner :: code) ?_ ⟨rfl, rfl, rfl, rfl⟩
  rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  exact .handlerIn (.inr h)

/-! ## Soundness: a diverging region run is an infinite Core run -/

theorem transGen_of_steps {c c' : Config H} (h : Steps P host c c') (hne : c ≠ c') :
    Relation.TransGen (Step P host) c c' := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hb, hr⟩
  · exact absurd rfl hne
  · exact Relation.TransGen.head' hb hr

theorem transGen_in {s s' : Store H} {f f' : Frame} {X Y : List Admin} (vs : List Val)
    (code : List Admin) (h : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Relation.TransGen (Step P host) ⟨s, f, vals vs ++ X ++ code⟩ ⟨s', f', vals vs ++ Y ++ code⟩ :=
  Relation.TransGen.lift (fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ code⟩ : Config H))
    (fun a b st => by rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact step_in vs code st) _ _ h

theorem transGen_label {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cont : List Instr) (h : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.label n cont X]⟩ ⟨s', f', [.label n cont Y]⟩ :=
  Relation.TransGen.lift (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b st => by rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtLabel st) _ _ h

theorem transGen_handler {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cs : List Catch) (h : Relation.TransGen (Step P host) ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Relation.TransGen (Step P host) ⟨s, f, [.handler n cs X]⟩ ⟨s', f', [.handler n cs Y]⟩ :=
  Relation.TransGen.lift (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b st => by rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtHandler st) _ _ h

/-- A run of a non-value to values takes at least one step. -/
theorem atom_transGen {s s₁ : Store H} {f f₁ : Frame} {vs vs₁ : List Val} {a : Admin}
    (ha : a.val? = none) (h : Steps P host ⟨s, f, vals vs ++ [a]⟩ ⟨s₁, f₁, vals vs₁⟩) :
    Relation.TransGen (Step P host) ⟨s, f, vals vs ++ [a]⟩ ⟨s₁, f₁, vals vs₁⟩ := by
  refine transGen_of_steps h fun he => ?_
  simp only [Config.mk.injEq] at he
  have hm : a ∈ vals vs₁ := by rw [← he.2.2]; simp
  exact SingleThreaded.Det.mem_vals hm ha

theorem diverges_in {s : Store H} {f : Frame} {X : List Admin} (vs : List Val)
    (code : List Admin) (h : Diverges P host ⟨s, f, X⟩) :
    Diverges P host ⟨s, f, vals vs ++ X ++ code⟩ :=
  InfiniteTrace.map (R := Step P host) (S := Step P host)
    (fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ code⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact step_in vs code hs) h

theorem diverges_label {s : Store H} {f : Frame} {X : List Admin} (n : Nat) (cont : List Instr)
    (h : Diverges P host ⟨s, f, X⟩) : Diverges P host ⟨s, f, [.label n cont X]⟩ :=
  InfiniteTrace.map (R := Step P host) (S := Step P host)
    (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtLabel hs) h

theorem diverges_handler {s : Store H} {f : Frame} {X : List Admin} (n : Nat) (cs : List Catch)
    (h : Diverges P host ⟨s, f, X⟩) : Diverges P host ⟨s, f, [.handler n cs X]⟩ :=
  InfiniteTrace.map (R := Step P host) (S := Step P host)
    (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b hs => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtHandler hs) h

/-- **Progress**: a diverging region run takes at least one Core step to another diverging
region run, or (at a call `D` names) its code diverges in Core. -/
theorem progress (hC : CallSound P host C) (hD : DivCallSound P host D) {s : Store H} {f : Frame}
    {vs : List Val} {code : List Admin} (h : RunDivC P host C D s f vs code) :
    (∃ s' f' vs' code', Relation.TransGen (Step P host) ⟨s, f, vals vs ++ code⟩
      ⟨s', f', vals vs' ++ code'⟩ ∧ RunDivC P host C D s' f' vs' code') ∨
      Diverges P host ⟨s, f, vals vs ++ code⟩ := by
  induction hsz : sizeOf code using Nat.strong_induction_on generalizing s f vs code with
  | _ N ih =>
  subst hsz
  cases runDiv_unfold h with
  | @val _ _ a v code' hv hd =>
    rw [Admin.eq_of_val? hv]
    rcases ih (sizeOf code') (by simp) hd rfl with ⟨s', f', vs', c', hs, hd⟩ | hdiv
    · exact .inl ⟨s', f', vs', c', by simpa [vals] using hs, hd⟩
    · exact .inr (by simpa [vals] using hdiv)
  | @simple s₁ _ f₁ _ vs₁ i code' hi h₁ hd =>
    refine .inl ⟨s₁, f₁, vs₁, code', ?_, hd⟩
    have := transGen_in [] code' (atom_transGen (Proofs.Exec.val_none_of_noncontrol hi) h₁)
    simpa [vals] using this
  | @brIf _ ws k l code' hd =>
    refine .inl ⟨_, _, ws, _, .single ?_, hd⟩
    split
    · rename_i hk; subst hk
      have := step_in (P := P) (host := host) ws code' (Step.brIfFalse (s := s) (f := f) (l := l))
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
    · rename_i hk
      have := step_in (P := P) (host := host) ws code'
        (Step.brIfTrue (s := s) (f := f) (l := l) hk)
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
  | @brData _ ws us us' i X code' hb hd =>
    refine .inl ⟨_, _, ws ++ us', _, .single ?_, hd⟩
    simpa using step_in (P := P) (host := host) ws code' (BrStep.step (P := P) (host := host) hb)
  | @block _ ws us bt b t₁ t₂ code' hbt hm hd =>
    refine .inl ⟨_, _, ws, _, .single ?_, hd⟩
    simpa using step_in (P := P) (host := host) ws code' (Step.block (s := s) (body := b) hbt hm)
  | @loop _ ws us bt b t₁ t₂ code' hbt hm hd =>
    refine .inl ⟨_, _, ws, _, .single ?_, hd⟩
    simpa using step_in (P := P) (host := host) ws code' (Step.loop (s := s) (body := b) hbt hm)
  | @if_ _ ws k bt t e code' hd =>
    refine .inl ⟨_, _, ws, _, .single ?_, hd⟩
    split
    · rename_i hk; subst hk
      have := step_in (P := P) (host := host) ws code'
        (Step.ifFalse (s := s) (f := f) (bt := bt) (b₁ := t) (b₂ := e))
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
    · rename_i hk
      have := step_in (P := P) (host := host) ws code'
        (Step.ifTrue (s := s) (f := f) (bt := bt) (b₁ := t) (b₂ := e) hk)
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
  | @labelIn _ _ n cont inner code' hd =>
    rcases ih (sizeOf inner) (by simp; omega) hd rfl with ⟨s', f', vs', c', hs, hd⟩ | hdiv
    · refine .inl ⟨s', f', vs, .label n cont (vals vs' ++ c') :: code', ?_,
        runDiv_label (runDiv_vals hd)⟩
      have := transGen_in vs code' (transGen_label n cont (X := inner) (Y := vals vs' ++ c') hs)
      simpa using this
    · exact .inr (by simpa using diverges_in vs code' (diverges_label n cont (by simpa using hdiv)))
  | @tryTable _ ws us bt cs b t₁ t₂ code' hbt hm hd =>
    refine .inl ⟨_, _, ws, _, .single ?_, hd⟩
    simpa using step_in (P := P) (host := host) ws code'
      (Step.tryTable (s := s) (cs := cs) (body := b) hbt hm)
  | @handlerIn _ _ n cs inner code' hd =>
    rcases ih (sizeOf inner) (by simp; omega) hd rfl with ⟨s', f', vs', c', hs, hd⟩ | hdiv
    · refine .inl ⟨s', f', vs, .handler n cs (vals vs' ++ c') :: code', ?_,
        runDiv_handler (runDiv_vals hd)⟩
      have := transGen_in vs code' (transGen_handler n cs (X := inner) (Y := vals vs' ++ c') hs)
      simpa using this
    · exact .inr (by simpa using diverges_in vs code' (diverges_handler n cs (by simpa using hdiv)))
  | @handlerNormal s₁ _ f₁ _ us n cs inner code' hin hd =>
    refine .inl ⟨s₁, f₁, vs ++ us, code', ?_, hd⟩
    obtain ⟨c₁, hs₁, he₁⟩ := soundC hC hin
    simp only [Out.Ends] at he₁; subst he₁
    have h1 := steps_in vs code' (steps_handler n cs (by simpa using hs₁))
    have h2 := step_in (P := P) (host := host) vs code'
      (Step.handlerVals (s := s₁) (f := f₁) (n := n) (cs := cs) (vs := us))
    have := Relation.TransGen.tail' h1 h2
    simpa using this
  | @labelNormal s₁ _ f₁ _ us n cont inner code' hin hd =>
    refine .inl ⟨s₁, f₁, vs ++ us, code', ?_, hd⟩
    obtain ⟨c₁, hs₁, he₁⟩ := soundC hC hin
    simp only [Out.Ends] at he₁; subst he₁
    have h1 := steps_in vs code' (steps_label n cont (by simpa using hs₁))
    have h2 := step_in (P := P) (host := host) vs code'
      (Step.labelVals (s := s₁) (f := f₁) (n := n) (cont := cont) (vs := us))
    have := Relation.TransGen.tail' h1 h2
    simpa using this
  | @labelBr0 s₁ _ f₁ _ us₁ us₂ n cont inner code' hin hn hd =>
    refine .inl ⟨s₁, f₁, vs, _, ?_, hd⟩
    obtain ⟨c₁, hs₁, x, rest, hx, rfl⟩ := soundC hC hin
    have h1 := steps_in vs code' (steps_label n cont (by simpa using hs₁))
    have h2 := step_in (P := P) (host := host) vs code'
      (Step.brLabelZero (s := s₁) (f := f₁) (n := n) (cont := cont) (vs' := us₁) (vs := us₂)
        (l := x) (rest := rest) hx hn)
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := Relation.TransGen.tail' h1 h2
    simpa using this
  | @call s₁ _ ws us vs₁ x a fi ps rs fl code' hfi hty hn hcall hvs hd =>
    refine .inl ⟨s₁, f, ws ++ (vs₁.take rs.length).reverse, code', ?_, hd⟩
    have h1 := steps_in ws code'
      ((hC s s₁ f a fi ps rs us fl (func?_inv hfi).2 hty hn hcall).1 vs₁ hvs)
    exact Relation.TransGen.head' (call_head hfi) (by simpa using h1)
  | @callDiv _ ws us x a fi ps rs code' hfi hty hn hd =>
    refine .inr (InfiniteTrace.fold (call_head hfi) ?_)
    exact diverges_in ws code' (hD s f a fi ps rs us _ trivial (func?_inv hfi).2 hty hn hd)

/-- **Soundness for divergence**: a diverging region run is an infinite Core 3.0 run, when `C`
answers calls as Core runs them and the calls `D` names diverge in Core. -/
theorem div_soundC (hC : CallSound P host C) (hD : DivCallSound P host D) {s : Store H}
    {f : Frame} {vs : List Val} {code : List Admin} (h : RunDivC P host C D s f vs code) :
    Diverges P host ⟨s, f, vals vs ++ code⟩ := by
  refine InfiniteTrace.coinduct (fun c => (∃ s f vs code, RunDivC P host C D s f vs code ∧
    Steps P host c ⟨s, f, vals vs ++ code⟩) ∨ Diverges P host c) ?_
    (.inl ⟨s, f, vs, code, h, .refl⟩)
  rintro c (⟨s, f, vs, code, hd, hs⟩ | hdiv)
  · rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨b, hb, hr⟩
    · rcases progress hC hD hd with ⟨s', f', vs', c', ht, hd'⟩ | hdiv
      · obtain ⟨b, hb, hr⟩ := Relation.TransGen.head'_iff.1 ht
        exact ⟨b, hb, .inl ⟨s', f', vs', c', hd', hr⟩⟩
      · obtain ⟨b, hb, hb'⟩ := hdiv.unfold
        exact ⟨b, hb, .inr hb'⟩
    · exact ⟨b, hb, .inl ⟨s, f, vs, code, hd, hr⟩⟩
  · obtain ⟨b, hb, hb'⟩ := hdiv.unfold
    exact ⟨b, hb, .inr hb'⟩

/-- **Soundness for call-free divergence.** -/
theorem div_sound {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : RunDiv P host s f vs code) : Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  div_soundC (fun _ _ _ _ _ _ _ _ _ _ _ _ hc => hc.elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hd => hd.elim) h

/-! ## Codes that cannot diverge -/

/-- A trap after values. -/
def TrapForm (c : List Admin) : Prop := ∃ ws rest, c = vals ws ++ .trap :: rest

theorem trapForm_step {c c' : Config H} (h : Step P host c c') (ht : TrapForm c.code) :
    TrapForm c'.code ∧ c'.code.length < c.code.length := by
  obtain ⟨ws, rest, hc⟩ := ht
  rcases c with ⟨s, f, x⟩
  rcases c' with ⟨s', f', x'⟩
  dsimp only at hc ⊢
  subst hc
  rcases Sim.Step.split_head rfl h with ⟨ws₁, us, is', rfl, hs, rfl⟩ | ⟨-, -, -, ws₁, us, r, r', rfl, rfl, hne, rfl⟩ |
      ⟨h, -⟩
  · obtain ⟨w, he, hw⟩ := Step.trap_vals_inv hs
    simp only [Config.mk.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    exact ⟨⟨ws₁ ++ w, rest, by simp⟩, by simp; omega⟩
  · refine ⟨⟨ws₁, r', by simp⟩, ?_⟩
    simp only [List.length_append, vals_length, List.length_cons, List.length_singleton,
      List.length_nil]
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega
  · cases h

theorem trapForm_not_div {c : Config H} (ht : TrapForm c.code) : ¬ Diverges P host c := by
  induction hn : c.code.length using Nat.strong_induction_on generalizing c with
  | _ N ih =>
  intro hd
  obtain ⟨c', hs, hd'⟩ := hd.unfold
  obtain ⟨ht', hl⟩ := trapForm_step hs ht
  exact ih _ (hn ▸ hl) ht' rfl hd'

theorem br_stuck_seq {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx} {rest : List Admin}
    {c : Config H} (h : Step P host ⟨s, f, vals vs ++ .plain (.br l) :: rest⟩ c) : False := by
  rcases c with ⟨s', f', x'⟩
  rcases Sim.Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Step.br_vals_stuck hs
  · cases h
  · cases h

theorem ret_stuck_seq {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    {c : Config H} (h : Step P host ⟨s, f, vals vs ++ .plain .return_ :: rest⟩ c) : False := by
  rcases c with ⟨s', f', x'⟩
  rcases Sim.Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Step.return_vals_stuck hs
  · cases h
  · cases h

/-! ## Leaving an atom -/

/-- A step of `X ++ Y`, `X` simple code that is not all values, is a step of `X`. -/
theorem seq_step {s : Store H} {f : Frame} {X Y : List Admin} {c : Config H}
    (hX : ∀ b ∈ X, SimpleAdmin b) (hnv : X.all Admin.isVal = false)
    (h : Step P host ⟨s, f, X ++ Y⟩ c) :
    ∃ X', Step P host ⟨s, f, X⟩ ⟨c.store, c.frame, X'⟩ ∧ c.code = X' ++ Y := by
  obtain ⟨w, a, Xr, ha, rfl⟩ := Sim.exists_head_of_not_all hnv
  obtain ⟨i, rfl, hi⟩ : ∃ i, a = .plain i ∧ Det.famOf (.plain i) ≠ .control := by
    rcases hX a (by simp) with h | h
    · exact absurd ha h
    · exact h
  rcases c with ⟨s', f', x'⟩
  have h' : Step P host ⟨s, f, vals w ++ .plain i :: (Xr ++ Y)⟩ ⟨s', f', x'⟩ := by simpa using h
  rcases Sim.Step.split_head ha h' with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · refine ⟨vals ws ++ is' ++ Xr, ?_, by simp⟩
    simpa using step_in ws Xr hs
  · cases h
  · simp only [Admin.plain.injEq] at h; subst h; simp [Det.famOf] at hi

/-- Simple code, or a trap form: what the reduction of an atom passes through. -/
def AtomInv (x : List Admin) : Prop := (∀ b ∈ x, SimpleAdmin b) ∨ TrapForm x

theorem atomInv_step {c c' : Config H} (h : Step P host c c') (hi : AtomInv c.code) :
    AtomInv c'.code := by
  rcases hi with hB | ht
  · by_cases hv : c.code.all Admin.isVal = true
    · obtain ⟨W, hW⟩ := Sim.exists_vals_of_all hv
      rcases c with ⟨s, f, x⟩
      dsimp only at hW; subst hW
      exact (Step.not_vals h).elim
    · obtain ⟨w, a, Xr, ha, hc⟩ := Sim.exists_head_of_not_all (by simpa using hv)
      obtain ⟨i, rfl, hk⟩ : ∃ i, a = .plain i ∧ Det.famOf (.plain i) ≠ .control := by
        rcases hB a (by rw [hc]; simp) with h | h
        · exact absurd ha h
        · exact h
      rcases Proofs.Exec.simple_step h (A' := Xr) (R := []) hk (by simpa using hc) with
        ⟨B, hB', he⟩ | ⟨ws, he⟩
      · left
        rw [he]; intro b hb
        simp only [List.append_nil, List.mem_append] at hb
        rcases hb with hb | hb
        · exact hB' b hb
        · exact hB b (by rw [hc]; simp [hb])
      · right; exact ⟨ws, Xr, by rw [he]; simp⟩
  · exact .inr (trapForm_step h ht).1

/-- **Leaving an atom**: when a terminating atom runs at the head of a diverging configuration,
it reaches values, and the configuration after them still diverges. -/
theorem atom_exit {s : Store H} {f : Frame} {vs : List Val} {i : Instr} {Y : List Admin}
    (hk : Det.famOf (.plain i) ≠ .control)
    (hacc : Acc (fun a b => Step P host b a) (⟨s, f, vals vs ++ [.plain i]⟩ : Config H))
    (hd : Diverges P host ⟨s, f, vals vs ++ .plain i :: Y⟩) :
    ∃ s₁ f₁ vs₁, Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩ ∧
      Diverges P host ⟨s₁, f₁, vals vs₁ ++ Y⟩ := by
  classical
  let plug : Config H → Config H := fun x => ⟨x.store, x.frame, x.code ++ Y⟩
  let bd : Config H → Config H → Prop := fun a b => Step P host (plug a) b ∧
    (a.code.all Admin.isVal = true ∨ ¬ ∀ x ∈ a.code, SimpleAdmin x)
  have peel : ∀ a b, Step P host (plug a) b → (∃ next, Step P host a next ∧ b = plug next) ∨ bd a b := by
    intro a b hs
    by_cases hv : a.code.all Admin.isVal = true
    · exact .inr ⟨hs, .inl hv⟩
    · by_cases hS : ∀ x ∈ a.code, SimpleAdmin x
      · rcases a with ⟨sa, fa, xa⟩
        obtain ⟨X', hX', he⟩ := seq_step hS (by simpa using hv) hs
        left
        refine ⟨⟨b.store, b.frame, X'⟩, hX', ?_⟩
        rcases b with ⟨_, _, _⟩; simp only [plug] at he ⊢; rw [he]
      · exact .inr ⟨hs, .inr hS⟩
  have hd' : InfiniteTrace (Step P host) (plug ⟨s, f, vals vs ++ [.plain i]⟩) := by
    unfold Diverges at hd; simpa [plug] using hd
  rcases InfiniteTrace.context_decompose (Step P host) (Step P host) plug bd peel hd' with
    hin | ⟨a, b, hr, ⟨hs, hb⟩, hb'⟩
  · exact (InfiniteTrace.iff_not_acc.1 hin hacc).elim
  · have hinv : AtomInv a.code := by
      clear hb hs hb'
      induction hr with
      | refl => exact .inl (by
          intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact .inl (SingleThreaded.Det.mem_vals hx)
          · exact .inr ⟨i, rfl, hk⟩)
      | tail _ st ih => exact atomInv_step st ih
    have hpa : Diverges P host (plug a) := InfiniteTrace.fold hs hb'
    rcases hb with hv | hS
    · obtain ⟨W, hW⟩ := Sim.exists_vals_of_all hv
      refine ⟨a.store, a.frame, W, ?_, ?_⟩
      · rcases a with ⟨_, _, _⟩; dsimp only at hW; subst hW; exact hr
      · simpa [plug, hW] using hpa
    · rcases hinv with h | ht
      · exact (hS h).elim
      · exact (trapForm_not_div (c := plug a) (by
          obtain ⟨ws, rest, he⟩ := ht; exact ⟨ws, rest ++ Y, by simp [plug, he]⟩) hpa).elim

/-! ## Leaving a label -/

theorem label_exit {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cont : List Instr}
    {inner code : List Admin}
    (hd : Diverges P host ⟨s, f, vals vs ++ .label n cont inner :: code⟩) :
    Diverges P host ⟨s, f, inner⟩ ∨
      ∃ a : Config H, Steps P host ⟨s, f, inner⟩ a ∧ ∃ out, LabelExit n cont a.code out ∧
        Diverges P host ⟨a.store, a.frame, vals vs ++ out ++ code⟩ := by
  let plug : Config H → Config H := fun x => ⟨x.store, x.frame, vals vs ++ .label n cont x.code :: code⟩
  let bd : Config H → Config H → Prop := fun a b =>
    ∃ out, LabelExit n cont a.code out ∧ b = ⟨a.store, a.frame, vals vs ++ out ++ code⟩
  have peel : ∀ a b, Step P host (plug a) b → (∃ next, Step P host a next ∧ b = plug next) ∨ bd a b := by
    intro a b hs
    rcases a with ⟨sa, fa, xa⟩
    obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (by simp [Admin.IsCtx]) hs
    rcases Step.label_inv h₀ with ⟨s', f', is', hs', rfl⟩ | ⟨out, hx, rfl⟩
    · exact .inl ⟨⟨s', f', is'⟩, hs', by simp [plug]⟩
    · exact .inr ⟨out, hx, rfl⟩
  have hd' : InfiniteTrace (Step P host) (plug ⟨s, f, inner⟩) := hd
  rcases InfiniteTrace.context_decompose (Step P host) (Step P host) plug bd peel hd' with
    hin | ⟨a, b, hr, ⟨out, hx, rfl⟩, hb⟩
  · exact .inl hin
  · exact .inr ⟨a, hr, out, hx, hb⟩

theorem frag_steps {c c' : Config H} (h : Steps P host c c') (hF : Frag c.code) : Frag c'.code := by
  induction h with
  | refl => exact hF
  | tail _ st ih => exact (Proofs.Region.expand st ih).1

/-! ## Exceptions cannot diverge -/

/-- A thrown exception after values. -/
def ThrowForm (c : List Admin) : Prop := ∃ ws a rest, c = vals ws ++ throwing a ++ rest

theorem throwForm_step {c c' : Config H} (h : Step P host c c') (ht : ThrowForm c.code) :
    ThrowForm c'.code ∧ c'.code.length < c.code.length := by
  obtain ⟨ws, a, rest, hc⟩ := ht
  rcases c with ⟨s, f, x⟩
  rcases c' with ⟨s', f', x'⟩
  dsimp only at hc ⊢
  subst hc
  have e : vals ws ++ throwing a ++ rest = vals (ws ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by
    simp [throwing, vals, Val.toAdmin]
  rw [e] at h ⊢
  rcases Sim.Step.split_head rfl h with ⟨ws₁, us, is', hus, hs, rfl⟩ | ⟨h, -⟩ |
      ⟨-, -, -, ws₁, us, x, r, r', hus, rfl, hne, rfl⟩
  · rcases Step.throwRef_vals_inv hs with ⟨w, hw, he⟩ | ⟨w, w', b, hw, hne, he⟩
    · rw [hw] at hus
      have := congrArg List.getLast? hus; simp at this
    · simp only [Config.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      rw [hw] at hus
      have hl := congrArg List.length hus
      have := congrArg List.getLast? hus
      simp at this; subst this
      refine ⟨⟨ws₁ ++ w, a, rest, by simp⟩, ?_⟩
      simp [throwing] at hl ⊢
      have := List.length_pos_iff.2 hne
      omega
  · cases h
  · have hl := congrArg List.length hus
    have hx := congrArg List.getLast? hus
    simp at hx; subst hx
    refine ⟨⟨ws₁, _, r', rfl⟩, ?_⟩
    simp [throwing] at hl ⊢
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega

theorem throwForm_not_div {c : Config H} (ht : ThrowForm c.code) : ¬ Diverges P host c := by
  induction hn : c.code.length using Nat.strong_induction_on generalizing c with
  | _ N ih =>
  intro hd
  obtain ⟨c', hs, hd'⟩ := hd.unfold
  obtain ⟨ht', hl⟩ := throwForm_step hs ht
  exact ih _ (hn ▸ hl) ht' rfl hd'

/-- A handler around a thrown exception walks its clauses and leaves: it never diverges. -/
theorem handler_throwing_not_div {s : Store H} {f : Frame} {vs : List Val} {n a : Nat}
    {code : List Admin} :
    ∀ {cs : List Catch}, ¬ Diverges P host ⟨s, f, vals vs ++ .handler n cs (throwing a) :: code⟩
  | cs, hd => by
    obtain ⟨⟨s', f', x'⟩, hs, hd'⟩ := hd.unfold
    obtain ⟨c₀, h₀, he⟩ := Step.ctx_in_seq (by simp [Admin.IsCtx]) hs
    rcases Step.handler_inv h₀ with ⟨_, _, _, hs', -⟩ | ⟨out, hx, rfl⟩
    · exact Step.throwing_stuck hs'
    · simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      generalize hw : throwing a = w at hx
      cases hx with
      | vals => exact SingleThreaded.Det.mem_vals (a := .plain .throwRef) (by rw [← hw]; simp [throwing]) rfl
      | @br _ _ l _ =>
        have : Admin.plain (.br l) ∈ throwing a := by rw [hw]; simp
        simp [throwing] at this
      | ret =>
        have : Admin.plain .return_ ∈ throwing a := by rw [hw]; simp
        simp [throwing] at this
      | @returnCall _ _ c _ hc =>
        have : c ∈ throwing a := by rw [hw]; simp
        simp [throwing] at this
        rcases this with rfl | rfl <;> simp [Admin.IsReturnCallRef] at hc
      | trap => simp [throwing] at hw
      | throwEmpty b =>
        exact throwForm_not_div ⟨vs, b, code, by simp⟩ hd'
      | catch_ =>
        obtain ⟨c', hs, -⟩ := hd'.unfold
        exact br_stuck_seq (vs := vs ++ _) (rest := code) (by simpa using hs)
      | catchRef =>
        obtain ⟨c', hs, -⟩ := hd'.unfold
        exact br_stuck_seq (vs := vs ++ (_ ++ [.ref (.exn _)])) (rest := code)
          (by simpa [vals, Val.toAdmin] using hs)
      | catchAll =>
        obtain ⟨c', hs, -⟩ := hd'.unfold
        exact br_stuck_seq (vs := vs) (rest := code) (by simpa using hs)
      | catchAllRef =>
        obtain ⟨c', hs, -⟩ := hd'.unfold
        exact br_stuck_seq (vs := vs ++ [.ref (.exn _)]) (rest := code)
          (by simpa [vals, Val.toAdmin] using hs)
      | @next c cs' b _ =>
        simp [throwing] at hw; obtain ⟨-, rfl⟩ := hw
        exact handler_throwing_not_div (cs := cs') (by unfold Diverges; simpa using hd')

theorem handler_exit {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cs : List Catch}
    {inner code : List Admin}
    (hd : Diverges P host ⟨s, f, vals vs ++ .handler n cs inner :: code⟩) :
    Diverges P host ⟨s, f, inner⟩ ∨
      ∃ a : Config H, Steps P host ⟨s, f, inner⟩ a ∧ ∃ out,
        HandlerExit a.store a.frame n cs a.code out ∧
        Diverges P host ⟨a.store, a.frame, vals vs ++ out ++ code⟩ := by
  let plug : Config H → Config H := fun x => ⟨x.store, x.frame, vals vs ++ .handler n cs x.code :: code⟩
  let bd : Config H → Config H → Prop := fun a b =>
    ∃ out, HandlerExit a.store a.frame n cs a.code out ∧ b = ⟨a.store, a.frame, vals vs ++ out ++ code⟩
  have peel : ∀ a b, Step P host (plug a) b → (∃ next, Step P host a next ∧ b = plug next) ∨ bd a b := by
    intro a b hs
    rcases a with ⟨sa, fa, xa⟩
    obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (by simp [Admin.IsCtx]) hs
    rcases Step.handler_inv h₀ with ⟨s', f', is', hs', rfl⟩ | ⟨out, hx, rfl⟩
    · exact .inl ⟨⟨s', f', is'⟩, hs', by simp [plug]⟩
    · exact .inr ⟨out, hx, rfl⟩
  have hd' : InfiniteTrace (Step P host) (plug ⟨s, f, inner⟩) := hd
  rcases InfiniteTrace.context_decompose (Step P host) (Step P host) plug bd peel hd' with
    hin | ⟨a, b, hr, ⟨out, hx, rfl⟩, hb⟩
  · exact .inl hin
  · exact .inr ⟨a, hr, out, hx, hb⟩

end Silmaril.Wasm.Cfg.Proofs.Region
