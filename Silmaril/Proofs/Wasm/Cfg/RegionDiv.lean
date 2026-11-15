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

variable {H : Type} {P : Profile} {host : HostSemantics H}

abbrev Rel4 (H : Type) := Store H → Frame → List Val → List Admin → Prop

/-! ## The greatest fixed point -/

theorem DivF.mono {R S : Rel4 H} (hRS : ∀ s f vs c, R s f vs c → S s f vs c)
    {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : DivF P host R s f vs code) : DivF P host S s f vs code := by
  cases h with
  | val hv h => exact .val hv (hRS _ _ _ _ h)
  | simple hi h₁ h => exact .simple hi h₁ (hRS _ _ _ _ h)
  | brIf h => exact .brIf (hRS _ _ _ _ h)
  | block hbt hm h => exact .block hbt hm (hRS _ _ _ _ h)
  | loop hbt hm h => exact .loop hbt hm (hRS _ _ _ _ h)
  | if_ h => exact .if_ (hRS _ _ _ _ h)
  | labelIn h => exact .labelIn (hRS _ _ _ _ h)
  | labelNormal hin h => exact .labelNormal hin (hRS _ _ _ _ h)
  | labelBr0 hin hn h => exact .labelBr0 hin hn (hRS _ _ _ _ h)

theorem runDiv_unfold {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : RunDiv P host s f vs code) : DivF P host (RunDiv P host) s f vs code := by
  obtain ⟨R, hR, hx⟩ := h
  exact DivF.mono (fun s f vs c hc => ⟨R, hR, hc⟩) (hR _ _ _ _ hx)

/-- Coinduction up to `RunDiv`. -/
theorem runDiv_coind (X : Rel4 H)
    (hX : ∀ s f vs c, X s f vs c → DivF P host (fun s f vs c => X s f vs c ∨ RunDiv P host s f vs c)
      s f vs c)
    {s : Store H} {f : Frame} {vs : List Val} {code : List Admin} (h : X s f vs code) :
    RunDiv P host s f vs code := by
  refine ⟨fun s f vs c => X s f vs c ∨ RunDiv P host s f vs c, ?_, .inl h⟩
  rintro s f vs c (hc | hc)
  · exact hX _ _ _ _ hc
  · exact DivF.mono (fun _ _ _ _ h => .inr h) (runDiv_unfold hc)

theorem runDiv_vals {s : Store H} {f : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin},
      RunDiv P host s f (vs ++ ws) code → RunDiv P host s f vs (vals ws ++ code)
  | [], _, h => by simpa [vals] using h
  | w :: ws, code, h => by
    have ih := runDiv_vals (vs := vs ++ [w]) (ws := ws) (code := code) (by simpa using h)
    refine runDiv_coind (fun s' f' vs' c => s' = s ∧ f' = f ∧ vs' = vs ∧
      c = vals (w :: ws) ++ code) ?_ ⟨rfl, rfl, rfl, rfl⟩
    rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
    simp only [vals, List.map_cons, List.cons_append]
    exact .val (Admin.val?_toAdmin w) (.inr ih)

theorem runDiv_label {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cont : List Instr}
    {inner code : List Admin} (h : RunDiv P host s f [] inner) :
    RunDiv P host s f vs (.label n cont inner :: code) := by
  refine runDiv_coind (fun s' f' vs' c => s' = s ∧ f' = f ∧ vs' = vs ∧
    c = .label n cont inner :: code) ?_ ⟨rfl, rfl, rfl, rfl⟩
  rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  exact .labelIn (.inr h)

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

/-- A run of a non-value to values takes at least one step. -/
theorem atom_transGen {s s₁ : Store H} {f f₁ : Frame} {vs vs₁ : List Val} {a : Admin}
    (ha : a.val? = none) (h : Steps P host ⟨s, f, vals vs ++ [a]⟩ ⟨s₁, f₁, vals vs₁⟩) :
    Relation.TransGen (Step P host) ⟨s, f, vals vs ++ [a]⟩ ⟨s₁, f₁, vals vs₁⟩ := by
  refine transGen_of_steps h fun he => ?_
  simp only [Config.mk.injEq] at he
  have hm : a ∈ vals vs₁ := by rw [← he.2.2]; simp
  exact SingleThreaded.Det.mem_vals hm ha

theorem progress {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : RunDiv P host s f vs code) :
    ∃ s' f' vs' code', Relation.TransGen (Step P host) ⟨s, f, vals vs ++ code⟩
      ⟨s', f', vals vs' ++ code'⟩ ∧ RunDiv P host s' f' vs' code' := by
  induction hsz : sizeOf code using Nat.strong_induction_on generalizing s f vs code with
  | _ N ih =>
  subst hsz
  cases runDiv_unfold h with
  | @val _ _ a v code' hv hd =>
    obtain ⟨s', f', vs', c', hs, hd⟩ := ih (sizeOf code') (by simp) hd rfl
    refine ⟨s', f', vs', c', ?_, hd⟩
    rw [Admin.eq_of_val? hv]; simpa [vals] using hs
  | @simple s₁ _ f₁ _ vs₁ i code' hi h₁ hd =>
    refine ⟨s₁, f₁, vs₁, code', ?_, hd⟩
    have := transGen_in [] code' (atom_transGen (Proofs.Exec.val_none_of_noncontrol hi) h₁)
    simpa [vals] using this
  | @brIf _ ws k l code' hd =>
    refine ⟨_, _, ws, _, .single ?_, hd⟩
    split
    · rename_i hk; subst hk
      have := step_in (P := P) (host := host) ws code' (Step.brIfFalse (s := s) (f := f) (l := l))
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
    · rename_i hk
      have := step_in (P := P) (host := host) ws code'
        (Step.brIfTrue (s := s) (f := f) (l := l) hk)
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
  | @block _ ws us bt b t₁ t₂ code' hbt hm hd =>
    refine ⟨_, _, ws, _, .single ?_, hd⟩
    simpa using step_in (P := P) (host := host) ws code' (Step.block (s := s) (body := b) hbt hm)
  | @loop _ ws us bt b t₁ t₂ code' hbt hm hd =>
    refine ⟨_, _, ws, _, .single ?_, hd⟩
    simpa using step_in (P := P) (host := host) ws code' (Step.loop (s := s) (body := b) hbt hm)
  | @if_ _ ws k bt t e code' hd =>
    refine ⟨_, _, ws, _, .single ?_, hd⟩
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
    obtain ⟨s', f', vs', c', hs, hd⟩ := ih (sizeOf inner) (by simp; omega) hd rfl
    refine ⟨s', f', vs, .label n cont (vals vs' ++ c') :: code', ?_, runDiv_label (runDiv_vals hd)⟩
    have := transGen_in vs code' (transGen_label n cont (X := inner) (Y := vals vs' ++ c') hs)
    simpa using this
  | @labelNormal s₁ _ f₁ _ us n cont inner code' hin hd =>
    refine ⟨s₁, f₁, vs ++ us, code', ?_, hd⟩
    obtain ⟨c₁, hs₁, he₁⟩ := sound hin
    simp only [Out.Ends] at he₁; subst he₁
    have h1 := steps_in vs code' (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code'
      (Step.labelVals (s := s₁) (f := f₁) (n := n) (cont := cont) (vs := us))
    have := Relation.TransGen.tail' h1 h2
    simpa using this
  | @labelBr0 s₁ _ f₁ _ us₁ us₂ n cont inner code' hin hn hd =>
    refine ⟨s₁, f₁, vs, _, ?_, hd⟩
    obtain ⟨c₁, hs₁, x, rest, hx, rfl⟩ := sound hin
    have h1 := steps_in vs code' (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code'
      (Step.brLabelZero (s := s₁) (f := f₁) (n := n) (cont := cont) (vs' := us₁) (vs := us₂)
        (l := x) (rest := rest) hx hn)
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := Relation.TransGen.tail' h1 h2
    simpa using this

/-- **Soundness for divergence**: a diverging region run is an infinite Core 3.0 run. -/
theorem div_sound {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : RunDiv P host s f vs code) : Diverges P host ⟨s, f, vals vs ++ code⟩ := by
  refine InfiniteTrace.coinduct (fun c => ∃ s f vs code, RunDiv P host s f vs code ∧
    Steps P host c ⟨s, f, vals vs ++ code⟩) ?_ ⟨s, f, vs, code, h, .refl⟩
  rintro c ⟨s, f, vs, code, hd, hs⟩
  rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨b, hb, hr⟩
  · obtain ⟨s', f', vs', c', ht, hd'⟩ := progress hd
    obtain ⟨b, hb, hr⟩ := Relation.TransGen.head'_iff.1 ht
    exact ⟨b, hb, s', f', vs', c', hd', hr⟩
  · exact ⟨b, hb, s, f, vs, code, hd, hr⟩

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

/-! ## Completeness for divergence -/

theorem div_complete {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (hA : AtomTerm P host) (hF : Frag code) (hd : Diverges P host ⟨s, f, vals vs ++ code⟩) :
    RunDiv P host s f vs code := by
  refine ⟨fun s f vs code => Frag code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩, ?_, hF, hd⟩
  rintro s f vs code ⟨hF, hd⟩
  rcases code with _ | ⟨a, code⟩
  · obtain ⟨c', hs, -⟩ := hd.unfold
    exact (Step.not_vals (by simpa using hs)).elim
  have hF' : Frag code := fun x hx => hF x (by simp [hx])
  have ha := hF a (by simp)
  -- values
  have val_case : ∀ v, a.val? = some v → DivF P host
      (fun s f vs code => Frag code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩) s f vs (a :: code) :=
    fun v hv => .val hv ⟨hF', by rw [Admin.eq_of_val? hv] at hd; simpa [vals] using hd⟩
  cases ha with
  | val h =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    exact val_case v hv
  | trap => exact (trapForm_not_div ⟨vs, code, rfl⟩ hd).elim
  | @label n cont inner hc hi =>
    rcases label_exit hd with hin | ⟨⟨sa, fa, xa⟩, hr, out, hx, hb⟩
    · exact .labelIn ⟨hi, by simpa [vals] using hin⟩
    · have hFa : Frag xa := frag_steps hr hi
      cases hx with
      | vals ws =>
        have hin : Run P host s f [] inner sa fa (.normal ws) := Proofs.Region.complete hi hr rfl
        exact .labelNormal hin ⟨hF', by simpa using hb⟩
      | @brZero vs' us l rest hl hn =>
        have hin : Run P host s f [] inner sa fa (.br 0 (vs' ++ us)) :=
          Proofs.Region.complete hi hr ⟨l, rest, hl, by simp⟩
        refine .labelBr0 hin hn ⟨?_, by simpa using hb⟩
        exact frag_append.2 ⟨frag_append.2 ⟨frag_vals _, frag_expression hc⟩, hF'⟩
      | @brSucc us l rest _ =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs ++ us) (rest := code) (by simpa using hs)).elim
      | @ret us rest =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (ret_stuck_seq (vs := vs ++ us) (rest := code) (by simpa using hs)).elim
      | @returnCall us c rest hc' =>
        exact (fragA_retCallRef (hFa c (by simp)) hc').elim
      | throw a =>
        exact (fragA_throwRef (hFa (.plain .throwRef) (by simp [throwing]))).elim
      | trap => exact (trapForm_not_div ⟨vs, code, by simp⟩ hb).elim
  | @plain i hI =>
    cases hI with
    | simple hk =>
      obtain ⟨s₁, f₁, vs₁, h₁, hd₁⟩ := atom_exit hk (hA s f vs i hk) hd
      exact .simple hk h₁ ⟨hF', hd₁⟩
    | const h =>
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
      exact val_case v hv
    | @block bt b hb =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', us', t₁, t₂, rfl, hbt, hm, he⟩ := Step.block_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : Frag (.label t₂.length [] (vals us' ++ expression b) :: code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .label (by simp) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩)
        · exact hF' x hx
      have := DivF.block (P := P) (host := host)
        (R := fun s f vs code => Frag code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩)
        (ws := ws ++ ws') (code := code) hbt hm ⟨hFl, by unfold Diverges; simpa using hd₁⟩
      simpa using this
    | @loop bt b hb =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', us', t₁, t₂, rfl, hbt, hm, he⟩ := Step.loop_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : Frag (.label t₁.length [.loop bt b] (vals us' ++ expression b) :: code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .label (by simp [FragI.loop hb]) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩)
        · exact hF' x hx
      have := DivF.loop (P := P) (host := host)
        (R := fun s f vs code => Frag code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩)
        (ws := ws ++ ws') (code := code) hbt hm ⟨hFl, by unfold Diverges; simpa using hd₁⟩
      simpa using this
    | @if_ bt t e ht he' =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', k, rfl, he⟩ := Step.if_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : Frag (.plain (.block bt (if k = 0 then e else t)) :: code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · split
          · exact .plain (.block he')
          · exact .plain (.block ht)
        · exact hF' x hx
      have := DivF.if_ (P := P) (host := host)
        (R := fun s f vs code => Frag code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩)
        (ws := ws ++ ws') (k := k) (t := t) (e := e) (code := code) ⟨hFl, by unfold Diverges; simpa using hd₁⟩
      simpa using this
    | br l =>
      obtain ⟨c', hs, -⟩ := hd.unfold
      exact (br_stuck_seq hs).elim
    | return_ =>
      obtain ⟨c', hs, -⟩ := hd.unfold
      exact (ret_stuck_seq hs).elim
    | brIf l =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', k, rfl, he⟩ := Step.brIf_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : Frag ((if k = 0 then [] else [.plain (.br l)]) ++ code) := by
        refine frag_append.2 ⟨?_, hF'⟩
        split
        · intro x hx; simp at hx
        · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact .plain (.br l)
      have := DivF.brIf (P := P) (host := host)
        (R := fun s f vs code => Frag code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩)
        (ws := ws ++ ws') (k := k) (l := l) (code := code) ⟨hFl, by unfold Diverges; simpa using hd₁⟩
      simpa using this

/-- **Adequacy for divergence**, given the atomic obligation. -/
theorem div_adequate {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (hA : AtomTerm P host) (hF : Frag code) :
    RunDiv P host s f vs code ↔ Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  ⟨div_sound, div_complete hA hF⟩

end Silmaril.Wasm.Cfg.Proofs.Region
