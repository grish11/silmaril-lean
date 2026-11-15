module

public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Proofs.Wasm.Cfg.Exec
public import Silmaril.Wasm.Execution.Core.Inversion.Thms

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (Det.famOf)

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Basic facts -/

theorem famOf_val {a : Admin} {v : Val} (h : a.val? = some v) : Det.famOf a = .control := by
  by_contra hk
  have := Proofs.Exec.val_none_of_noncontrol hk
  simp [h] at this

/-- Values push. -/
theorem run_vals {s s' : Store H} {f f' : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin} {o : Out},
      Run P host s f (vs ++ ws) code s' f' o → Run P host s f vs (vals ws ++ code) s' f' o
  | [], _, _, h => by simpa [vals] using h
  | w :: ws, code, o, h => by
    simp only [vals, List.map_cons, List.cons_append]
    exact .val (Admin.val?_toAdmin w) (run_vals (vs := vs ++ [w]) (by simpa using h))

theorem run_val_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {v : Val}
    {code : List Admin} {o : Out} (hv : a.val? = some v)
    (h : Run P host s f vs (a :: code) s' f' o) : Run P host s f (vs ++ [v]) code s' f' o := by
  cases h with
  | val hv' h => rw [hv] at hv'; cases hv'; exact h
  | simple hi => exact absurd (famOf_val hv) hi
  | simpleTrap hi => exact absurd (famOf_val hv) hi
  | _ => simp [Admin.val?] at hv

theorem run_vals_inv {s s' : Store H} {f f' : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin} {o : Out},
      Run P host s f vs (vals ws ++ code) s' f' o → Run P host s f (vs ++ ws) code s' f' o
  | [], _, _, h => by simpa [vals] using h
  | w :: ws, code, o, h => by
    simp only [vals, List.map_cons, List.cons_append] at h
    have := run_vals_inv (vs := vs ++ [w]) (run_val_inv (Admin.val?_toAdmin w) h)
    simpa using this

theorem run_vals_iff {s s' : Store H} {f f' : Frame} {vs ws : List Val} {code : List Admin}
    {o : Out} :
    Run P host s f vs (vals ws ++ code) s' f' o ↔ Run P host s f (vs ++ ws) code s' f' o :=
  ⟨run_vals_inv, run_vals⟩

theorem run_nil_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {o : Out}
    (h : Run P host s f vs [] s' f' o) : o = .normal vs ∧ s' = s ∧ f' = f := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem run_trap_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin}
    {o : Out} (h : Run P host s f vs (.trap :: code) s' f' o) :
    o = .trap ∧ s' = s ∧ f' = f := by
  cases h with
  | trap => exact ⟨rfl, rfl, rfl⟩
  | val hv => simp [Admin.val?] at hv

theorem run_br_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {l : LabelIdx}
    {code : List Admin} {o : Out} (h : Run P host s f vs (.plain (.br l) :: code) s' f' o) :
    o = .br l.toNat vs ∧ s' = s ∧ f' = f := by
  cases h with
  | br => exact ⟨rfl, rfl, rfl⟩
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [Det.famOf] at hi
  | simpleTrap hi => simp [Det.famOf] at hi

theorem run_ret_inv {s s' : Store H} {f f' : Frame} {vs : List Val}
    {code : List Admin} {o : Out} (h : Run P host s f vs (.plain .return_ :: code) s' f' o) :
    o = .ret vs ∧ s' = s ∧ f' = f := by
  cases h with
  | ret => exact ⟨rfl, rfl, rfl⟩
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [Det.famOf] at hi
  | simpleTrap hi => simp [Det.famOf] at hi

/-! ## Runs in contexts -/

theorem step_in {s s' : Store H} {f f' : Frame} {X Y : List Admin} (vs : List Val)
    (code : List Admin) (h : Step P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Step P host ⟨s, f, vals vs ++ X ++ code⟩ ⟨s', f', vals vs ++ Y ++ code⟩ :=
  Sim.Step.append_right (Sim.Step.vals_left h vs) code

theorem steps_in {s s' : Store H} {f f' : Frame} {X Y : List Admin} (vs : List Val)
    (code : List Admin) (h : Steps P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps P host ⟨s, f, vals vs ++ X ++ code⟩ ⟨s', f', vals vs ++ Y ++ code⟩ :=
  Sim.Steps.append_right (Sim.Steps.vals_left h vs) code

theorem steps_label {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cont : List Instr) (h : Steps P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps P host ⟨s, f, [.label n cont X]⟩ ⟨s', f', [.label n cont Y]⟩ :=
  Relation.ReflTransGen.lift (p := Step P host)
    (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtLabel st) _ _ h

theorem steps_trap (s : Store H) (f : Frame) (vs : List Val) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ .trap :: rest⟩ ⟨s, f, [.trap]⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · have e : vals vs ++ .trap :: rest = vals vs ++ [.trap] ++ rest := by simp
    rw [e]
    exact .single (Step.trapInstrs hne)
  · have hv : vs = [] ∧ rest = [] := by simpa only [ne_eq, not_or, Decidable.not_not] using hne
    rw [hv.1, hv.2]
    exact .refl

@[simp] theorem labelPred_toNat (l : LabelIdx) : (labelPred l).toNat = l.toNat - 1 := rfl

/-! ## Soundness: a region run is a Core run -/

theorem sound {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Out}
    (h : Run P host s f vs code s' f' o) :
    ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' := by
  induction h with
  | nil => exact ⟨_, .refl, by simp [Out.Ends]⟩
  | @val s s' f f' vs a v code o hv _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', ?_, he⟩
    rw [Admin.eq_of_val? hv]
    simpa [vals] using hs
  | @simple s s₁ s' f f₁ f' vs vs₁ i code o _ h₁ _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', ?_, he⟩
    have := steps_in [] code h₁
    simp only [vals, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append]
      at this
    exact this.trans (by simpa [vals] using hs)
  | @simpleTrap s s₁ f f₁ vs i code _ h₁ =>
    refine ⟨[.trap], ?_, rfl⟩
    have := steps_in [] code h₁
    simp only [vals, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append]
      at this
    exact this.trans (by simpa [vals] using steps_trap (P := P) (host := host) s₁ f₁ [] code)
  | @trap s f vs code => exact ⟨_, steps_trap s f vs code, rfl⟩
  | @br s f vs l code => exact ⟨_, .refl, l, code, rfl, rfl⟩
  | @ret s f vs code => exact ⟨_, .refl, code, rfl⟩
  | @brIf s s' f f' ws k l code o _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ (by simpa using hs), he⟩
    split
    · rename_i hk; subst hk
      have := step_in (P := P) (host := host) ws code (Step.brIfFalse (s := s) (f := f) (l := l))
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
    · rename_i hk
      have := step_in (P := P) (host := host) ws code (Step.brIfTrue (s := s) (f := f) (l := l) hk)
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
  | @block s s' f f' ws us bt b t₁ t₂ code o hbt hm _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ (by simpa using hs), he⟩
    have := step_in (P := P) (host := host) ws code (Step.block (s := s) (body := b) hbt hm)
    simpa using this
  | @loop s s' f f' ws us bt b t₁ t₂ code o hbt hm _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ (by simpa using hs), he⟩
    have := step_in (P := P) (host := host) ws code (Step.loop (s := s) (body := b) hbt hm)
    simpa using this
  | @if_ s s' f f' ws k bt t e code o _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ (by simpa using hs), he⟩
    split
    · rename_i hk; subst hk
      have := step_in (P := P) (host := host) ws code
        (Step.ifFalse (s := s) (f := f) (bt := bt) (b₁ := t) (b₂ := e))
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
    · rename_i hk
      have := step_in (P := P) (host := host) ws code
        (Step.ifTrue (s := s) (f := f) (bt := bt) (b₁ := t) (b₂ := e) hk)
      simpa [vals, Val.toAdmin, constI32, Val.i32] using this
  | @labelNormal s s₁ s' f f₁ f' vs us n cont inner code o _ _ ihin ih =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    obtain ⟨c', hs, he⟩ := ih
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨c', ?_, he⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.labelVals (s := s₁) (f := f₁) (n := n) (cont := cont) (vs := us))
    have := (h1.tail h2).trans (by simpa using hs)
    simpa using this
  | @labelBr0 s s₁ s' f f₁ f' vs us₁ us₂ n cont inner code o _ hn _ ihin ih =>
    obtain ⟨c₁, hs₁, x, rest, hx, rfl⟩ := ihin
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', ?_, he⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.brLabelZero (s := s₁) (f := f₁) (n := n) (cont := cont) (vs' := us₁) (vs := us₂)
        (l := x) (rest := rest) hx hn)
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := (h1.tail h2).trans (by simpa using hs)
    simpa using this
  | @labelBrSucc s s₁ f f₁ vs us n l cont inner code _ ihin =>
    obtain ⟨c₁, hs₁, x, rest, hx, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.plain (.br (labelPred x))]) ++ code, ?_,
      labelPred x, code, by simp [hx], by simp⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.brLabelSucc (s := s₁) (f := f₁) (n := n) (cont := cont) (vs := us) (l := x)
        (rest := rest) (by omega))
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := h1.tail h2
    simpa using this
  | @labelRet s s₁ f f₁ vs us n cont inner code _ ihin =>
    obtain ⟨c₁, hs₁, rest, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.plain .return_]) ++ code, ?_, code, by simp⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.returnLabel (s := s₁) (f := f₁) (n := n) (cont := cont) (vs := us) (rest := rest))
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := h1.tail h2
    simpa using this
  | @labelTrap s s₁ f f₁ vs n cont inner code _ ihin =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨[.trap], ?_, rfl⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.trapLabel (s := s₁) (f := f₁) (n := n) (cont := cont))
    have := (h1.tail h2).trans (by simpa using steps_trap (P := P) (host := host) s₁ f₁ vs code)
    simpa using this

/-! ## Sequencing -/

theorem run_append {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {A B : List Admin}
    {o₁ o : Out} (h : Run P host s f vs A s₁ f₁ o₁) (hB : Then P host s₁ f₁ o₁ B s' f' o) :
    Run P host s f vs (A ++ B) s' f' o := by
  induction h with
  | nil => exact hB
  | val hv _ ih => exact .val hv (ih hB)
  | simple hi h₁ _ ih => exact .simple hi h₁ (ih hB)
  | simpleTrap hi h₁ => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .simpleTrap hi h₁
  | trap => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .trap
  | br => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .br
  | ret => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .ret
  | brIf _ ih => exact .brIf (by simpa using ih hB)
  | block hbt hm _ ih => exact .block hbt hm (ih hB)
  | loop hbt hm _ ih => exact .loop hbt hm (ih hB)
  | if_ _ ih => exact .if_ (ih hB)
  | labelNormal hin _ _ ih => exact .labelNormal hin (ih hB)
  | labelBr0 hin hn _ _ ih => exact .labelBr0 hin hn (by simpa using ih hB)
  | labelBrSucc hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelBrSucc hin
  | labelRet hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelRet hin
  | labelTrap hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelTrap hin

theorem run_split {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Out}
    (h : Run P host s f vs code s' f' o) :
    ∀ {A B : List Admin}, code = A ++ B →
      ∃ s₁ f₁ o₁, Run P host s f vs A s₁ f₁ o₁ ∧ Then P host s₁ f₁ o₁ B s' f' o := by
  induction h with
  | nil =>
    intro A B hA
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hA.symm
    exact ⟨_, _, _, .nil, .nil⟩
  | val hv h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .val hv h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih rfl
      exact ⟨_, _, _, .val hv h₁, h₂⟩
  | simple hi h₁ h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .simple hi h₁ h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁', h₂⟩ := ih rfl
      exact ⟨_, _, _, .simple hi h₁ h₁', h₂⟩
  | simpleTrap hi h₁ =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .simpleTrap hi h₁⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .simpleTrap hi h₁, rfl, rfl, rfl⟩
  | trap =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .trap⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .trap, rfl, rfl, rfl⟩
  | br =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .br⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .br, rfl, rfl, rfl⟩
  | ret =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .ret⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .ret, rfl, rfl, rfl⟩
  | @brIf s s' f f' ws k l code o h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .brIf h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (List.append_assoc _ _ _).symm
      exact ⟨_, _, _, .brIf h₁, h₂⟩
  | block hbt hm h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .block hbt hm h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := _ :: A) rfl
      exact ⟨_, _, _, .block hbt hm h₁, h₂⟩
  | loop hbt hm h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .loop hbt hm h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := _ :: A) rfl
      exact ⟨_, _, _, .loop hbt hm h₁, h₂⟩
  | if_ h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .if_ h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := _ :: A) rfl
      exact ⟨_, _, _, .if_ h₁, h₂⟩
  | labelNormal hin h _ ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelNormal hin h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih rfl
      exact ⟨_, _, _, .labelNormal hin h₁, h₂⟩
  | @labelBr0 _ _ _ _ _ _ _ _ us₂ _ cont _ _ _ hin hn h _ ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelBr0 hin hn h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := vals us₂ ++ expression cont ++ A) (B := B) (by simp)
      exact ⟨_, _, _, .labelBr0 hin hn h₁, h₂⟩
  | labelBrSucc hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelBrSucc hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .labelBrSucc hin, rfl, rfl, rfl⟩
  | labelRet hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelRet hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .labelRet hin, rfl, rfl, rfl⟩
  | labelTrap hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelTrap hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .labelTrap hin, rfl, rfl, rfl⟩

/-! ## The fragment -/

theorem fragA_plain {i : Instr} (h : FragA (.plain i)) : FragI i := by
  cases h with
  | val h => exact .const h
  | plain h => exact h

theorem fragI_block {bt : BlockType} {b : List Instr} (h : FragI (.block bt b)) :
    ∀ i ∈ b, FragI i := by
  cases h with
  | simple h => simp [Det.famOf] at h
  | const h => simp [Admin.val?] at h
  | block h => exact h

theorem fragI_loop {bt : BlockType} {b : List Instr} (h : FragI (.loop bt b)) :
    ∀ i ∈ b, FragI i := by
  cases h with
  | simple h => simp [Det.famOf] at h
  | const h => simp [Admin.val?] at h
  | loop h => exact h

theorem fragI_if {bt : BlockType} {t e : List Instr} (h : FragI (.if_ bt t e)) :
    (∀ i ∈ t, FragI i) ∧ ∀ i ∈ e, FragI i := by
  cases h with
  | simple h => simp [Det.famOf] at h
  | const h => simp [Admin.val?] at h
  | if_ ht he => exact ⟨ht, he⟩

theorem fragA_label {n : Nat} {cont : List Instr} {inner : List Admin}
    (h : FragA (.label n cont inner)) : (∀ i ∈ cont, FragI i) ∧ Frag inner := by
  cases h with
  | val h => simp [Admin.val?] at h
  | label hc hi => exact ⟨hc, hi⟩

theorem fragA_callRef {c : Admin} (h : FragA c) (hc : c.IsCallRef) : False := by
  have hv := Admin.val?_of_isCallRef hc
  have hk := Proofs.Exec.isCallRef_control hc
  cases h with
  | val h => exact h hv
  | plain h =>
    cases h with
    | simple h => exact h hk
    | const h => exact h hv
    | _ => simp [Admin.IsCallRef] at hc
  | trap => simp [Admin.IsCallRef] at hc
  | label => simp [Admin.IsCallRef] at hc

theorem fragA_retCallRef {c : Admin} (h : FragA c) (hc : c.IsReturnCallRef) : False := by
  have hv := Admin.val?_of_isReturnCallRef hc
  cases h with
  | val h => exact h hv
  | plain h =>
    rename_i i
    cases i <;> simp [Admin.IsReturnCallRef] at hc
    cases h with
    | simple h => simp [Det.famOf] at h
    | const h => simp [Admin.val?] at h
  | trap => simp [Admin.IsReturnCallRef] at hc
  | label => simp [Admin.IsReturnCallRef] at hc

theorem frag_vals (vs : List Val) : Frag (vals vs) := fun _ ha =>
  .val (SingleThreaded.Det.mem_vals ha)

theorem frag_expression {b : List Instr} (h : ∀ i ∈ b, FragI i) : Frag (expression b) := by
  intro a ha
  simp only [expression, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact .plain (h i hi)

theorem fragA_simple {a : Admin} (h : SimpleAdmin a) : FragA a := by
  rcases h with h | ⟨i, rfl, hi⟩
  · exact .val h
  · exact .plain (.simple hi)

theorem frag_append {A B : List Admin} : Frag (A ++ B) ↔ Frag A ∧ Frag B := by
  unfold Frag; exact List.forall_mem_append

/-- Closes a case whose code holds an instruction outside the fragment. -/
local macro "frag_contra" hF:ident : tactic => `(tactic| (
  exfalso
  simp only [Frag, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_nil, and_true,
    throwing, List.cons_append, List.nil_append, List.append_assoc] at $hF:ident
  casesm* _ ∧ _
  cases_type* FragA FragI <;> simp_all [Det.famOf, Admin.val?]))

/-! ## Straight-line code -/

theorem run_simple_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {i : Instr}
    {code : List Admin} {o : Out} (hi : Det.famOf (.plain i) ≠ .control)
    (h : Run P host s f vs (.plain i :: code) s' f' o) :
    (∃ s₁ f₁ vs₁, Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩ ∧
        Run P host s₁ f₁ vs₁ code s' f' o) ∨
      (o = .trap ∧ Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s', f', [.trap]⟩) := by
  cases h with
  | val hv => exact absurd (Proofs.Exec.val_none_of_noncontrol hi) (by simp [hv])
  | simple _ h₁ h => exact .inl ⟨_, _, _, h₁, h⟩
  | simpleTrap _ h₁ => exact .inr ⟨rfl, h₁⟩
  | _ => simp [Det.famOf] at hi

/-- A run of simple code followed by `es` runs the simple code by Core reduction first. -/
theorem run_simple_split {es : List Admin} :
    ∀ {B : List Admin} {s s' : Store H} {f f' : Frame} {vs : List Val} {o : Out},
      (∀ b ∈ B, SimpleAdmin b) → Run P host s f vs (B ++ es) s' f' o →
      (∃ s₂ f₂ vs₂, Steps P host ⟨s, f, vals vs ++ B⟩ ⟨s₂, f₂, vals vs₂⟩ ∧
          Run P host s₂ f₂ vs₂ es s' f' o) ∨
        (o = .trap ∧ Steps P host ⟨s, f, vals vs ++ B⟩ ⟨s', f', [.trap]⟩)
  | [], _, _, _, _, _, _, _, h => .inl ⟨_, _, _, by simpa using .refl, h⟩
  | b :: B, s, s', f, f', vs, o, hB, h => by
    have hB' : ∀ b ∈ B, SimpleAdmin b := fun x hx => hB x (by simp [hx])
    rcases hB b (by simp) with hb | ⟨i, rfl, hi⟩
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hb
      have e : vals vs ++ b :: B = vals (vs ++ [v]) ++ B := by
        rw [Admin.eq_of_val? hv]; simp [vals]
      rw [e]
      exact run_simple_split hB' (run_val_inv hv h)
    · rcases run_simple_inv hi h with ⟨s₁, f₁, vs₁, h₁, h⟩ | ⟨rfl, h₁⟩
      · have l₁ := steps_in [] B h₁
        simp only [vals, List.map_nil, List.nil_append, List.append_assoc,
          List.singleton_append] at l₁
        rcases run_simple_split hB' h with ⟨s₂, f₂, vs₂, h₂, h₃⟩ | ⟨rfl, h₂⟩
        · exact .inl ⟨s₂, f₂, vs₂, l₁.trans (by simpa [vals] using h₂), h₃⟩
        · exact .inr ⟨rfl, l₁.trans (by simpa [vals] using h₂)⟩
      · right
        refine ⟨rfl, ?_⟩
        have l₁ := steps_in [] B h₁
        simp only [vals, List.map_nil, List.nil_append, List.append_assoc,
          List.singleton_append] at l₁
        exact l₁.trans (by simpa [vals] using steps_trap (P := P) (host := host) s' f' [] B)

/-! ## Expansion: a region run of the successor is one of the predecessor -/

theorem expand_fam {c c₁ : Config H} (h : Step P host c c₁) {args : List Val} {e : Admin}
    (hc : c.code = vals args ++ [e]) (hk : Det.famOf e ≠ .control) :
    Frag c₁.code ∧ ∀ {vs : List Val} {s' : Store H} {f' : Frame} {o : Out},
      Run P host c₁.store c₁.frame vs c₁.code s' f' o →
        Run P host c.store c.frame vs c.code s' f' o := by
  have hres := Proofs.Exec.step_noncontrol h args e hc hk
  obtain ⟨i, rfl⟩ : ∃ i, e = .plain i := by
    cases e with
    | plain i => exact ⟨i, rfl⟩
    | _ => simp [Det.famOf] at hk
  rcases c with ⟨s, f, code⟩
  rcases c₁ with ⟨s₁, f₁, code₁⟩
  dsimp only at hc hres ⊢
  subst hc
  have hstep : ∀ vs : List Val,
      Step P host ⟨s, f, vals (vs ++ args) ++ [.plain i]⟩ ⟨s₁, f₁, vals vs ++ code₁⟩ := by
    intro vs; simpa using Sim.Step.vals_left h vs
  rcases hres with hB | ⟨ws, rfl⟩
  · refine ⟨fun a ha => fragA_simple (hB a ha), ?_⟩
    intro vs s' f' o hr
    apply run_vals
    rcases run_simple_split (es := []) hB (by simpa using hr) with
      ⟨s₂, f₂, vs₂, h₂, h₃⟩ | ⟨rfl, h₂⟩
    · obtain ⟨rfl, rfl, rfl⟩ := run_nil_inv h₃
      exact .simple hk (.head (hstep vs) h₂) .nil
    · exact .simpleTrap hk (.head (hstep vs) h₂)
  · refine ⟨frag_append.2 ⟨frag_vals ws, fun a ha => by simp at ha; subst ha; exact .trap⟩, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_trap_inv (run_vals_inv hr)
    apply run_vals
    refine .simpleTrap hk (.head (hstep vs) ?_)
    simpa using steps_trap (P := P) (host := host) _ _ (vs ++ ws) []

theorem frag_single {a : Admin} (h : Frag [a]) : FragA a := h a (by simp)

theorem frag_last {l : List Admin} {a : Admin} (h : Frag (l ++ [a])) : FragA a := h a (by simp)

theorem run_br_at {s : Store H} {f : Frame} (us : List Val) (l : LabelIdx) (rest : List Admin) :
    Run P host s f [] (vals us ++ .plain (.br l) :: rest) s f (.br l.toNat us) :=
  run_vals (by simpa using (Run.br (P := P) (host := host) (s := s) (f := f) (vs := us) (l := l)
    (code := rest)))

theorem run_ret_at {s : Store H} {f : Frame} (us : List Val) (rest : List Admin) :
    Run P host s f [] (vals us ++ .plain .return_ :: rest) s f (.ret us) :=
  run_vals (by simpa using (Run.ret (P := P) (host := host) (s := s) (f := f) (vs := us)
    (code := rest)))

theorem run_vals_normal {s : Store H} {f : Frame} (us : List Val) :
    Run P host s f [] (vals us) s f (.normal us) := by
  have := run_vals (P := P) (host := host) (s := s) (f := f) (vs := []) (ws := us) (code := [])
    (by simpa using (Run.nil (P := P) (host := host) (s := s) (f := f) (vs := us)))
  simpa using this

theorem fragA_throwRef : ¬ FragA (.plain .throwRef) := by
  intro h
  cases h with
  | val h => simp [Admin.val?] at h
  | plain h => cases h <;> simp_all [Det.famOf, Admin.val?]

/-- Rebuild a label run from a run of its body's successor. -/
theorem label_back {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {n : Nat}
    {cont : List Instr} {inner inner' code : List Admin} {o : Out}
    (hb : ∀ {o₁ : Out} {s₂ : Store H} {f₂ : Frame},
      Run P host s₁ f₁ [] inner' s₂ f₂ o₁ → Run P host s f [] inner s₂ f₂ o₁)
    (h : Run P host s₁ f₁ vs (.label n cont inner' :: code) s' f' o) :
    Run P host s f vs (.label n cont inner :: code) s' f' o := by
  cases h with
  | val hv => simp [Admin.val?] at hv
  | labelNormal hin h => exact .labelNormal (hb hin) h
  | labelBr0 hin hn h => exact .labelBr0 (hb hin) hn h
  | labelBrSucc hin => exact .labelBrSucc (hb hin)
  | labelRet hin => exact .labelRet (hb hin)
  | labelTrap hin => exact .labelTrap (hb hin)

theorem expand {c c₁ : Config H} (h : Step P host c c₁) : Frag c.code →
    Frag c₁.code ∧ ∀ {vs : List Val} {s' : Store H} {f' : Frame} {o : Out},
      Run P host c₁.store c₁.frame vs c₁.code s' f' o →
        Run P host c.store c.frame vs c.code s' f' o := by
  induction h with
  | parametric h' =>
    intro _
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.ParametricStep.shape h'
    exact expand_fam (.parametric h') hc (by rw [hk]; decide)
  | numeric h' =>
    intro _
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.NumericStep.shape h'
    exact expand_fam (.numeric h') hc (by rw [hk]; decide)
  | vector h' =>
    intro _
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.VectorStep.shape h'
    exact expand_fam (.vector h') hc (by rw [hk]; decide)
  | @«variable» c c' h' =>
    intro _
    rcases c with ⟨s, f, l⟩
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.VariableStep.shape h'
    exact expand_fam (.variable h') hc (by rw [hk]; decide)
  | @table c c' h' =>
    intro _
    rcases c with ⟨s, f, l⟩
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.TableStep.shape h'
    exact expand_fam (.table h') hc (by rw [hk]; decide)
  | @memory c c' h' =>
    intro _
    rcases c with ⟨s, f, l⟩
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.MemoryStep.shape h'
    exact expand_fam (.memory h') hc (by rw [hk]; decide)
  | @reference c c' h' =>
    intro _
    rcases c with ⟨s, f, l⟩
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.RefStep.shape h'
    exact expand_fam (.reference h') hc (by rw [hk]; decide)
  | @aggregate c c' h' =>
    intro _
    rcases c with ⟨s, f, l⟩
    obtain ⟨args, e, hc, -, hk⟩ := SingleThreaded.Det.AggregateStep.shape h'
    exact expand_fam (.aggregate h') hc (by rw [hk]; decide)
  | @ctxtInstrs s s' f f' vs₀ is is' rest _ _ ih =>
    intro hF
    dsimp only at hF ⊢
    obtain ⟨hF₁, hF₂⟩ := frag_append.1 hF
    obtain ⟨-, hF₃⟩ := frag_append.1 hF₁
    obtain ⟨hF', hb⟩ := ih hF₃
    refine ⟨frag_append.2 ⟨frag_append.2 ⟨frag_vals vs₀, hF'⟩, hF₂⟩, ?_⟩
    intro vs s'' f'' o hr
    rw [List.append_assoc] at hr ⊢
    apply run_vals
    obtain ⟨s₁, f₁, o₁, h₁, h₂⟩ := run_split (run_vals_inv hr) rfl
    exact run_append (hb h₁) h₂
  | ctxtLabel _ ih =>
    intro hF
    dsimp only at hF ⊢
    obtain ⟨hc, hi⟩ := fragA_label (frag_single hF)
    obtain ⟨hF', hb⟩ := ih hi
    refine ⟨fun a ha => by simp at ha; subst ha; exact .label hc hF', ?_⟩
    intro vs s'' f'' o hr
    exact label_back hb hr
  | ctxtHandler => intro hF; frag_contra hF
  | ctxtFrame => intro hF; frag_contra hF
  | @block s f bt b vs t₁ t₂ hbt hm =>
    intro hF
    dsimp only at hF ⊢
    have hb := fragI_block (fragA_plain (frag_last hF))
    refine ⟨fun a ha => by
      simp at ha; subst ha
      exact .label (by simp) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩), ?_⟩
    intro ws s' f' o hr
    exact run_vals (.block hbt hm hr)
  | @loop s f bt b vs t₁ t₂ hbt hm =>
    intro hF
    dsimp only at hF ⊢
    have hb := fragI_loop (fragA_plain (frag_last hF))
    refine ⟨fun a ha => by
      simp at ha; subst ha
      exact .label (by simp [FragI.loop hb]) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩),
      ?_⟩
    intro ws s' f' o hr
    exact run_vals (.loop hbt hm hr)
  | @ifTrue s f k bt t e hk =>
    intro hF
    dsimp only at hF ⊢
    obtain ⟨ht, he⟩ := fragI_if (fragA_plain (frag_last (l := [constI32 _]) hF))
    refine ⟨fun a ha => by simp at ha; subst ha; exact .plain (.block ht), ?_⟩
    intro ws s' f' o hr
    refine .val (v := .i32 k) rfl (.if_ ?_)
    split
    · rename_i h0; exact absurd h0 hk
    · exact hr
  | @ifFalse s f bt t e =>
    intro hF
    dsimp only at hF ⊢
    obtain ⟨ht, he⟩ := fragI_if (fragA_plain (frag_last (l := [constI32 _]) hF))
    refine ⟨fun a ha => by simp at ha; subst ha; exact .plain (.block he), ?_⟩
    intro ws s' f' o hr
    exact .val (v := .i32 0) rfl (.if_ (by simpa using hr))
  | @labelVals s f n cont us =>
    intro hF
    refine ⟨frag_vals us, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_nil_inv (run_vals_inv (code := []) (by simpa using hr))
    exact .labelNormal (run_vals_normal us) .nil
  | @brLabelZero s f n cont vs' us l rest hl hn =>
    intro hF
    dsimp only at hF ⊢
    obtain ⟨hc, -⟩ := fragA_label (frag_single hF)
    refine ⟨frag_append.2 ⟨frag_vals _, frag_expression hc⟩, ?_⟩
    intro vs s' f' o hr
    refine .labelBr0 (us₁ := vs') (us₂ := us) ?_ hn (by simpa using hr)
    have := run_br_at (P := P) (host := host) (s := s) (f := f) (vs' ++ us) l rest
    rw [hl] at this
    simpa using this
  | @brLabelSucc s f n cont us l rest hl =>
    intro hF
    refine ⟨frag_append.2 ⟨frag_vals _, fun a ha => by
      simp at ha; subst ha; exact .plain (.br _)⟩, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_br_inv (run_vals_inv hr)
    have e : l.toNat = (labelPred l).toNat + 1 := by simp; omega
    refine .labelBrSucc ?_
    have := run_br_at (P := P) (host := host) (s := s') (f := f') us l rest
    rw [e] at this
    simpa using this
  | @brHandler => intro hF; frag_contra hF
  | @brIfTrue s f k l hk =>
    intro hF
    refine ⟨fun a ha => by simp at ha; subst ha; exact .plain (.br l), ?_⟩
    intro ws s' f' o hr
    refine .val (v := .i32 k) rfl (.brIf ?_)
    split
    · rename_i h0; exact absurd h0 hk
    · simpa using hr
  | @brIfFalse s f l =>
    intro hF
    refine ⟨fun a ha => by simp at ha, ?_⟩
    intro ws s' f' o hr
    exact .val (v := .i32 0) rfl (.brIf (by simpa using hr))
  | @returnLabel s f n cont us rest =>
    intro hF
    refine ⟨frag_append.2 ⟨frag_vals _, fun a ha => by
      simp at ha; subst ha; exact .plain .return_⟩, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_ret_inv (run_vals_inv hr)
    refine .labelRet ?_
    simpa using run_ret_at (P := P) (host := host) (s := s') (f := f') us rest
  | @trapLabel s f n cont =>
    intro hF
    refine ⟨fun a ha => by simp at ha; subst ha; exact .trap, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_trap_inv hr
    exact .labelTrap .trap
  | @trapInstrs s f vs' rest _ =>
    intro hF
    refine ⟨fun a ha => by simp at ha; subst ha; exact .trap, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_trap_inv hr
    rw [List.append_assoc]
    exact run_vals (by simpa using (Run.trap (P := P) (host := host)))
  | returnCallRefLabel hc =>
    intro hF
    obtain ⟨-, hi⟩ := fragA_label (frag_single hF)
    exact (fragA_retCallRef (hi _ (by simp)) hc).elim
  | throwRefLabel =>
    intro hF
    obtain ⟨-, hi⟩ := fragA_label (frag_single hF)
    exact (fragA_throwRef (hi (.plain .throwRef) (by simp [throwing]))).elim
  | @callRefNull _ _ c hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @callRefFunc _ _ c _ _ _ _ _ _ hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @callRefHost _ _ _ c _ _ _ _ _ _ _ hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @callRefHostDiv _ _ c _ _ _ _ _ _ hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @brOnNullAddr _ _ v l _ =>
    intro hF
    have := hF (.plain (.brOnNull l)) (by simp)
    cases this with
    | val h => simp [Admin.val?] at h
    | plain h => cases h <;> simp_all [Det.famOf, Admin.val?]
  | @brOnNonNullAddr _ _ v l _ =>
    intro hF
    have := hF (.plain (.brOnNonNull l)) (by simp)
    cases this with
    | val h => simp [Admin.val?] at h
    | plain h => cases h <;> simp_all [Det.famOf, Admin.val?]
  | _ => intro hF; frag_contra hF

/-! ## Completeness and adequacy -/

theorem run_of_ends {s : Store H} {f : Frame} {c : List Admin} {o : Out} (he : o.Ends c) :
    Run P host s f [] c s f o := by
  cases o with
  | normal vs => rw [show c = vals vs from he]; exact run_vals_normal vs
  | br l vs =>
    obtain ⟨x, rest, rfl, rfl⟩ := he
    exact run_br_at vs x rest
  | ret vs =>
    obtain ⟨rest, rfl⟩ := he
    exact run_ret_at vs rest
  | trap => rw [show c = [.trap] from he]; exact .trap

theorem complete {s s' : Store H} {f f' : Frame} {code c' : List Admin} {o : Out}
    (hF : Frag code) (h : Steps P host ⟨s, f, code⟩ ⟨s', f', c'⟩) (he : o.Ends c') :
    Run P host s f [] code s' f' o := by
  generalize hc : (⟨s, f, code⟩ : Config H) = c at h
  induction h using Relation.ReflTransGen.head_induction_on generalizing s f code with
  | refl => cases hc; exact run_of_ends he
  | head hab _ ih =>
    subst hc
    rename_i b _
    obtain ⟨hF', hb⟩ := expand hab hF
    rcases b with ⟨sb, fb, cb⟩
    exact hb (ih hF' rfl)

theorem adequate {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Out}
    (hF : Frag code) :
    Run P host s f vs code s' f' o ↔
      ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' := by
  refine ⟨sound, fun ⟨c', hs, he⟩ => ?_⟩
  exact run_vals_inv (vs := []) (by simpa using complete (frag_append.2 ⟨frag_vals vs, hF⟩) hs he)

/-! ## Frames -/

theorem steps_frame {s s' : Store H} {f fi fi' : Frame} {X Y : List Admin} (n : Nat)
    (h : Steps P host ⟨s, fi, X⟩ ⟨s', fi', Y⟩) :
    Steps P host ⟨s, f, [.frame n fi X]⟩ ⟨s', f, [.frame n fi' Y]⟩ :=
  Relation.ReflTransGen.lift (p := Step P host)
    (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtFrame st) _ _ h

/-- A result does not step, so a run from it stays. -/
theorem steps_result {s s' : Store H} {f f' : Frame} {r : Result} {c' : List Admin}
    (h : Steps P host ⟨s, f, r.toAdmin⟩ ⟨s', f', c'⟩) : s' = s ∧ f' = f ∧ c' = r.toAdmin := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | head hab _ => exact (Step.result_stuck r hab).elim

theorem frame_sound {s s' : Store H} {f fi fi' : Frame} {n : Nat} {inner c' : List Admin}
    {o : Out} (h : Run P host s fi [] inner s' fi' o) (ho : FrameOut n o c') :
    Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s', f, c'⟩ := by
  obtain ⟨c₁, hs, he⟩ := sound h
  have h1 := steps_frame (f := f) n (by simpa [vals] using hs)
  cases o with
  | normal us =>
    obtain ⟨hn, rfl⟩ := ho
    simp only [Out.Ends] at he; subst he
    exact h1.tail (Step.frameVals hn)
  | ret us =>
    obtain ⟨us₁, ws, rfl, hn, rfl⟩ := ho
    obtain ⟨rest, rfl⟩ := he
    refine h1.tail ?_
    have := Step.frameVals (P := P) (host := host) (s := s') (f := f) (fi := fi') hn
    have := Step.returnFrame (P := P) (host := host) (s := s') (f := f) (fi := fi') (vs' := us₁)
      (vs := ws) (rest := rest) hn
    simpa using this
  | trap =>
    simp only [FrameOut] at ho; subst ho
    simp only [Out.Ends] at he; subst he
    exact h1.tail Step.trapFrame
  | br => exact ho.elim

theorem frame_complete {s s' : Store H} {f f' fi : Frame} {n : Nat} {inner c' : List Admin}
    (hF : Frag inner) (h : Steps P host ⟨s, f, [.frame n fi inner]⟩ ⟨s', f', c'⟩)
    (hc : ∃ r : Result, c' = r.toAdmin) :
    f' = f ∧ ∃ fi' o, Run P host s fi [] inner s' fi' o ∧ FrameOut n o c' := by
  obtain ⟨r, rfl⟩ := hc
  generalize hx : (⟨s, f, [.frame n fi inner]⟩ : Config H) = x at h
  induction h using Relation.ReflTransGen.head_induction_on generalizing s fi inner with
  | refl =>
    simp only [Config.mk.injEq] at hx
    obtain ⟨-, -, hx⟩ := hx
    exfalso
    rcases r with vs | a | _ <;> simp [Result.toAdmin, throwing] at hx
    exact SingleThreaded.Det.mem_vals (a := .frame n fi inner) (by rw [← hx]; simp) rfl
  | head hab hrest ih =>
    subst hx
    rcases Step.frame_inv hab with ⟨s₁, fi₁, inner₁, hs, rfl⟩ | ⟨out, hx, rfl⟩
    · obtain ⟨hF', hb⟩ := Proofs.Region.expand hs hF
      obtain ⟨rfl, fi', o, hr, ho⟩ := ih hF' rfl
      exact ⟨rfl, fi', o, hb hr, ho⟩
    · cases hx with
      | @vals vs hn =>
        have := steps_result (r := .values vs) (by simpa [Result.toAdmin] using hrest)
        obtain ⟨rfl, rfl, hc⟩ := this
        exact ⟨rfl, fi, .normal vs, run_vals_normal vs, hn, by simpa [Result.toAdmin] using hc⟩
      | @ret vs' vs rest hn =>
        have := steps_result (r := .values vs) (by simpa [Result.toAdmin] using hrest)
        obtain ⟨rfl, rfl, hc⟩ := this
        refine ⟨rfl, fi, .ret (vs' ++ vs), ?_, vs', vs, rfl, hn, by simpa [Result.toAdmin] using hc⟩
        simpa using run_ret_at (P := P) (host := host) (s := s') (f := fi) (vs' ++ vs) rest
      | trap =>
        have := steps_result (r := .trap) (by simpa [Result.toAdmin] using hrest)
        obtain ⟨rfl, rfl, hc⟩ := this
        exact ⟨rfl, fi, .trap, .trap, by simpa [Result.toAdmin, FrameOut] using hc⟩
      | throw a => exact (fragA_throwRef (hF (.plain .throwRef) (by simp [throwing]))).elim
      | @returnCallNull vs c rest hc =>
        exact (fragA_retCallRef (hF c (by simp)) hc).elim
      | @returnCallAddr vs' vs a c rest fn ps rs hc =>
        exact (fragA_retCallRef (hF c (by simp)) hc).elim

end Silmaril.Wasm.Cfg.Proofs.Region
