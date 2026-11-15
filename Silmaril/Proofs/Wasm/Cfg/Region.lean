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

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-! ## Basic facts -/

theorem famOf_val {a : Admin} {v : Val} (h : a.val? = some v) : Det.famOf a = .control := by
  by_contra hk
  have := Proofs.Exec.val_none_of_noncontrol hk
  simp [h] at this

theorem isRetCallRef_val {c : Admin} (hc : c.IsReturnCallRef) : c.val? = none := by
  unfold Admin.IsReturnCallRef at hc
  split at hc <;> first | rfl | exact hc.elim

theorem isRetCallRef_plain {i : Instr} (hc : (Admin.plain i).IsReturnCallRef) :
    ∃ y, i = .returnCallRef y := by
  unfold Admin.IsReturnCallRef at hc
  split at hc <;> simp_all

/-- Values push. -/
theorem run_vals {s s' : Store H} {f f' : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin} {o : Out},
      RunC P host C s f (vs ++ ws) code s' f' o → RunC P host C s f vs (vals ws ++ code) s' f' o
  | [], _, _, h => by simpa [vals] using h
  | w :: ws, code, o, h => by
    simp only [vals, List.map_cons, List.cons_append]
    exact .val (Admin.val?_toAdmin w) (run_vals (vs := vs ++ [w]) (by simpa using h))

theorem run_val_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {v : Val}
    {code : List Admin} {o : Out} (hv : a.val? = some v)
    (h : RunC P host C s f vs (a :: code) s' f' o) : RunC P host C s f (vs ++ [v]) code s' f' o := by
  cases h with
  | returnCallRef hc => simp [isRetCallRef_val hc] at hv
  | returnCallRefNull hc => simp [isRetCallRef_val hc] at hv
  | val hv' h => rw [hv] at hv'; cases hv'; exact h
  | simple hi => exact absurd (famOf_val hv) hi
  | simpleTrap hi => exact absurd (famOf_val hv) hi
  | brData hb => cases hb <;> simp [Admin.val?] at hv
  | _ => simp [Admin.val?] at hv

theorem run_vals_inv {s s' : Store H} {f f' : Frame} {vs : List Val} :
    ∀ {ws : List Val} {code : List Admin} {o : Out},
      RunC P host C s f vs (vals ws ++ code) s' f' o → RunC P host C s f (vs ++ ws) code s' f' o
  | [], _, _, h => by simpa [vals] using h
  | w :: ws, code, o, h => by
    simp only [vals, List.map_cons, List.cons_append] at h
    have := run_vals_inv (vs := vs ++ [w]) (run_val_inv (Admin.val?_toAdmin w) h)
    simpa using this

theorem run_vals_iff {s s' : Store H} {f f' : Frame} {vs ws : List Val} {code : List Admin}
    {o : Out} :
    RunC P host C s f vs (vals ws ++ code) s' f' o ↔ RunC P host C s f (vs ++ ws) code s' f' o :=
  ⟨run_vals_inv, run_vals⟩

theorem run_nil_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {o : Out}
    (h : RunC P host C s f vs [] s' f' o) : o = .normal vs ∧ s' = s ∧ f' = f := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem run_trap_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin}
    {o : Out} (h : RunC P host C s f vs (.trap :: code) s' f' o) :
    o = .trap ∧ s' = s ∧ f' = f := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | trap => exact ⟨rfl, rfl, rfl⟩
  | val hv => simp [Admin.val?] at hv

theorem run_br_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {l : LabelIdx}
    {code : List Admin} {o : Out} (h : RunC P host C s f vs (.plain (.br l) :: code) s' f' o) :
    o = .br l.toNat vs ∧ s' = s ∧ f' = f := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | br => exact ⟨rfl, rfl, rfl⟩
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [Det.famOf] at hi
  | simpleTrap hi => simp [Det.famOf] at hi
  | brData hb => cases hb

theorem run_ret_inv {s s' : Store H} {f f' : Frame} {vs : List Val}
    {code : List Admin} {o : Out} (h : RunC P host C s f vs (.plain .return_ :: code) s' f' o) :
    o = .ret vs ∧ s' = s ∧ f' = f := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | ret => exact ⟨rfl, rfl, rfl⟩
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [Det.famOf] at hi
  | simpleTrap hi => simp [Det.famOf] at hi
  | brData hb => cases hb

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

theorem steps_throwing (s : Store H) (f : Frame) (vs : List Val) (a : Nat) (rest : List Admin) :
    Steps P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .single (Step.throwRefInstrs hne)
  · have hv : vs = [] ∧ rest = [] := by simpa only [ne_eq, not_or, Decidable.not_not] using hne
    rw [hv.1, hv.2]; simpa [vals] using .refl

theorem steps_handler {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cs : List Catch) (h : Steps P host ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    Steps P host ⟨s, f, [.handler n cs X]⟩ ⟨s', f', [.handler n cs Y]⟩ :=
  Relation.ReflTransGen.lift (p := Step P host)
    (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctxtHandler st) _ _ h

/-- The code a handler leaves for a resolved exception. -/
def catchCode (a : Nat) : Option (List Val × LabelIdx) → List Admin
  | some (us, l) => vals us ++ [.plain (.br l)]
  | none => throwing a

theorem catches_steps {s : Store H} {f : Frame} {a n : Nat} {cs : List Catch}
    {r : Option (List Val × LabelIdx)} (hc : Catches s f a cs r) :
    Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩ ⟨s, f, catchCode a r⟩ := by
  induction hc with
  | catch_ he ht => exact .single (Step.throwRefHandlerCatch he ht)
  | @catchRef x l cs e he ht =>
    have h1 : Step P host ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩ := Step.throwRefHandlerCatchRef he ht
    exact .single (by simpa [catchCode, vals, Val.toAdmin] using h1)
  | @catchAll l cs =>
    have h1 : Step P host ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩
        ⟨s, f, [.plain (.br l)]⟩ := Step.throwRefHandlerCatchAll
    exact .single (by simpa [catchCode, vals] using h1)
  | @catchAllRef l cs =>
    have h1 : Step P host ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩
        ⟨s, f, [.ref (.exn a), .plain (.br l)]⟩ := Step.throwRefHandlerCatchAllRef
    exact .single (by simpa [catchCode, vals, Val.toAdmin] using h1)
  | next h _ ih => exact .head (Step.throwRefHandlerNext h) ih
  | empty => exact .single Step.throwRefHandlerEmpty

/-! ## Soundness: a region run is a Core run -/

theorem func?_inv {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (h : s.func? f x = some (a, fi)) : f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi := by
  unfold Store.func? at h
  cases ha : f.module.funcs[x.toNat]? with
  | none => simp [ha] at h
  | some a' =>
    cases hb : s.funcs[a']? with
    | none => simp [ha, hb] at h
    | some fi' => simp [ha, hb] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, hb⟩

theorem call_head {s : Store H} {f : Frame} {ws us : List Val} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} {code : List Admin} (hfi : s.func? f x = some (a, fi)) :
    Step P host ⟨s, f, vals (ws ++ us) ++ .plain (.call x) :: code⟩
      ⟨s, f, vals ws ++ (vals us ++ [.ref (.func a), .callRefType fi.type]) ++ code⟩ := by
  obtain ⟨hx, hf⟩ := func?_inv hfi
  have := step_in (P := P) (host := host) (ws ++ us) code (Step.call (s := s) hx hf)
  simpa using this

/-- **Soundness, with calls answered by a Core-sound oracle.** -/
theorem soundC {C : Abstract.CallRel H} (hC : CallSound P host C) {s s' : Store H} {f f' : Frame}
    {vs : List Val} {code : List Admin} {o : Out} (h : RunC P host C s f vs code s' f' o) :
    ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' := by
  induction h with
  | @call s s₁ s' f f' ws us vs x a fi ps rs fl code o hfi hty hn hcall hvs _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head (call_head hfi) ?_, he⟩
    have h1 := steps_in ws code ((hC s s₁ f a fi ps rs us fl (func?_inv hfi).2 hty hn hcall).1 vs hvs)
    exact h1.trans (by simpa using hs)
  | @callTrap s s₁ f ws us x a fi ps rs code hfi hty hn hcall =>
    refine ⟨[.trap], .head (call_head hfi) ?_, rfl⟩
    have h1 := steps_in ws code ((hC s s₁ f a fi ps rs us _ (func?_inv hfi).2 hty hn hcall).2.1 rfl)
    exact h1.trans (by simpa using steps_trap (P := P) (host := host) s₁ f ws code)
  | @callThrow s s₁ f ws us x a t fi ps rs code hfi hty hn hcall =>
    refine ⟨throwing t, .head (call_head hfi) ?_, rfl⟩
    have h1 := steps_in ws code ((hC s s₁ f a fi ps rs us _ (func?_inv hfi).2 hty hn hcall).2.2 t rfl)
    exact h1.trans (steps_throwing (P := P) (host := host) s₁ f ws t code)
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
  | @brData s s' f f' ws us us' i X code o hb _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ (by simpa using hs), he⟩
    have := step_in (P := P) (host := host) ws code (BrStep.step (P := P) (host := host) hb)
    simpa using this
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
  | @throw s f ws vs x ta ti ts code ht he hn =>
    refine ⟨throwing s.exns.length, ?_, rfl⟩
    have h1 := step_in (P := P) (host := host) ws code (Step.throw (s := s) (f := f) ht he hn)
    exact (Relation.ReflTransGen.single (by simpa using h1)).trans (steps_throwing _ _ _ _ _)
  | @throwRefNull s f ws code =>
    refine ⟨[.trap], ?_, rfl⟩
    have h1 := step_in (P := P) (host := host) ws code (Step.throwRefNull (s := s) (f := f))
    have e : vals (ws ++ [Val.ref .null]) ++ Admin.plain .throwRef :: code =
        vals ws ++ [.ref .null, .plain .throwRef] ++ code := by simp [vals, Val.toAdmin]
    rw [e]
    exact (Relation.ReflTransGen.single h1).trans
      (by simpa using steps_trap (P := P) (host := host) s f ws code)
  | @throwRefExn s f ws a code =>
    refine ⟨throwing a, ?_, rfl⟩
    simpa [throwing, vals, Val.toAdmin] using steps_throwing (P := P) (host := host) s f ws a code
  | @tryTable s s' f f' ws us bt cs b t₁ t₂ code o hbt hm _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ (by simpa using hs), he⟩
    simpa using step_in (P := P) (host := host) ws code
      (Step.tryTable (s := s) (cs := cs) (body := b) hbt hm)
  | @labelThrow s s₁ f f₁ vs n cont inner code a _ ihin =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨throwing a, ?_, rfl⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.throwRefLabel (s := s₁) (f := f₁) (n := n) (cont := cont) (a := a))
    have := (h1.tail h2).trans (steps_throwing (P := P) (host := host) s₁ f₁ vs a code)
    simpa using this
  | @handlerNormal s s₁ s' f f₁ f' vs us n cs inner code o _ _ ihin ih =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    obtain ⟨c', hs, he⟩ := ih
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨c', ?_, he⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.handlerVals (s := s₁) (f := f₁) (n := n) (cs := cs) (vs := us))
    have := (h1.tail h2).trans (by simpa using hs)
    simpa using this
  | @handlerBr s s₁ f f₁ vs us n l cs inner code _ ihin =>
    obtain ⟨c₁, hs₁, x, rest, hx, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.plain (.br x)]) ++ code, ?_, x, code, hx, by simp⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.brHandler (s := s₁) (f := f₁) (n := n) (cs := cs) (vs := us) (l := x) (rest := rest))
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := h1.tail h2
    simpa using this
  | @handlerRet s s₁ f f₁ vs us n cs inner code _ ihin =>
    obtain ⟨c₁, hs₁, rest, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.plain .return_]) ++ code, ?_, code, by simp⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.returnHandler (s := s₁) (f := f₁) (n := n) (cs := cs) (vs := us) (rest := rest))
    simp only [vals_append, List.append_assoc, List.singleton_append, List.cons_append] at h1 h2
    have := h1.tail h2
    simpa using this
  | @handlerTrap s s₁ f f₁ vs n cs inner code _ ihin =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨[.trap], ?_, rfl⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.trapHandler (s := s₁) (f := f₁) (n := n) (cs := cs))
    have := (h1.tail h2).trans (by simpa using steps_trap (P := P) (host := host) s₁ f₁ vs code)
    simpa using this
  | @handlerCatch s s₁ f f₁ vs us n a l cs inner code _ hc ihin =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨vals vs ++ (vals us ++ [.plain (.br l)]) ++ code, ?_, l, code, rfl, by simp⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := steps_in vs code (catches_steps (P := P) (host := host) (n := n) hc)
    have := h1.trans h2
    simpa [catchCode] using this
  | @handlerRethrow s s₁ f f₁ vs n a cs inner code _ hc ihin =>
    obtain ⟨c₁, hs₁, he₁⟩ := ihin
    simp only [Out.Ends] at he₁; subst he₁
    refine ⟨throwing a, ?_, rfl⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := steps_in vs code (catches_steps (P := P) (host := host) (n := n) hc)
    have := (h1.trans h2).trans (steps_throwing (P := P) (host := host) s₁ f₁ vs a code)
    simpa [catchCode] using this
  | @labelTail s s₁ f f₁ vs us n cont inner code a c _ ihin =>
    obtain ⟨c₁, hs₁, hc, rest, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.ref (.func a), c]) ++ code, ?_, hc, code, by simp⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.returnCallRefLabel (s := s₁) (f := f₁) (k := n) (cont := cont) (vs := us ++ [Val.ref (.func a)]) (c := c)
        (rest := rest) hc)
    simp only [vals, List.map_append, List.map_cons, List.map_nil, Val.toAdmin, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.tail h2
  | @labelTailNull s s₁ f f₁ vs us n cont inner code c _ ihin =>
    obtain ⟨c₁, hs₁, hc, rest, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.ref .null, c]) ++ code, ?_, hc, code, by simp⟩
    have h1 := steps_in vs code (steps_label n cont hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.returnCallRefLabel (s := s₁) (f := f₁) (k := n) (cont := cont) (vs := us ++ [Val.ref .null]) (c := c)
        (rest := rest) hc)
    simp only [vals, List.map_append, List.map_cons, List.map_nil, Val.toAdmin, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.tail h2
  | @handlerTail s s₁ f f₁ vs us n cs inner code a c _ ihin =>
    obtain ⟨c₁, hs₁, hc, rest, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.ref (.func a), c]) ++ code, ?_, hc, code, by simp⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.returnCallRefHandler (s := s₁) (f := f₁) (k := n) (cs := cs) (vs := us ++ [Val.ref (.func a)]) (c := c)
        (rest := rest) hc)
    simp only [vals, List.map_append, List.map_cons, List.map_nil, Val.toAdmin, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.tail h2
  | @handlerTailNull s s₁ f f₁ vs us n cs inner code c _ ihin =>
    obtain ⟨c₁, hs₁, hc, rest, rfl⟩ := ihin
    refine ⟨vals vs ++ (vals us ++ [.ref .null, c]) ++ code, ?_, hc, code, by simp⟩
    have h1 := steps_in vs code (steps_handler n cs hs₁)
    have h2 := step_in (P := P) (host := host) vs code
      (Step.returnCallRefHandler (s := s₁) (f := f₁) (k := n) (cs := cs) (vs := us ++ [Val.ref .null]) (c := c)
        (rest := rest) hc)
    simp only [vals, List.map_append, List.map_cons, List.map_nil, Val.toAdmin, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.tail h2
  | @returnCall s f vs x a fi code hfi =>
    refine ⟨vals vs ++ [.ref (.func a), .returnCallRefType fi.type] ++ code, .single ?_, trivial, code,
      by simp⟩
    have := step_in (P := P) (host := host) vs code
      (Step.returnCall (s := s) (f := f) (func?_inv hfi).1 (func?_inv hfi).2)
    simpa using this
  | @returnCallRef s f ws a c code hc =>
    exact ⟨_, .refl, hc, code, by simp [vals, Val.toAdmin]⟩
  | @returnCallRefNull s f ws c code hc =>
    exact ⟨_, .refl, hc, code, by simp [vals, Val.toAdmin]⟩
  | @returnCallIndirect s s' f f' vs x y code o _ ih =>
    obtain ⟨c', hs, he⟩ := ih
    refine ⟨c', .head ?_ hs, he⟩
    have := step_in (P := P) (host := host) vs code
      (Step.returnCallIndirect (s := s) (f := f) (x := x) (y := y))
    simpa using this

theorem noCall_sound : CallSound P host (noCall (H := H)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim

theorem sound {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Out}
    (h : Run P host s f vs code s' f' o) :
    ∃ c', Steps P host ⟨s, f, vals vs ++ code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' :=
  soundC noCall_sound h

/-! ## Sequencing -/

theorem run_append {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {A B : List Admin}
    {o₁ o : Out} (h : RunC P host C s f vs A s₁ f₁ o₁) (hB : ThenC P host C s₁ f₁ o₁ B s' f' o) :
    RunC P host C s f vs (A ++ B) s' f' o := by
  induction h with
  | call hfi hty hn hcall hvs _ ih => exact .call hfi hty hn hcall hvs (ih hB)
  | callTrap hfi hty hn hcall => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .callTrap hfi hty hn hcall
  | callThrow hfi hty hn hcall => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .callThrow hfi hty hn hcall
  | nil => exact hB
  | val hv _ ih => exact .val hv (ih hB)
  | simple hi h₁ _ ih => exact .simple hi h₁ (ih hB)
  | simpleTrap hi h₁ => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .simpleTrap hi h₁
  | trap => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .trap
  | br => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .br
  | ret => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .ret
  | brIf _ ih => exact .brIf (by simpa using ih hB)
  | brData hb _ ih => exact .brData hb (by simpa using ih hB)
  | block hbt hm _ ih => exact .block hbt hm (ih hB)
  | loop hbt hm _ ih => exact .loop hbt hm (ih hB)
  | if_ _ ih => exact .if_ (ih hB)
  | labelNormal hin _ _ ih => exact .labelNormal hin (ih hB)
  | labelBr0 hin hn _ _ ih => exact .labelBr0 hin hn (by simpa using ih hB)
  | labelBrSucc hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelBrSucc hin
  | labelRet hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelRet hin
  | labelTrap hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelTrap hin
  | throw ht he hn => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .throw ht he hn
  | throwRefNull => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .throwRefNull
  | throwRefExn => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .throwRefExn
  | tryTable hbt hm _ ih => exact .tryTable hbt hm (ih hB)
  | labelThrow hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelThrow hin
  | handlerNormal hin _ _ ih => exact .handlerNormal hin (ih hB)
  | handlerBr hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerBr hin
  | handlerRet hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerRet hin
  | handlerTrap hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerTrap hin
  | handlerCatch hin hc => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerCatch hin hc
  | handlerRethrow hin hc => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerRethrow hin hc
  | returnCall hfi => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .returnCall hfi
  | returnCallRef hc => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .returnCallRef hc
  | returnCallRefNull hc => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .returnCallRefNull hc
  | returnCallIndirect _ ih => exact .returnCallIndirect (ih hB)
  | labelTail hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelTail hin
  | labelTailNull hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .labelTailNull hin
  | handlerTail hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerTail hin
  | handlerTailNull hin => obtain ⟨rfl, rfl, rfl⟩ := hB; exact .handlerTailNull hin

theorem run_split {s s' : Store H} {f f' : Frame} {vs : List Val} {code : List Admin} {o : Out}
    (h : RunC P host C s f vs code s' f' o) :
    ∀ {A B : List Admin}, code = A ++ B →
      ∃ s₁ f₁ o₁, RunC P host C s f vs A s₁ f₁ o₁ ∧ ThenC P host C s₁ f₁ o₁ B s' f' o := by
  induction h with
  | call hfi hty hn hcall hvs h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .call hfi hty hn hcall hvs h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁', h₂⟩ := ih rfl
      exact ⟨_, _, _, .call hfi hty hn hcall hvs h₁', h₂⟩
  | callTrap hfi hty hn hcall =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .callTrap hfi hty hn hcall⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .callTrap hfi hty hn hcall, rfl, rfl, rfl⟩
  | callThrow hfi hty hn hcall =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .callThrow hfi hty hn hcall⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .callThrow hfi hty hn hcall, rfl, rfl, rfl⟩
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
  | @brData _ _ _ _ _ _ _ _ X _ _ hb h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .brData hb h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := X ++ A) (B := B) (List.append_assoc _ _ _).symm
      exact ⟨_, _, _, .brData hb h₁, h₂⟩
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
  | throw ht he hn =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .throw ht he hn⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .throw ht he hn, rfl, rfl, rfl⟩
  | throwRefNull =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .throwRefNull⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .throwRefNull, rfl, rfl, rfl⟩
  | throwRefExn =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .throwRefExn⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .throwRefExn, rfl, rfl, rfl⟩
  | labelThrow hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelThrow hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .labelThrow hin, rfl, rfl, rfl⟩
  | handlerBr hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerBr hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerBr hin, rfl, rfl, rfl⟩
  | handlerRet hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerRet hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerRet hin, rfl, rfl, rfl⟩
  | handlerTrap hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerTrap hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerTrap hin, rfl, rfl, rfl⟩
  | handlerCatch hin hc =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerCatch hin hc⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerCatch hin hc, rfl, rfl, rfl⟩
  | handlerRethrow hin hc =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerRethrow hin hc⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerRethrow hin hc, rfl, rfl, rfl⟩
  | tryTable hbt hm h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .tryTable hbt hm h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := _ :: A) rfl
      exact ⟨_, _, _, .tryTable hbt hm h₁, h₂⟩
  | handlerNormal hin h _ ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerNormal hin h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih rfl
      exact ⟨_, _, _, .handlerNormal hin h₁, h₂⟩
  | returnCall hfi =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .returnCall hfi⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .returnCall hfi, rfl, rfl, rfl⟩
  | returnCallRef hc =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .returnCallRef hc⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .returnCallRef hc, rfl, rfl, rfl⟩
  | returnCallRefNull hc =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .returnCallRefNull hc⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .returnCallRefNull hc, rfl, rfl, rfl⟩
  | labelTail hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelTail hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .labelTail hin, rfl, rfl, rfl⟩
  | labelTailNull hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .labelTailNull hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .labelTailNull hin, rfl, rfl, rfl⟩
  | handlerTail hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerTail hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerTail hin, rfl, rfl, rfl⟩
  | handlerTailNull hin =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .handlerTailNull hin⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      exact ⟨_, _, _, .handlerTailNull hin, rfl, rfl, rfl⟩
  | returnCallIndirect h ih =>
    intro A B hA
    rcases A with _ | ⟨a, A⟩
    · subst hA; exact ⟨_, _, _, .nil, .returnCallIndirect h⟩
    · simp only [List.cons_append, List.cons.injEq] at hA
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨_, _, _, h₁, h₂⟩ := ih (A := _ :: _ :: _ :: A) rfl
      exact ⟨_, _, _, .returnCallIndirect h₁, h₂⟩

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
  | brData h => simp [Instr.IsBrData] at h
  | block h => exact h

theorem fragI_loop {bt : BlockType} {b : List Instr} (h : FragI (.loop bt b)) :
    ∀ i ∈ b, FragI i := by
  cases h with
  | simple h => simp [Det.famOf] at h
  | const h => simp [Admin.val?] at h
  | brData h => simp [Instr.IsBrData] at h
  | loop h => exact h

theorem fragI_if {bt : BlockType} {t e : List Instr} (h : FragI (.if_ bt t e)) :
    (∀ i ∈ t, FragI i) ∧ ∀ i ∈ e, FragI i := by
  cases h with
  | simple h => simp [Det.famOf] at h
  | const h => simp [Admin.val?] at h
  | brData h => simp [Instr.IsBrData] at h
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
    | brData h => rename_i i; cases i <;> simp_all [Instr.IsBrData, Admin.IsCallRef]
    | _ => simp [Admin.IsCallRef] at hc
  | trap => simp [Admin.IsCallRef] at hc
  | label => simp [Admin.IsCallRef] at hc
  | handler => simp [Admin.IsCallRef] at hc

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
    | brData h => simp [Instr.IsBrData] at h
  | trap => simp [Admin.IsReturnCallRef] at hc
  | label => simp [Admin.IsReturnCallRef] at hc
  | handler => simp [Admin.IsReturnCallRef] at hc

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
  cases_type* FragA FragI <;> simp_all [Det.famOf, Admin.val?, Instr.IsBrData]))

/-! ## Straight-line code -/

theorem run_simple_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {i : Instr}
    {code : List Admin} {o : Out} (hi : Det.famOf (.plain i) ≠ .control)
    (h : Run P host s f vs (.plain i :: code) s' f' o) :
    (∃ s₁ f₁ vs₁, Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩ ∧
        Run P host s₁ f₁ vs₁ code s' f' o) ∨
      (o = .trap ∧ Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s', f', [.trap]⟩) := by
  cases h with
  | returnCallRef hc => obtain ⟨y, rfl⟩ := isRetCallRef_plain hc; simp [Det.famOf] at hi
  | returnCallRefNull hc => obtain ⟨y, rfl⟩ := isRetCallRef_plain hc; simp [Det.famOf] at hi
  | val hv => exact absurd (Proofs.Exec.val_none_of_noncontrol hi) (by simp [hv])
  | simple _ h₁ h => exact .inl ⟨_, _, _, h₁, h⟩
  | simpleTrap _ h₁ => exact .inr ⟨rfl, h₁⟩
  | brData hb => cases hb <;> simp [Det.famOf] at hi
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
    RunC P host C s f [] (vals us ++ .plain (.br l) :: rest) s f (.br l.toNat us) :=
  run_vals (by simpa using (RunC.br (P := P) (host := host) (s := s) (f := f) (vs := us) (l := l)
    (code := rest)))

theorem run_ret_at {s : Store H} {f : Frame} (us : List Val) (rest : List Admin) :
    RunC P host C s f [] (vals us ++ .plain .return_ :: rest) s f (.ret us) :=
  run_vals (by simpa using (RunC.ret (P := P) (host := host) (s := s) (f := f) (vs := us)
    (code := rest)))

theorem run_vals_normal {s : Store H} {f : Frame} (us : List Val) :
    RunC P host C s f [] (vals us) s f (.normal us) := by
  have := run_vals (P := P) (host := host) (C := C) (s := s) (f := f) (vs := []) (ws := us)
    (code := []) (by simpa using (RunC.nil (P := P) (host := host) (C := C) (s := s) (f := f)
      (vs := us)))
  simpa using this

theorem expand_br {s : Store H} {f : Frame} {us us' : List Val} {i : Instr} {X : List Admin}
    (hb : BrStep s f us i us' X) :
    Frag (vals us' ++ X) ∧ ∀ {vs : List Val} {s' : Store H} {f' : Frame} {o : Out},
      RunC P host C s f vs (vals us' ++ X) s' f' o →
        RunC P host C s f vs (vals us ++ [.plain i]) s' f' o := by
  refine ⟨frag_append.2 ⟨frag_vals _, ?_⟩, ?_⟩
  · cases hb <;> intro a ha <;> simp at ha <;> subst ha <;> exact .plain (.br _)
  · intro vs s' f' o hr
    apply run_vals
    exact .brData (ws := vs) (code := []) hb (by simpa using run_vals_inv hr)

/-- Rebuild a label run from a run of its body's successor. -/
theorem label_back {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {n : Nat}
    {cont : List Instr} {inner inner' code : List Admin} {o : Out}
    (hb : ∀ {o₁ : Out} {s₂ : Store H} {f₂ : Frame},
      RunC P host C s₁ f₁ [] inner' s₂ f₂ o₁ → RunC P host C s f [] inner s₂ f₂ o₁)
    (h : RunC P host C s₁ f₁ vs (.label n cont inner' :: code) s' f' o) :
    RunC P host C s f vs (.label n cont inner :: code) s' f' o := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | labelNormal hin h => exact .labelNormal (hb hin) h
  | labelBr0 hin hn h => exact .labelBr0 (hb hin) hn h
  | labelBrSucc hin => exact .labelBrSucc (hb hin)
  | labelRet hin => exact .labelRet (hb hin)
  | labelTrap hin => exact .labelTrap (hb hin)
  | labelThrow hin => exact .labelThrow (hb hin)
  | labelTail hin => exact .labelTail (hb hin)
  | labelTailNull hin => exact .labelTailNull (hb hin)

theorem fragA_handler {n : Nat} {cs : List Catch} {inner : List Admin}
    (h : FragA (.handler n cs inner)) : Frag inner := by
  cases h with
  | val h => simp [Admin.val?] at h
  | handler hi => exact hi

theorem run_throwing_at {s : Store H} {f : Frame} (vs : List Val) (a : Nat) (rest : List Admin) :
    RunC P host C s f vs (throwing a ++ rest) s f (.throw a) :=
  .val (v := .ref (.exn a)) rfl (RunC.throwRefExn (ws := vs))

theorem run_throwing_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Nat}
    {rest : List Admin} {o : Out} (h : RunC P host C s f vs (throwing a ++ rest) s' f' o) :
    o = .throw a ∧ s' = s ∧ f' = f := by
  have h' := run_val_inv (v := .ref (.exn a)) rfl h
  generalize hst : vs ++ [Val.ref (.exn a)] = st at h'
  cases h' with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | simple hi => simp [Det.famOf] at hi
  | simpleTrap hi => simp [Det.famOf] at hi
  | brData hb => cases hb
  | throwRefNull =>
    have := congrArg List.getLast? hst; simp at this
  | throwRefExn =>
    have := congrArg List.getLast? hst; simp at this; subst this; exact ⟨rfl, rfl, rfl⟩

/-- Rebuild a handler run from a run of its body's successor. -/
theorem handler_back {s s₁ s' : Store H} {f f₁ f' : Frame} {vs : List Val} {n : Nat}
    {cs : List Catch} {inner inner' code : List Admin} {o : Out}
    (hb : ∀ {o₁ : Out} {s₂ : Store H} {f₂ : Frame},
      RunC P host C s₁ f₁ [] inner' s₂ f₂ o₁ → RunC P host C s f [] inner s₂ f₂ o₁)
    (h : RunC P host C s₁ f₁ vs (.handler n cs inner' :: code) s' f' o) :
    RunC P host C s f vs (.handler n cs inner :: code) s' f' o := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | handlerNormal hin h => exact .handlerNormal (hb hin) h
  | handlerBr hin => exact .handlerBr (hb hin)
  | handlerRet hin => exact .handlerRet (hb hin)
  | handlerTrap hin => exact .handlerTrap (hb hin)
  | handlerCatch hin hc => exact .handlerCatch (hb hin) hc
  | handlerRethrow hin hc => exact .handlerRethrow (hb hin) hc
  | handlerTail hin => exact .handlerTail (hb hin)
  | handlerTailNull hin => exact .handlerTailNull (hb hin)

/-- A handler around a thrown exception resolves it by `Catches`. -/
theorem handler_throwing_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {n a : Nat}
    {cs : List Catch} {code : List Admin} {o : Out}
    (h : RunC P host C s f vs (.handler n cs (throwing a) :: code) s' f' o) :
    s' = s ∧ f' = f ∧ ((∃ us l, Catches s f a cs (some (us, l)) ∧ o = .br l.toNat (vs ++ us)) ∨
      (Catches s f a cs none ∧ o = .throw a)) := by
  cases h with
  | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
  | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
  | val hv => simp [Admin.val?] at hv
  | handlerNormal hin => have := (run_throwing_inv (rest := []) (by simpa using hin)).1; cases this
  | handlerBr hin => have := (run_throwing_inv (rest := []) (by simpa using hin)).1; cases this
  | handlerRet hin => have := (run_throwing_inv (rest := []) (by simpa using hin)).1; cases this
  | handlerTrap hin => have := (run_throwing_inv (rest := []) (by simpa using hin)).1; cases this
  | handlerTail hin => have := (run_throwing_inv (rest := []) (by simpa using hin)).1; cases this
  | handlerTailNull hin =>
    have := (run_throwing_inv (rest := []) (by simpa using hin)).1; cases this
  | handlerCatch hin hc =>
    obtain ⟨he, rfl, rfl⟩ := run_throwing_inv (rest := []) (by simpa using hin)
    cases he
    exact ⟨rfl, rfl, .inl ⟨_, _, hc, rfl⟩⟩
  | handlerRethrow hin hc =>
    obtain ⟨he, rfl, rfl⟩ := run_throwing_inv (rest := []) (by simpa using hin)
    cases he
    exact ⟨rfl, rfl, .inr ⟨hc, rfl⟩⟩

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
    have := run_br_at (P := P) (host := host) (C := noCall) (s := s) (f := f) (vs' ++ us) l rest
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
    have := run_br_at (P := P) (host := host) (C := noCall) (s := s') (f := f') us l rest
    rw [e] at this
    simpa using this
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
    simpa using run_ret_at (P := P) (host := host) (C := noCall) (s := s') (f := f') us rest
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
    exact run_vals (by simpa using (RunC.trap (P := P) (host := host)))
  | returnCallRefLabel hc =>
    intro hF
    obtain ⟨-, hi⟩ := fragA_label (frag_single hF)
    exact (fragA_retCallRef (hi _ (by simp)) hc).elim
  | throwRefLabel =>
    intro hF
    refine ⟨fun x hx => by
      simp [throwing] at hx; rcases hx with rfl | rfl
      · exact .val (by simp)
      · exact .plain .throwRef, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_throwing_inv (rest := []) (by simpa using hr)
    exact .labelThrow (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ [])
  | @throw s f x vs ta ti ts ht he hn =>
    intro hF
    refine ⟨fun x hx => by
      simp [throwing] at hx; rcases hx with rfl | rfl
      · exact .val (by simp)
      · exact .plain .throwRef, ?_⟩
    intro ws s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_throwing_inv (rest := []) (by simpa using hr)
    exact run_vals (.throw (code := []) ht he hn)
  | @throwRefNull s f =>
    intro hF
    refine ⟨fun x hx => by simp at hx; subst hx; exact .trap, ?_⟩
    intro ws s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_trap_inv hr
    exact .val (v := .ref .null) rfl (RunC.throwRefNull (ws := ws))
  | @throwRefInstrs s f vs a rest _ =>
    intro hF
    refine ⟨fun x hx => by
      simp [throwing] at hx; rcases hx with rfl | rfl
      · exact .val (by simp)
      · exact .plain .throwRef, ?_⟩
    intro ws s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_throwing_inv (rest := []) (by simpa using hr)
    rw [List.append_assoc]
    exact run_vals (run_throwing_at _ _ _)
  | @tryTable s f bt cs b vs t₁ t₂ hbt hm =>
    intro hF
    dsimp only at hF ⊢
    have hb : ∀ i ∈ b, FragI i := by
      have := fragA_plain (frag_last hF)
      cases this with
      | simple h => simp [Det.famOf] at h
      | const h => simp [Admin.val?] at h
      | brData h => simp [Instr.IsBrData] at h
      | tryTable h => exact h
    refine ⟨fun a ha => by
      simp at ha; subst ha
      exact .handler (fun x hx => by
        simp at hx; subst hx
        exact .label (by simp) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩)), ?_⟩
    intro ws s' f' o hr
    exact run_vals (.tryTable hbt hm hr)
  | ctxtHandler _ ih =>
    intro hF
    dsimp only at hF ⊢
    have hi := fragA_handler (frag_single hF)
    obtain ⟨hF', hb⟩ := ih hi
    refine ⟨fun a ha => by simp at ha; subst ha; exact .handler hF', ?_⟩
    intro vs s'' f'' o hr
    exact handler_back hb hr
  | @handlerVals s f n cs us =>
    intro hF
    refine ⟨frag_vals us, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_nil_inv (run_vals_inv (code := []) (by simpa using hr))
    exact .handlerNormal (run_vals_normal us) .nil
  | @brHandler s f n cs us l rest =>
    intro hF
    refine ⟨frag_append.2 ⟨frag_vals _, fun a ha => by
      simp at ha; subst ha; exact .plain (.br _)⟩, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_br_inv (run_vals_inv hr)
    exact .handlerBr (by simpa using run_br_at (P := P) (host := host) (C := noCall) (s := s') (f := f') us l rest)
  | @returnHandler s f n cs us rest =>
    intro hF
    refine ⟨frag_append.2 ⟨frag_vals _, fun a ha => by
      simp at ha; subst ha; exact .plain .return_⟩, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_ret_inv (run_vals_inv hr)
    exact .handlerRet (by simpa using run_ret_at (P := P) (host := host) (C := noCall) (s := s') (f := f') us rest)
  | @trapHandler s f n cs =>
    intro hF
    refine ⟨fun a ha => by simp at ha; subst ha; exact .trap, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_trap_inv hr
    exact .handlerTrap .trap
  | @throwRefHandlerEmpty s f n a =>
    intro hF
    refine ⟨fun x hx => by
      simp [throwing] at hx; rcases hx with rfl | rfl
      · exact .val (by simp)
      · exact .plain .throwRef, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_throwing_inv (rest := []) (by simpa using hr)
    exact .handlerRethrow (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ []) .empty
  | @throwRefHandlerCatch s f n x l cs a e he ht =>
    intro hF
    refine ⟨frag_append.2 ⟨frag_vals _, fun a ha => by
      simp at ha; subst ha; exact .plain (.br _)⟩, ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_br_inv (run_vals_inv hr)
    exact .handlerCatch (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ [])
      (.catch_ he ht)
  | @throwRefHandlerCatchRef s f n x l cs a e he ht =>
    intro hF
    refine ⟨frag_append.2 ⟨frag_vals _, fun x hx => by
      simp at hx; rcases hx with rfl | rfl
      · exact .val (by simp)
      · exact .plain (.br _)⟩, ?_⟩
    intro vs s' f' o hr
    have hr' : Run P host s f vs (vals (e.fields ++ [.ref (.exn a)]) ++ [.plain (.br l)]) s' f' o := by
      simpa [vals, Val.toAdmin] using hr
    obtain ⟨rfl, rfl, rfl⟩ := run_br_inv (run_vals_inv hr')
    exact .handlerCatch (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ [])
      (.catchRef he ht)
  | @throwRefHandlerCatchAll s f n l cs a =>
    intro hF
    refine ⟨fun a ha => by simp at ha; subst ha; exact .plain (.br _), ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_br_inv hr
    have := RunC.handlerCatch (P := P) (host := host) (vs := vs) (us := []) (n := n) (code := [])
      (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) (s := s') (f := f') [] a [])
      (Catches.catchAll (l := l) (cs := cs))
    simpa using this
  | @throwRefHandlerCatchAllRef s f n l cs a =>
    intro hF
    refine ⟨fun x hx => by
      simp at hx; rcases hx with rfl | rfl
      · exact .val (by simp)
      · exact .plain (.br _), ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, rfl⟩ := run_br_inv (run_val_inv (v := .ref (.exn a)) rfl hr)
    exact .handlerCatch (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ [])
      (Catches.catchAllRef (l := l) (cs := cs))
  | @throwRefHandlerNext s f n c cs a hn =>
    intro hF
    refine ⟨fun x hx => by
      simp at hx; subst hx
      exact .handler (fun y hy => by
        simp [throwing] at hy; rcases hy with rfl | rfl
        · exact .val (by simp)
        · exact .plain .throwRef), ?_⟩
    intro vs s' f' o hr
    obtain ⟨rfl, rfl, hres⟩ := handler_throwing_inv hr
    rcases hres with ⟨us, l, hc, rfl⟩ | ⟨hc, rfl⟩
    · exact .handlerCatch (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ [])
        (.next hn hc)
    · exact .handlerRethrow (by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] _ [])
        (.next hn hc)
  | returnCallRefHandler hc =>
    intro hF
    have hi := fragA_handler (frag_single hF)
    exact (fragA_retCallRef (hi _ (by simp)) hc).elim
  | @callRefNull _ _ c hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @callRefFunc _ _ c _ _ _ _ _ _ hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @callRefHost _ _ _ c _ _ _ _ _ _ _ hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @callRefHostDiv _ _ c _ _ _ _ _ _ hc => intro hF; exact (fragA_callRef (hF c (by simp)) hc).elim
  | @brTableLt s f k ls l' l hi =>
    intro _; simpa [vals, Val.toAdmin, constI32, Val.i32] using
      expand_br (P := P) (host := host) (BrStep.tableLt (s := s) (f := f) (l' := l') hi)
  | @brTableGe s f k ls l' hi =>
    intro _; simpa [vals, Val.toAdmin, constI32, Val.i32] using
      expand_br (P := P) (host := host) (BrStep.tableGe (s := s) (f := f) (l' := l') hi)
  | @brOnNullNull s f l =>
    intro _; simpa [vals, Val.toAdmin] using
      expand_br (P := P) (host := host) (BrStep.onNullNull (s := s) (f := f) (l := l))
  | @brOnNullAddr s f v l hv =>
    intro _; simpa [vals] using
      expand_br (P := P) (host := host) (BrStep.onNullAddr (s := s) (f := f) (l := l) hv)
  | @brOnNonNullNull s f l =>
    intro _; simpa [vals, Val.toAdmin] using
      expand_br (P := P) (host := host) (BrStep.onNonNullNull (s := s) (f := f) (l := l))
  | @brOnNonNullAddr s f v l hv =>
    intro _; simpa [vals] using
      expand_br (P := P) (host := host) (BrStep.onNonNullAddr (s := s) (f := f) (l := l) hv)
  | brOnCastSucceed h =>
    intro _; simpa [vals, Val.toAdmin] using expand_br (P := P) (host := host) (BrStep.onCastSucceed h)
  | brOnCastFail h =>
    intro _; simpa [vals, Val.toAdmin] using expand_br (P := P) (host := host) (BrStep.onCastFail h)
  | brOnCastFailSucceed h =>
    intro _; simpa [vals, Val.toAdmin] using
      expand_br (P := P) (host := host) (BrStep.onCastFailSucceed h)
  | brOnCastFailFail h =>
    intro _; simpa [vals, Val.toAdmin] using
      expand_br (P := P) (host := host) (BrStep.onCastFailFail h)
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
  | throw a => rw [show c = throwing a from he]; simpa using run_throwing_at (P := P) (host := host) (C := noCall) (s := s) (f := f) [] a []
  | tail vs a r =>
    obtain ⟨hr, rest, rfl⟩ := he
    exact run_vals (by simpa [vals, Val.toAdmin] using
      (RunC.val (C := noCall) (P := P) (host := host) (s := s) (f := f) (vs := vs)
        (v := .ref (.func a)) rfl (RunC.returnCallRef (code := rest) hr)))
  | tailNull vs r =>
    obtain ⟨hr, rest, rfl⟩ := he
    exact run_vals (by simpa [vals, Val.toAdmin] using
      (RunC.val (C := noCall) (P := P) (host := host) (s := s) (f := f) (vs := vs)
        (v := .ref .null) rfl (RunC.returnCallRefNull (code := rest) hr)))

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
  | throw a =>
    simp only [FrameOut] at ho; subst ho
    simp only [Out.Ends] at he; subst he
    exact h1.tail Step.throwRefFrame
  | br => exact ho.elim
  | tail => exact ho.elim
  | tailNull vs r =>
    simp only [FrameOut] at ho; subst ho
    obtain ⟨hr, rest, rfl⟩ := he
    have h2 := Step.returnCallRefFrameNull (P := P) (host := host) (s := s') (f := f) (fi := fi')
      (k := n) (vs := vs) (rest := rest) hr
    exact h1.tail (by simpa using h2)

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
        simpa using run_ret_at (P := P) (host := host) (C := noCall) (s := s') (f := fi) (vs' ++ vs) rest
      | trap =>
        have := steps_result (r := .trap) (by simpa [Result.toAdmin] using hrest)
        obtain ⟨rfl, rfl, hc⟩ := this
        exact ⟨rfl, fi, .trap, .trap, by simpa [Result.toAdmin, FrameOut] using hc⟩
      | throw a =>
        have := steps_result (r := .throw a) (by simpa [Result.toAdmin] using hrest)
        obtain ⟨rfl, rfl, hc⟩ := this
        exact ⟨rfl, fi, .throw a, by simpa using run_throwing_at (P := P) (host := host) (C := noCall) [] a [],
          by simpa [Result.toAdmin, FrameOut] using hc⟩
      | @returnCallNull vs c rest hc =>
        exact (fragA_retCallRef (hF c (by simp)) hc).elim
      | @returnCallAddr vs' vs a c rest fn ps rs hc =>
        exact (fragA_retCallRef (hF c (by simp)) hc).elim

end Silmaril.Wasm.Cfg.Proofs.Region

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem catches_total (s : Store H) (f : Frame) (a : Nat) :
    ∀ cs : List Catch, ∃ r, Catches s f a cs r
  | [] => ⟨none, .empty⟩
  | c :: cs => by
    by_cases hm : CatchMatches s f a c
    · cases c with
      | catch_ x l =>
        obtain ⟨e, ta, he, ht, rfl⟩ := hm
        exact ⟨_, .catch_ he ht⟩
      | catchRef x l =>
        obtain ⟨e, ta, he, ht, rfl⟩ := hm
        exact ⟨_, .catchRef he ht⟩
      | catchAll l => exact ⟨_, .catchAll⟩
      | catchAllRef l => exact ⟨_, .catchAllRef⟩
    · obtain ⟨r, hr⟩ := catches_total s f a cs
      exact ⟨r, .next hm hr⟩

theorem catches_unique {s : Store H} {f : Frame} {a : Nat} :
    ∀ {cs : List Catch} {r r' : Option (List Val × LabelIdx)},
      Catches s f a cs r → Catches s f a cs r' → r = r'
  | _, _, _, .empty, h' => by cases h'; rfl
  | _, _, _, .catch_ he ht, h' => by
    cases h' with
    | catch_ he' ht' => rw [he] at he'; cases he'; rfl
    | next hn _ => exact absurd ⟨_, _, he, ht, rfl⟩ hn
  | _, _, _, .catchRef he ht, h' => by
    cases h' with
    | catchRef he' ht' => rw [he] at he'; cases he'; rfl
    | next hn _ => exact absurd ⟨_, _, he, ht, rfl⟩ hn
  | _, _, _, .catchAll, h' => by
    cases h' with
    | catchAll => rfl
    | next hn _ => exact absurd trivial hn
  | _, _, _, .catchAllRef, h' => by
    cases h' with
    | catchAllRef => rfl
    | next hn _ => exact absurd trivial hn
  | _, _, _, .next hn hr, h' => by
    cases h' with
    | catch_ he ht => exact absurd ⟨_, _, he, ht, rfl⟩ hn
    | catchRef he ht => exact absurd ⟨_, _, he, ht, rfl⟩ hn
    | catchAll => exact absurd trivial hn
    | catchAllRef => exact absurd trivial hn
    | next _ hr' => exact catches_unique hr hr'

end Silmaril.Wasm.Cfg.Proofs.Region
