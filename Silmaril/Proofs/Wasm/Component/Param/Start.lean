module

public import Silmaril.Wasm.Component.Param.Start.Defs
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Handler.Thms

/-!
# The engine semantics with a start phase: proofs

* `instOf_eq`: `instOf` is `instOfS` on instances without a start function, and `none` on the
  others.
* `engineStrategyS_of_start_none`: without a start function, `engineStrategyS` is
  `engineStrategy` (two simulations: the `ready` states are `engineStrategy`'s states).
* `engineStrategyS_start_mem`: a start phase whose import calls are `w` and which returns at
  `s'` puts `w` between the first question and the moves `engineStrategy` makes from `s'`.
* `engineStrategyS_start_prefix`, `engineStrategyS_start_call`, `engineStrategyS_start_trap`:
  the start phase's import calls and traps are plays.
* `engineStrategyS_eq_trapAll`: a start function that can only trap gives `trapAll` (two
  simulations against the transition system of `trapAll`'s handler).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)

variable {E : Engine}

/-! ## Instances -/

theorem instOf_eq (E : Engine) (m : E.Module) (imps exps : CoreIface) :
    instOf E m imps exps = (instOfS E m imps exps).bind fun I =>
      match I.start with
      | none => some I.toE
      | some _ => none := by
  unfold instOf instOfS
  generalize allocHosts E (E.empty Nat) 0 imps = p
  obtain ⟨s, as⟩ := p
  dsimp only
  generalize E.prepare? s m (as.map E.ofFunc) = r
  rcases r with _ | ⟨s', inst, _ | st⟩
  · rfl
  · dsimp only
    cases exportAddrs E inst exps <;> rfl
  · dsimp only
    cases exportAddrs E inst exps <;> rfl

/-! ## Without a start function -/

/-- The `ready` states simulate `engineStrategy`. -/
def simReady (I : EInstance E) (st : SInstance E) (imps exps : CoreIface)
    (hst : (st.init : SState E imps.length exps.length) = .ready (.idle I.store))
    (haddrs : st.addrs = I.addrs) :
    (engineLTS E I imps exps).Simulation (engineLTSS E st imps exps) where
  R x y := y = .ready x
  init := hst
  step := by
    rintro x x' y l rfl ⟨m, rfl, h⟩
    exact ⟨.ready x', LTS.Run.of_step (L := engineLTSS E st imps exps)
      (show STrans E st.addrs imps exps _ _ _ from .lift (haddrs ▸ h)), rfl⟩

/-- `engineStrategy` simulates the `ready` states. -/
def simReady' (I : EInstance E) (st : SInstance E) (imps exps : CoreIface)
    (hst : (st.init : SState E imps.length exps.length) = .ready (.idle I.store))
    (haddrs : st.addrs = I.addrs) :
    (engineLTSS E st imps exps).Simulation (engineLTS E I imps exps) where
  R y x := y = .ready x
  init := hst
  step := by
    rintro y y' x l rfl h
    change STrans E st.addrs imps exps _ _ _ at h
    cases h with
    | lift h => exact ⟨_, LTS.Run.of_step (L := engineLTS E I imps exps) ⟨_, rfl, haddrs ▸ h⟩, rfl⟩

theorem engineStrategyS_of_start_none (I : SInstance E) (h : I.start = none)
    (imps exps : CoreIface) :
    engineStrategyS E I imps exps = engineStrategy E I.toE imps exps := by
  have hst : (I.init : SState E imps.length exps.length) = .ready (.idle I.toE.store) := by
    simp [SInstance.init, h, SInstance.toE]
  exact le_antisymm (simReady' I.toE I imps exps hst rfl).ofLTS_le
    (simReady I.toE I imps exps hst rfl).ofLTS_le

theorem engineSemS_sem_of_noStart (M : Type) [CoreModule M] (emb : M → E.Module) (m : M)
    (h : ∀ I, instOfS E (emb m) (CoreModule.imports m) (CoreModule.exports m) = some I →
      I.start = none) :
    (engineSemS E M emb).sem m = (engineSem E M emb).sem m := by
  simp only [engineSemS, engineSem, instOf_eq]
  rcases hI : instOfS E (emb m) (CoreModule.imports m) (CoreModule.exports m) with _ | I
  · rfl
  · have hs := h I hI
    simp only [Option.bind_some, hs]
    exact engineStrategyS_of_start_none I hs _ _

/-! ## Runs of the start phase -/

/-- Runs of `engineStrategy` are runs of the `ready` states. -/
theorem run_ready {I : SInstance E} {J : EInstance E} (hJ : J.addrs = I.addrs)
    {imps exps : CoreIface} {x y : (engineLTS E J imps exps).State}
    {p : List (Move (sigN imps.length) (sigN exps.length))}
    (h : (engineLTS E J imps exps).Run x p y) :
    (engineLTSS E I imps exps).Run (.ready x) p (.ready y) := by
  induction h with
  | nil => exact .nil _
  | tau h _ _ => obtain ⟨_, h, -⟩ := h; cases h
  | vis h _ ih =>
    obtain ⟨m, hm, h⟩ := h
    cases hm
    exact .vis (show STrans E I.addrs imps exps _ _ _ from .lift (hJ ▸ h)) ih

/-- `engineStrategy` has no silent step. -/
theorem run_nil_engine {J : EInstance E} {imps exps : CoreIface}
    {x y : (engineLTS E J imps exps).State} {p : List (Move (sigN imps.length) (sigN exps.length))}
    (h : (engineLTS E J imps exps).Run x p y) (hp : p = []) : x = y := by
  induction h with
  | nil => rfl
  | tau h _ _ => obtain ⟨_, h, -⟩ := h; cases h
  | vis _ _ _ => cases hp

/-- A start run is a run of the `starting` states, up to its last internal run. -/
theorem run_starting {I : SInstance E} {imps exps : CoreIface} (q : (sigN exps.length).Op)
    {c c' : E.Config Nat} {w : List (Move (sigN imps.length) (sigN exps.length))}
    (h : StartRun E imps c w c') :
    ∃ c₀ : E.Config Nat, (engineLTSS E I imps exps).Run (.starting q c.1 c.2) w
      (.starting q c₀.1 c₀.2) ∧ Steps E c₀ c' := by
  induction h with
  | @nil c c' run => exact ⟨c, .nil _, run⟩
  | call run callout hh r _ ih =>
    obtain ⟨c₀, hr, hs⟩ := ih
    exact ⟨c₀, .vis (show STrans E I.addrs imps exps _ _ _ from .scall run callout hh)
      (.vis (show STrans E I.addrs imps exps _ _ _ from .sret r) hr), hs⟩

/-- The moves of a start run keep the question `q` running. -/
theorem path_startRun {imps : CoreIface} {k : Nat} {q : (sigN k).Op} {c c' : E.Config Nat}
    {w : List (Move (sigN imps.length) (sigN k))} (h : StartRun E imps c w c') :
    Path (.run q) w (.run q) := by
  induction h with
  | nil => exact .nil _
  | call _ _ _ _ _ ih => exact .cons (.call _ _) (.cons (.reply _ _ _) ih)

/-- The first question of a play of `engineStrategy` leads to `dispatch`. -/
theorem run_idle_ask {I : EInstance E} {imps exps : CoreIface} {s : E.Store Nat}
    {q : (sigN exps.length).Op} {p : List (Move (sigN imps.length) (sigN exps.length))}
    {y : EState E imps.length exps.length}
    (h : (engineLTS E I imps exps).Run (.idle s) (.inr (.ask q) :: p) y) :
    (engineLTS E I imps exps).Run (dispatch I.addrs exps q s) p y := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  have hx : EState.idle s = x₁ := run_nil_engine h₁ rfl
  subst hx
  obtain ⟨m, hm, h₂⟩ := h₂
  cases hm
  cases h₂ with
  | call hc => simpa [dispatch, hc] using h₃
  | refuse hc => simpa [dispatch, hc] using h₃

/-- **A trace of the instance after its start phase, behind the start run.** -/
theorem traces_start {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat} (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t'))
    {ys : List Flat} (hfin : E.status s' t' = .returned (.values ys)) {q : (sigN exps.length).Op}
    {u : List (Move (sigN imps.length) (sigN exps.length))}
    (hu : .inr (.ask q) :: u ∈ (engineLTS E ⟨s', I.addrs⟩ imps exps).Traces) :
    .inr (.ask q) :: (w ++ u) ∈ (engineLTSS E I imps exps).Traces := by
  obtain ⟨y, hy⟩ := hu
  have h₁ := run_idle_ask hy
  obtain ⟨c₀, hr, hc⟩ := run_starting (I := I) (exps := exps) q hrun
  have hinit : (engineLTSS E I imps exps).init = .pending I.store (E.invoke a []) := by
    show I.init = _
    simp [SInstance.init, hs]
  refine ⟨.ready y, ?_⟩
  rw [hinit]
  refine .vis (show STrans E I.addrs imps exps _ _ _ from .first) (hr.append ?_)
  exact .tau (show STrans E I.addrs imps exps _ _ _ from .sdone hc hfin)
    (run_ready (I := I) rfl h₁)

/-- The start run after the first question is a trace. -/
theorem traces_start_prefix {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {c' : E.Config Nat} (hrun : StartRun E imps (I.store, E.invoke a []) w c')
    (q : (sigN exps.length).Op) :
    ∃ c₀ : E.Config Nat, (engineLTSS E I imps exps).Run (engineLTSS E I imps exps).init
      (.inr (.ask q) :: w) (.starting q c₀.1 c₀.2) ∧ Steps E c₀ c' := by
  obtain ⟨c₀, hr, hc⟩ := run_starting (I := I) (exps := exps) q hrun
  have hinit : (engineLTSS E I imps exps).init = .pending I.store (E.invoke a []) := by
    show I.init = _
    simp [SInstance.init, hs]
  refine ⟨c₀, ?_, hc⟩
  rw [hinit]
  exact .vis (show STrans E I.addrs imps exps _ _ _ from .first) hr

theorem engineStrategyS_start_prefix {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {c' : E.Config Nat} (hrun : StartRun E imps (I.store, E.invoke a []) w c')
    (q : (sigN exps.length).Op) :
    .inr (.ask q) :: w ∈ engineStrategyS E I imps exps := by
  obtain ⟨c₀, hr, -⟩ := traces_start_prefix hs hrun q
  exact Strategy.mem_ofLTS_of_mem_traces ⟨_, hr⟩ ⟨_, .cons (.ask q) (path_startRun hrun)⟩

theorem engineStrategyS_start_call {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t')) {h : Nat} {args : List Flat}
    (hc : E.status s' t' = .callout h args) (hh : h < imps.length) (q : (sigN exps.length).Op) :
    .inr (.ask q) :: (w ++ [.inl (.ask (⟨h, hh⟩, .flat args))]) ∈
      engineStrategyS E I imps exps := by
  obtain ⟨c₀, hr, hc₀⟩ := traces_start_prefix hs hrun q
  have hr' := hr.append (LTS.Run.of_step (L := engineLTSS E I imps exps)
    (show STrans E I.addrs imps exps _ _ _ from .scall hc₀ hc hh))
  rw [List.cons_append] at hr'
  exact Strategy.mem_ofLTS_of_mem_traces ⟨_, hr'⟩
    ⟨_, .cons (.ask q) ((path_startRun hrun).append (.single (.call q _)))⟩

theorem engineStrategyS_start_trap {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t'))
    (ht : E.status s' t' = .returned .trap) (q : (sigN exps.length).Op) :
    .inr (.ask q) :: (w ++ [.inr (.ans q none)]) ∈ engineStrategyS E I imps exps := by
  obtain ⟨c₀, hr, hc₀⟩ := traces_start_prefix hs hrun q
  have hr' := hr.append (.tau (show STrans E I.addrs imps exps _ _ _ from .strap hc₀ ht)
    (LTS.Run.of_step (L := engineLTSS E I imps exps)
      (show STrans E I.addrs imps exps _ _ _ from .fail)))
  rw [List.cons_append] at hr'
  exact Strategy.mem_ofLTS_of_mem_traces ⟨_, hr'⟩
    ⟨_, .cons (.ask q) ((path_startRun hrun).append (.single (.ret q _)))⟩

/-- The start run keeps a play legal. -/
theorem legal_start {imps : CoreIface} {k : Nat} {q : (sigN k).Op} {c c' : E.Config Nat}
    {w : List (Move (sigN imps.length) (sigN k))} (hrun : StartRun E imps c w c')
    {x : List (Move (sigN imps.length) (sigN k))} (hl : Legal (.inr (.ask q) :: x)) :
    Legal (.inr (.ask q) :: (w ++ x)) := by
  obtain ⟨y, hl⟩ := hl
  cases hl with
  | cons hst hp' =>
    cases hst
    exact ⟨y, .cons (.ask q) ((path_startRun hrun).append hp')⟩

/-- A prefix of a legal trace of `engineStrategy` after the start phase. -/
theorem start_mem_of_prefix {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t')) {ys : List Flat}
    (hfin : E.status s' t' = .returned (.values ys)) {q : (sigN exps.length).Op}
    {p u : List (Move (sigN imps.length) (sigN exps.length))}
    (hu : u ∈ (engineLTS E ⟨s', I.addrs⟩ imps exps).Traces) (hlu : Legal u)
    (hpre : .inr (.ask q) :: p <+: u) :
    .inr (.ask q) :: (w ++ p) ∈ engineStrategyS E I imps exps := by
  obtain ⟨v, rfl⟩ := hpre
  have ht := traces_start hs hrun hfin (u := p ++ v) hu
  refine (engineStrategyS E I imps exps).of_prefix
    (Strategy.mem_ofLTS_of_mem_traces ht (legal_start hrun hlu)) ⟨v, by simp⟩

/-- **The start phase, then `engineStrategy` from the store it returns at.** -/
theorem engineStrategyS_start_mem {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a) {w : List (Move (sigN imps.length) (sigN exps.length))}
    {s' : E.Store Nat} {t' : E.Thread Nat}
    (hrun : StartRun E imps (I.store, E.invoke a []) w (s', t')) {ys : List Flat}
    (hfin : E.status s' t' = .returned (.values ys)) {q : (sigN exps.length).Op}
    {p : List (Move (sigN imps.length) (sigN exps.length))}
    (hp : .inr (.ask q) :: p ∈ engineStrategy E ⟨s', I.addrs⟩ imps exps) :
    .inr (.ask q) :: (w ++ p) ∈ engineStrategyS E I imps exps := by
  obtain ⟨hl, u, hu, hpre⟩ := hp
  rcases hpre with hpre | ⟨p₀, o, hp₀, hpre, ho⟩
  · rcases hu with rfl | ⟨hu, hlu⟩
    · obtain ⟨v, hv⟩ := hpre
      simp at hv
    · exact start_mem_of_prefix hs hrun hfin hu hlu hpre
  · rcases p₀ with _ | ⟨x, p₁⟩
    · obtain ⟨rfl, rfl⟩ : .inr (.ask q) = o ∧ p = [] := by simpa using hp₀
      simpa using engineStrategyS_start_prefix hs hrun q
    · obtain ⟨rfl, rfl⟩ : .inr (.ask q) = x ∧ p = p₁ ++ [o] := by simpa using hp₀
      have hm : .inr (.ask q) :: (w ++ p₁) ∈ engineStrategyS E I imps exps := by
        rcases hu with rfl | ⟨hu, hlu⟩
        · obtain ⟨v, hv⟩ := hpre
          simp at hv
        · exact start_mem_of_prefix hs hrun hfin hu hlu hpre
      obtain ⟨y, hy⟩ := legal_start hrun hl
      have hy' : Path .idle ((.inr (.ask q) :: (w ++ p₁)) ++ [o]) y := by simpa using hy
      obtain ⟨x, hx, hxo⟩ := Path.concat_iff.1 hy'
      simpa using (engineStrategyS E I imps exps).receptive hm hx hxo ho

/-! ## A start function that can only trap -/

/-- The handler of `trapAll`. -/
abbrev trapH (n k : Nat) : Handler (sigN n) (sigN k) := fun _ => .pure none

theorem trapAll_eq (n k : Nat) : trapAll n k = Strategy.ofLTS (trapH n k).toReduction.toLTS := rfl

/-- The trapping start phase simulates `trapAll`. -/
def simTrap {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr} (hs : I.start = some a)
    (honly : ∀ s' t', Steps E (I.store, E.invoke a []) (s', t') →
      (∀ ys, E.status s' t' ≠ .returned (.values ys)) ∧ ∀ h args, E.status s' t' ≠ .callout h args) :
    (engineLTSS E I imps exps).Simulation (trapH imps.length exps.length).toReduction.toLTS where
  R x y := (x = .pending I.store (E.invoke a []) ∧ y = .idle) ∨
    (∃ q, x = .starting q I.store (E.invoke a []) ∧ y = .run q (.pure none)) ∨
    (∃ q, x = .failing q ∧ y = .run q (.pure none)) ∨ (x = .failed ∧ y = .idle)
  init := .inl ⟨by show I.init = _; simp [SInstance.init, hs], rfl⟩
  step := by
    rintro x x' y l hR h
    change STrans E I.addrs imps exps _ _ _ at h
    rcases hR with ⟨rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨q, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h with
      | @first _ _ q =>
        exact ⟨.run q (.pure none), LTS.Run.of_step (Reduction.Step.ask q),
          .inr (.inl ⟨q, rfl, rfl⟩)⟩
    · cases h with
      | scall run callout => exact absurd callout ((honly _ _ run).2 _ _)
      | sdone run final => exact absurd final ((honly _ _ run).1 _)
      | strap => exact ⟨_, .nil _, .inr (.inr (.inl ⟨q, rfl, rfl⟩))⟩
    · cases h with
      | fail =>
        exact ⟨.idle, LTS.Run.of_step (Reduction.Step.ret (show Prog.pure none = .pure none from rfl)),
          .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
    · cases h with
      | @dead q =>
        exact ⟨.run q (.pure none), LTS.Run.of_step (Reduction.Step.ask q),
          .inr (.inr (.inl ⟨q, rfl, rfl⟩))⟩

/-- `trapAll` simulates a start phase that may trap. -/
def simTrap' {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr} (hs : I.start = some a)
    {s' : E.Store Nat} {t' : E.Thread Nat} (run : Steps E (I.store, E.invoke a []) (s', t'))
    (ht : E.status s' t' = .returned .trap) :
    (trapH imps.length exps.length).toReduction.toLTS.Simulation (engineLTSS E I imps exps) where
  R y x := (y = .idle ∧ (x = .pending I.store (E.invoke a []) ∨ x = .failed)) ∨
    (∃ q, y = .run q (.pure none) ∧ x = .failing q)
  init := .inl ⟨rfl, .inl (by show I.init = _; simp [SInstance.init, hs])⟩
  step := by
    rintro y y' x l hR h
    rcases hR with ⟨rfl, rfl | rfl⟩ | ⟨q, rfl, rfl⟩
    · cases h with
      | ask q =>
        exact ⟨.failing q, .vis (show STrans E I.addrs imps exps _ _ _ from .first)
          (.tau (show STrans E I.addrs imps exps _ _ _ from .strap run ht) (.nil _)),
          .inr ⟨q, rfl, rfl⟩⟩
    · cases h with
      | ask q =>
        exact ⟨.failing q, .vis (show STrans E I.addrs imps exps _ _ _ from .dead) (.nil _),
          .inr ⟨q, rfl, rfl⟩⟩
    · cases h with
      | tau h => exact h.elim
      | call h => cases h
      | ret h =>
        cases h
        exact ⟨.failed, .vis (show STrans E I.addrs imps exps _ _ _ from .fail) (.nil _),
          .inl ⟨rfl, .inr rfl⟩⟩

/-- `trapAll`'s answer is a trap. -/
theorem trap_no_value {n k : Nat} {q : (sigN k).Op} {r : Payload}
    {x y : (trapH n k).toReduction.toLTS.State}
    {p : List (Move (sigN n) (sigN k))} (h : (trapH n k).toReduction.toLTS.Run x p y)
    (hx : x = .run q (.pure none)) (hp : p = [.inr (.ans q (some r))]) : False := by
  induction h with
  | nil => cases hp
  | tau h _ _ =>
    subst hx
    cases h with
    | tau h => exact h.elim
  | vis h _ _ =>
    subst hx
    cases hp
    cases h with
    | ret h => cases h

/-- `trapAll` answers no question with a value. -/
theorem two_some_not_mem_trapAll {n k : Nat} (q : (sigN k).Op) (r : Payload) :
    [.inr (.ask q), .inr (.ans q (some r))] ∉ trapAll n k := by
  intro h
  obtain ⟨y, h⟩ := Strategy.mem_ofHandler.mp h
  cases h with
  | tau h _ => cases h
  | vis h h' =>
    cases h
    exact trap_no_value h' rfl rfl

theorem engineStrategyS_eq_trapAll {I : SInstance E} {imps exps : CoreIface} {a : E.FuncAddr}
    (hs : I.start = some a)
    (htrap : ∃ s' t', Steps E (I.store, E.invoke a []) (s', t') ∧ E.status s' t' = .returned .trap)
    (honly : ∀ s' t', Steps E (I.store, E.invoke a []) (s', t') →
      (∀ ys, E.status s' t' ≠ .returned (.values ys)) ∧ ∀ h args, E.status s' t' ≠ .callout h args) :
    engineStrategyS E I imps exps = trapAll _ _ := by
  obtain ⟨s', t', run, ht⟩ := htrap
  rw [trapAll_eq]
  exact le_antisymm (simTrap hs honly).ofLTS_le (simTrap' hs run ht).ofLTS_le

end Silmaril.Proofs.Wasm.Component.Param
