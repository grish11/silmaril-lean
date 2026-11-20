module

public import Silmaril.Proofs.Wasm.Component.InstTests.Pos
public import Silmaril.Proofs.Wasm.Component.InstLitmus.Neg

/-!
# Component test binaries at a deterministic profile: what cannot happen

At `profile o` every litmus module is bounded by a script (`callMod_le_script`,
`trapMod_le_script`, and here `globMod_le_script`: `inst` is answered `ready`, `get()` is
answered `42`, any other export question a trap), so `startsC` and `trapLC` are bounded by
handlers (`startsC_le`, `trapLC_le`). The protocol guard keeps the plays of these handlers that
follow the instantiation protocol (`guard_plays`). Then:

* the handler of `startsC` asks, for `inst`, `f(u32 1)` and (if answered `()`) `f(u32 2)`
  (`startsCH_inst`), answers each export question without a call (`startsCH_ex`), and answers
  `get()` with `42` (`startsCH_get`);
* the handler of `trapLC` fails `inst` at once (`trapLCH_inst`).

Generic facts about handlers used here: `handler_ans_pure` (an answer to a question whose program
is `pure a` is `a`), `runs_of_instPlay` (a complete instantiation play of a handler runs its
program for `inst`), `runs_host_unique` (a program answered by a fixed host runs in one way).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstTests

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Proofs.Wasm.Component.InstLitmus
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

/-! ## Handlers -/

section Handler

variable {E F : Sig.{0}}

/-- The invariant of `handler_ans_pure`. -/
def AnsInv (H : Handler E F) (x : F.Op) (a : F.Ar x) : H.toReduction.toLTS.State → Prop
  | .idle => True
  | .run q P => q = x → HEq P (Prog.pure (E := E) a)
  | .wait q _ _ => q ≠ x

/-- **An answer to a question whose program is `pure a` is `a`**, in every run of the
handler. -/
theorem handler_ans_pure {H : Handler E F} {x : F.Op} {a : F.Ar x} (hx : H x = .pure a) :
    ∀ {s : H.toReduction.toLTS.State} {p : List (Move E F)} {y : H.toReduction.toLTS.State},
      AnsInv H x a s → H.toReduction.toLTS.Run s p y → ∀ r, .inr (.ans x r) ∈ p → r = a := by
  intro s p y hs hr
  induction hr with
  | nil => intro r hr; cases hr
  | tau hs' _ _ => cases hs' with | tau hc => exact (hc : False).elim
  | @vis s₁ s₂ _ o _ hst _ ih =>
    intro r hr
    cases hst with
    | ask q =>
      rcases List.mem_cons.1 hr with h | h
      · cases h
      · refine ih ?_ r h
        intro e
        subst e
        show HEq (H _) _
        rw [hx]
    | @call q P m k hc =>
      rcases List.mem_cons.1 hr with h | h
      · cases h
      · refine ih ?_ r h
        intro e
        subst e
        have := hs rfl
        cases hc
        cases this
    | resume q m k n =>
      rcases List.mem_cons.1 hr with h | h
      · cases h
      · exact ih (fun e => absurd e hs) r h
    | @ret q P r₀ hd =>
      rcases List.mem_cons.1 hr with h | h
      · cases h
        have := hs rfl
        cases hd
        cases this
        rfl
      · exact ih trivial r h

theorem runs_of_round {q : F.Op} {a : F.Ar q} :
    ∀ (cs : List (Σ m : E.Op, E.Ar m)) {H : Handler E F} {P : Prog E (F.Ar q)}
      {y : H.toReduction.toLTS.State},
      H.toReduction.toLTS.Run (.run q P)
        ((cs.flatMap fun c => [.inl (.ask c.1), .inl (.ans c.1 c.2)]) ++ [.inr (.ans q a)]) y →
      Prog.Runs P cs a
  | [], _, P, _, hr => by
    obtain ⟨y, hs, -⟩ := handler_run_cons hr
    cases hs with
    | ret hd => cases hd; exact .pure _
  | ⟨m, n⟩ :: cs, _, P, _, hr => by
    obtain ⟨y, hs, hr₁⟩ := handler_run_cons hr
    cases hs with
    | call hc =>
      cases hc
      obtain ⟨y', hs', hr'⟩ := handler_run_cons hr₁
      cases hs' with
      | resume _ _ _ _ => exact .call (runs_of_round cs hr')

/-- **A complete instantiation play of a handler runs its program for `inst`.** -/
theorem runs_of_instPlay {R : Type} {H : Handler E (F.withInst R)}
    {cs : List (Σ m : E.Op, E.Ar m)} {a : InstAns R}
    (h : instPlay (F := F) cs a ∈ Strategy.ofHandler H) : Prog.Runs (H none) cs a := by
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 h
  obtain ⟨q, hq, hr⟩ := handler_run_idle_cons hy
  cases hq
  exact runs_of_round cs hr

/-- **A program answered by a fixed host runs in one way.** -/
theorem runs_host_unique {A : Type} {host : (m : E.Op) → E.Ar m} {P : Prog E A}
    {cs cs' : List (Σ m : E.Op, E.Ar m)} {a a' : A} (h : Prog.Runs P cs a)
    (h' : Prog.Runs P cs' a') (hc : ∀ x ∈ cs, x.2 = host x.1) (hc' : ∀ x ∈ cs', x.2 = host x.1) :
    cs = cs' ∧ a = a' := by
  induction h generalizing cs' with
  | pure a => cases h'; exact ⟨rfl, rfl⟩
  | @call m k n cs a _ ih =>
    cases h' with
    | @call _ _ n' cs' _ h' =>
      have e₁ := hc ⟨m, n⟩ (.head _)
      have e₂ := hc' ⟨m, n'⟩ (.head _)
      simp only at e₁ e₂
      subst e₁ e₂
      obtain ⟨rfl, rfl⟩ := ih h' (fun x hx => hc x (.tail _ hx)) (fun x hx => hc' x (.tail _ hx))
      exact ⟨rfl, rfl⟩

/-- A play of the protocol guard over a handler's plays that ends with a Proponent move is a
play of the handler. -/
theorem mem_ofHandler_of_guard {R : Type} {σ : Strategy E (F.withInst R)}
    {H : Handler E (F.withInst R)} (hle : σ ≤ Strategy.ofHandler H)
    {p : List (Move E (F.withInst R))} {x : Move E (F.withInst R)} (hx : ¬ x.IsO)
    (hp : p ++ [x] ∈ instGuard σ) : p ++ [x] ∈ Strategy.ofHandler H := by
  obtain ⟨q, hq, -, h⟩ := guard_plays hle hp
  rcases h with h | ⟨q₀, x', he, h, hx'⟩
  · exact (Strategy.ofHandler H).of_prefix hq h
  · obtain ⟨-, he'⟩ := List.append_inj' he rfl
    cases he'
    exact absurd hx' hx

end Handler

/-! ## `globMod` at a deterministic profile -/

/-- The answer of `globMod`'s script to an export question with payload `pl`. -/
def globAns : Payload → Option Payload
  | .flat [] => a42
  | _ => none

/-- **The script of `globMod`**: `inst` is answered `ready`; `get()` is answered `42`, any other
export question a trap. -/
def globS : Handler (sigN 0) ((sigN 1).withInst Unit) := fun q =>
  match q with
  | none => .pure .ready
  | some q => .pure (globAns q.2)

theorem callee_glob {E : Engine} {a₀ : E.FuncAddr} {q : (sigN 1).Op} {a : E.FuncAddr}
    {xs : List Flat} (h : callee? [a₀] globMod.exports q = some (a, xs)) :
    q.2 = .flat [] ∧ a = a₀ ∧ xs = [] := by
  obtain ⟨⟨i, hi⟩, pl⟩ := q
  obtain rfl : i = 0 := by omega
  unfold callee? at h
  rcases pl with ys | vs
  · simp only at h
    split at h
    · rename_i hty
      have hys : ys = [] := List.map_eq_nil_iff.1 hty
      subst hys
      simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem callee_glob_none {E : Engine} {a₀ : E.FuncAddr} {q : (sigN 1).Op}
    (h : callee? [a₀] globMod.exports q = none) : globAns q.2 = none := by
  obtain ⟨⟨i, hi⟩, pl⟩ := q
  obtain rfl : i = 0 := by omega
  rcases pl with (_ | ⟨y, ys⟩) | vs
  · exact absurd h (by simp [callee?, FlatTyped, globMod, getFt])
  · rfl
  · rfl

/-- The relation of the simulation of `globMod` by its script. -/
inductive GlobRel (P : Profile) (s₀ : Store Nat) :
    IState (core3P P) globMod.imports.length globMod.exports.length →
      globS.toReduction.State → Prop
  | fresh : GlobRel P s₀ .fresh .idle
  | pre {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
      (h : ESteps (core3P P) (s₀, (core3P P).invoke (0 : Nat) []) (s, t)) :
      GlobRel P s₀ (.starting s t) (.run none (.pure .ready))
  | readying : GlobRel P s₀ (.readying (globAfter s₀)) (.run none (.pure .ready))
  | idle : GlobRel P s₀ (.ready (.idle (globAfter s₀))) .idle
  | running {q : (sigN 1).Op} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
      (hq : q.2 = .flat [])
      (h : ESteps (core3P P) (globAfter s₀, (core3P P).invoke (1 : Nat) []) (s, t)) :
      GlobRel P s₀ (.ready (.running q s t)) (.run (some q) (.pure a42))
  | refusing {q : (sigN 1).Op} (hq : globAns q.2 = none) :
      GlobRel P s₀ (.ready (.refusing q (globAfter s₀))) (.run (some q) (.pure none))

/-- **`globMod` is bounded by its script**, at a deterministic profile. -/
theorem globMod_le_script {o : GrowOracle} :
    (core3SemI (profile o)).sem globMod ≤ Strategy.ofHandler globS := by
  show engineStrategyI (core3P (profile o)) (instOfI (core3P (profile o)) globMod.mod
    globMod.imports globMod.exports) globMod.imports globMod.exports ≤ _
  rw [instOfI_glob]
  obtain ⟨_, -, hs⟩ := prepOk_eq globPrep_ok.1
  obtain ⟨t₁, hr₁, hf₁⟩ := glob_start (P := profile o) hs
  obtain ⟨t₂, hr₂, hf₂⟩ := glob_get (P := profile o) hs
  have hn₁ : Normal (profile o) (globAfter (storeOf globPrep), t₁) := .inr ⟨_, hf₁⟩
  have hn₂ : Normal (profile o) (globAfter (storeOf globPrep), t₂) := .inr ⟨_, hf₂⟩
  refine LTS.Simulation.ofLTS_le ⟨GlobRel (profile o) (storeOf globPrep), .fresh, ?_⟩
  intro x x' y l hR hstep
  change ITrans (core3P (profile o)) (some (globI (profile o))) globMod.imports
    globMod.exports x l x' at hstep
  cases hR with
  | fresh =>
    cases hstep with
    | start hI ha =>
      cases hI
      cases ha
      exact ⟨_, .vis (Reduction.Step.ask (R := globS.toReduction) (none : Option (sigN 1).Op))
        (.nil _), .pre .refl⟩
    | noStart hI ha => cases hI; cases ha
    | noInst hI => cases hI
  | pre h =>
    cases hstep with
    | scall run callout hh => exact absurd hh (Nat.not_lt_zero _)
    | sdone run final =>
      have heq := normal_unique (h.trans run) hr₁ (.inr ⟨_, final⟩) hn₁
      cases heq
      exact ⟨_, .nil _, .readying⟩
    | strap run final =>
      exact absurd (normal_unique (h.trans run) hr₁ (.inr ⟨_, final⟩) hn₁) fun heq => by
        cases heq; rw [hf₁] at final; cases final
  | readying =>
    cases hstep with
    | ready => exact ⟨_, .vis (.ret rfl) (.nil _), .idle⟩
  | idle =>
    cases hstep with
    | lift h =>
      cases h with
      | @call _ q a xs hc =>
        obtain ⟨hq, rfl, rfl⟩ := callee_glob hc
        exact ⟨_, .vis (Reduction.Step.ask (R := globS.toReduction) (some q)) (.nil _),
          by
            show GlobRel _ _ _ (.run (some q) (.pure (globAns q.2)))
            rw [hq]
            exact .running hq .refl⟩
      | @refuse _ q hc =>
        exact ⟨_, .vis (Reduction.Step.ask (R := globS.toReduction) (some q)) (.nil _),
          by
            show GlobRel _ _ _ (.run (some q) (.pure (globAns q.2)))
            rw [callee_glob_none hc]
            exact .refusing (callee_glob_none hc)⟩
  | running hq h =>
    cases hstep with
    | lift h' =>
      cases h' with
      | ucall run callout hh => exact absurd hh (Nat.not_lt_zero _)
      | oret run final =>
        have heq := normal_unique (h.trans run) hr₂ (.inr ⟨_, final⟩) hn₂
        cases heq
        rw [hf₂] at final
        cases final
        exact ⟨_, .vis (.ret rfl) (.nil _), .idle⟩
      | otrap run final =>
        exact absurd (normal_unique (h.trans run) hr₂ (.inr ⟨_, final⟩) hn₂) fun heq => by
          cases heq; rw [hf₂] at final; cases final
  | refusing hq =>
    cases hstep with
    | lift h' =>
      cases h' with
      | refused => exact ⟨_, .vis (.ret rfl) (.nil _), .idle⟩

/-! ## The handlers of the components -/

/-- The script of `startsC`. -/
def startsCH : Handler sigU sigUI :=
  (extScriptH 1 (extScriptH 1 (extScriptH 1 (baseH 1)
      ((implsN 1 lowF 1).comp ((callS 1).comp (liftH (widenH 0)))))
      ((implsN 1 lowF 1).comp ((callS 2).comp (liftH (widenH 0)))))
    ((implsN 1 [] 0).comp (globS.comp (liftH (widenH 1))))).comp
    (liftH (exportsH 2 [getL 1]))

/-- The script of `trapLC`. -/
def trapLCH : Handler sigU sigUI :=
  (extScriptH 2 (extScriptH 1 (baseH 1) ((implsN 1 [] 0).comp (trapS.comp (liftH (widenH 1)))))
    ((implsN 2 lowF 1).comp ((callS 2).comp (liftH (widenH 0))))).comp
    (liftH (exportsH 2 [getL 1]))

variable {o : GrowOracle}

theorem startsC_le : startsC.denIR (core3SemI (profile o)) ≤ Strategy.ofHandler startsCH := by
  rw [startsC, Comp.denIR]
  simp only [denNodesI, Node.denI]
  rw [startsCH, Strategy.ofHandler_comp, base_eq]
  refine Strategy.comp_mono ?_ le_rfl
  rw [← extI_ofHandler, ← extI_ofHandler, ← extI_ofHandler]
  exact extI_mono _ (extI_mono _ (extI_mono _ le_rfl
    (coreNodeI_le (callMod_le_script callPrep_one) _ _))
    (coreNodeI_le (callMod_le_script callPrep_two) _ _)) (coreNodeI_le globMod_le_script _ _)

theorem trapLC_le : trapLC.denIR (core3SemI (profile o)) ≤ Strategy.ofHandler trapLCH := by
  rw [trapLC, Comp.denIR]
  simp only [denNodesI, Node.denI]
  rw [trapLCH, Strategy.ofHandler_comp, base_eq]
  refine Strategy.comp_mono ?_ le_rfl
  rw [← extI_ofHandler, ← extI_ofHandler]
  exact extI_mono _ (extI_mono _ le_rfl (coreNodeI_le trapMod_le_script _ _))
    (coreNodeI_le (callMod_le_script callPrep_two) _ _)

theorem trapLCH_inst : trapLCH none = .pure (.fail ()) := rfl

theorem startsCH_inst : Prog.AsksWithin (startsCH none) [fV 1, fV 2] := by
  refine .call fun r₁ => ?_
  rcases r₁ with _ | (ys | (_ | ⟨w, ws⟩))
  · exact .pure _ _
  · exact .pure _ _
  · refine .call fun r₂ => ?_
    rcases r₂ with _ | (ys' | (_ | ⟨w', ws'⟩))
    all_goals exact .pure _ _
  · exact .pure _ _

theorem startsCH_runs : Prog.Runs (startsCH none) startsTrace .ready :=
  .call (.call (.pure _))

theorem startsCH_get : startsCH (some getV) = .pure v42 := rfl

theorem startsCH_ex (q : sigU.Op) : ∃ a, startsCH (some q) = .pure a := by
  obtain ⟨_ | j, pl⟩ := q
  · rcases pl with ys | (_ | ⟨v, vs⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ## The plays -/

/-- **`starts`: the host calls of every play are a prefix of `f(1), f(2)`.** -/
theorem starts_asks {p : List (Move sigU sigUI)} (hp : p ∈ startsC.denI (core3SemI (profile o))) :
    lowerAsks p <+: [fV 1, fV 2] := by
  obtain ⟨q, hq, hpr, hpq⟩ := guard_plays startsC_le hp
  have h := handler_proper_asks startsCH_inst startsCH_ex hq hpr
  rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
  · exact (lowerAsks_prefix h').trans h
  · rw [lowerAsks_append, lowerAsks_isO hx, List.append_nil]
    exact (lowerAsks_prefix h').trans h

/-- **`starts`: a complete instantiation answered by the typed host makes the calls of
`startsTrace` and is `ready`.** -/
theorem starts_complete {cs : List (Σ _ : sigU.Op, Option Payload)} {a : InstAns Unit}
    (hp : instPlay (F := sigU) cs a ∈ startsC.denI (core3SemI (profile o)))
    (hc : ∀ x ∈ cs, x.2 = unitHost x.1) : cs = startsTrace ∧ a = .ready := by
  have hp' : instPlay (F := sigU) cs a ∈ Strategy.ofHandler startsCH := by
    have e : instPlay (F := sigU) cs a = (askInst ::
        (cs.flatMap fun c => [.inl (.ask c.1), .inl (.ans c.1 c.2)])) ++ [ansInst a] := rfl
    rw [e] at hp ⊢
    exact mem_ofHandler_of_guard startsC_le (by simp [ansInst, Move.IsO]) hp
  exact runs_host_unique (host := unitHost) (runs_of_instPlay hp') startsCH_runs hc
    (by intro x hx; simp only [startsTrace, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl)

/-- **`starts`: every answer to `get()` is `42`.** -/
theorem starts_get {p : List (Move sigU sigUI)} (hp : p ∈ startsC.denI (core3SemI (profile o)))
    {r : Option Payload} (hr : ansEx getV r ∈ p) : r = v42 := by
  obtain ⟨q, hq, -, hpq⟩ := guard_plays startsC_le hp
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hq
  have hq' : ansEx (E := sigU) getV r ∈ q := by
    rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
    · exact h'.subset hr
    · rcases List.mem_append.1 hr with h | h
      · exact h'.subset h
      · rw [← List.mem_singleton.1 h] at hx
        exact hx.elim
  exact handler_ans_pure (H := startsCH) (x := some getV) startsCH_get (s := .idle) trivial hy r
    hq'

/-- **`trap`: every play is a prefix of `[inst, fail ()]`**, possibly followed by one Opponent
move that is never answered. -/
theorem trap_plays {p : List (Move sigU sigUI)} (hp : p ∈ trapLC.denI (core3SemI (profile o))) :
    p <+: [askInst, ansInst (.fail ())] ∨
      ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: [askInst, ansInst (.fail ())] ∧ x.IsO := by
  obtain ⟨q, hq, hpr, hpq⟩ := guard_plays trapLC_le hp
  have h := handler_proper_fail trapLCH_inst hq hpr
  rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
  · exact .inl (h'.trans h)
  · exact .inr ⟨q₀, x, rfl, h'.trans h, hx⟩

theorem trap_moves {p : List (Move sigU sigUI)} (hp : p ∈ trapLC.denI (core3SemI (profile o))) :
    ∀ y ∈ p, y = askInst ∨ y = ansInst (.fail ()) ∨ y.IsO := by
  have hsub : ∀ {q : List (Move sigU sigUI)}, q <+: [askInst, ansInst (.fail ())] →
      ∀ y ∈ q, y = askInst ∨ y = ansInst (.fail ()) := by
    intro q hq y hy
    have := hq.subset hy
    simpa using this
  rcases trap_plays hp with h | ⟨q₀, x, rfl, h, hx⟩
  · intro y hy
    rcases hsub h y hy with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · rcases hsub h y hy with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · rw [List.mem_singleton.1 hy]; exact .inr (.inr hx)

end Silmaril.Proofs.Wasm.Component.InstTests
