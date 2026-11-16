module

public import Silmaril.Wasm.Component.DWiringChatter2.Defs
public import Silmaril.Games.Handler.Thms

/-!
# Plays through `splitH`

`splitH e` forwards each outer question to the pairing below at once, routed by
`splitQ e`, and passes the answer back. So the pairing play under a play `c`
above it is `c.map (splitRoute e)`:

* `route_prefix_of_zip`: if a legal pairing play `a` interacts with a play of
  `splitH e` with visible part `c`, then `c.map (splitRoute e)` is a prefix of
  `a`, unless `c` ends with an outer question not yet forwarded (`a` may also
  hold an answer that `splitH e` has not passed on yet);
* `exists_zip_route`: conversely, every legal `c` is the visible part of
  `c.map (splitRoute e)` interacting with a play of `splitH e`;
* `legal_route`: routing preserves legality.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter2

open Silmaril.Games Silmaril.Wasm.Component

variable {e : Nat}

/-! ## Legality -/

/-- The position of the pairing play under a position above `splitH e`. -/
def rpos (e : Nat) : Pos sigU sigU → Pos sigU (sigU ⊕ₛ sigU)
  | .idle => .idle
  | .run q => .run (splitQ e q)
  | .wait q m => .wait (splitQ e q) m

theorem splitQ_of_lt {q : sigU.Op} (hq : q.1 < e) : splitQ e q = .inl q := by
  simp [splitQ, hq]

theorem splitQ_of_not_lt {q : sigU.Op} (hq : ¬ q.1 < e) : splitQ e q = .inr (q.1 - e, q.2) := by
  simp [splitQ, hq]

theorem step_route {x y : Pos sigU sigU} {o : Move sigU sigU} (h : Step x o y) :
    Step (rpos e x) (splitRoute e o) (rpos e y) := by
  cases h with
  | ask q => exact .ask _
  | call q m => exact .call _ _
  | reply q m n => exact .reply _ _ _
  | ret q r =>
    by_cases hq : q.1 < e
    · simp only [rpos, splitRoute, hq, ↓reduceIte, splitQ_of_lt hq]
      exact .ret _ _
    · simp only [rpos, splitRoute, hq, ↓reduceIte, splitQ_of_not_lt hq]
      exact .ret _ _

theorem path_route {x y : Pos sigU sigU} {c : List (Move sigU sigU)} (h : Path x c y) :
    Path (rpos e x) (c.map (splitRoute e)) (rpos e y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (step_route hs) ih

/-- Routing preserves legality. -/
theorem legal_route {c : List (Move sigU sigU)} (h : Legal c) : Legal (c.map (splitRoute e)) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨_, path_route (e := e) hy⟩

/-! ## Runs of `splitH e` -/

/-- `splitH e` waiting for the pairing's answer to the routed question. -/
def wst (e : Nat) (q : sigU.Op) : (splitH e).toReduction.State :=
  if q.1 < e then .wait q (.inl q) (fun n => .pure n)
  else .wait q (.inr (q.1 - e, q.2)) (fun n => .pure n)

theorem wst_of_lt {q : sigU.Op} (hq : q.1 < e) :
    wst e q = .wait q (.inl q) (fun n => .pure n) := by
  simp [wst, hq]

theorem wst_of_not_lt {q : sigU.Op} (hq : ¬ q.1 < e) :
    wst e q = .wait q (.inr (q.1 - e, q.2)) (fun n => .pure n) := by
  simp [wst, hq]

theorem splitH_of_lt {q : sigU.Op} (hq : q.1 < e) :
    splitH e q = .call (.inl q) (fun n => .pure n) := by
  simp [splitH, hq]

theorem splitH_of_not_lt {q : sigU.Op} (hq : ¬ q.1 < e) :
    splitH e q = .call (.inr (q.1 - e, q.2)) (fun n => .pure n) := by
  simp [splitH, hq]

/-- Handler runs have no silent steps. -/
theorem run_cons {x y : (splitH e).toReduction.State} {o : Move (sigU ⊕ₛ sigU) sigU}
    {w : List (Move (sigU ⊕ₛ sigU) sigU)} (h : (splitH e).toReduction.toLTS.Run x (o :: w) y) :
    ∃ z, (splitH e).toReduction.toLTS.step x (some o) z ∧
      (splitH e).toReduction.toLTS.Run z w y :=
  match h with
  | .tau hs' _ => by cases hs' with | tau hc => exact hc.elim
  | .vis hs' hr => ⟨_, hs', hr⟩

/-- The state of `splitH e` above a position of the play it serves. -/
def sst (e : Nat) : Pos sigU sigU → (splitH e).toReduction.State
  | .idle => .idle
  | .run q => wst e q
  | .wait q _ => wst e q

/-- **Every legal play is served by `splitH e` from the routed pairing play.** -/
theorem exists_run_route {x y : Pos sigU sigU} {c : List (Move sigU sigU)} (h : Path x c y) :
    ∃ w y', (splitH e).toReduction.toLTS.Run (sst e x) w y' ∧ Zip (c.map (splitRoute e)) w c := by
  induction h with
  | nil => exact ⟨[], _, .nil _, .nil⟩
  | @cons x z y o c hs _ ih =>
    obtain ⟨w, y', hr, hz⟩ := ih
    cases hs with
    | ask q =>
      by_cases hq : q.1 < e
      · rw [sst, wst_of_lt hq] at hr
        refine ⟨_, _, LTS.Run.vis (Reduction.Step.ask q) (LTS.Run.vis (Reduction.Step.call (splitH_of_lt hq)) hr), ?_⟩
        show Zip (Sum.inr (Ev.ask (splitQ e q)) :: _) _ _
        rw [splitQ_of_lt hq]
        exact .right _ (.sync _ hz)
      · rw [sst, wst_of_not_lt hq] at hr
        refine ⟨_, _, LTS.Run.vis (Reduction.Step.ask q) (LTS.Run.vis (Reduction.Step.call (splitH_of_not_lt hq)) hr), ?_⟩
        show Zip (Sum.inr (Ev.ask (splitQ e q)) :: _) _ _
        rw [splitQ_of_not_lt hq]
        exact .right _ (.sync _ hz)
    | call q m => exact ⟨w, y', hr, .left _ hz⟩
    | reply q m n => exact ⟨w, y', hr, .left _ hz⟩
    | ret q r =>
      by_cases hq : q.1 < e
      · refine ⟨.inl (.ans (.inl q) r) :: .inr (.ans q r) :: w, y', ?_, ?_⟩
        · rw [sst, wst_of_lt hq]
          exact LTS.Run.vis (Reduction.Step.resume (R := (splitH e).toReduction) q (.inl q)
            (fun n => .pure n) r) (LTS.Run.vis (Reduction.Step.ret rfl) hr)
        · simp only [List.map_cons, splitRoute, hq, ↓reduceIte]
          exact .sync _ (.right _ hz)
      · refine ⟨.inl (.ans (.inr (q.1 - e, q.2)) r) :: .inr (.ans q r) :: w, y', ?_, ?_⟩
        · rw [sst, wst_of_not_lt hq]
          exact LTS.Run.vis (Reduction.Step.resume (R := (splitH e).toReduction) q
            (.inr (q.1 - e, q.2)) (fun n => .pure n) r) (LTS.Run.vis (Reduction.Step.ret rfl) hr)
        · simp only [List.map_cons, splitRoute, hq, ↓reduceIte]
          exact .sync _ (.right _ hz)

/-- **Every legal play is served by `splitH e` from the routed pairing play.** -/
theorem exists_zip_route {c : List (Move sigU sigU)} (h : Legal c) :
    ∃ w ∈ Strategy.ofHandler (splitH e), Zip (c.map (splitRoute e)) w c := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨w, y', hr, hz⟩ := exists_run_route (e := e) hy
  exact ⟨w, Strategy.mem_ofHandler.2 ⟨y', hr⟩, hz⟩

/-! ## The pairing play under a play through `splitH e` -/

/-- `c` ends with an outer question. -/
def EndsAsk (c : List (Move sigU sigU)) : Prop := ∃ c' q, c = c' ++ [.inr (.ask q)]

theorem EndsAsk.cons {c : List (Move sigU sigU)} (h : EndsAsk c) (o : Move sigU sigU) :
    EndsAsk (o :: c) := by
  obtain ⟨c', q, rfl⟩ := h
  exact ⟨o :: c', q, rfl⟩

/-- Phases of `splitH e` serving a question. -/
inductive Ph
  /-- Between questions. -/
  | idle
  /-- The outer question `q` is received, not yet forwarded. -/
  | fwd (q : sigU.Op)
  /-- `q` is forwarded; waiting for the pairing. -/
  | busy (q : sigU.Op)
  /-- The pairing answered `r`, not yet passed on. -/
  | back (q : sigU.Op) (r : Option Payload)

/-- The state of `splitH e` in a phase. -/
def Ph.st (e : Nat) : Ph → (splitH e).toReduction.State
  | .idle => .idle
  | .fwd q => .run q (splitH e q)
  | .busy q => wst e q
  | .back q r => .run q (.pure r)

/-- The position of the pairing in a phase. -/
def Ph.ok (e : Nat) : Ph → Pos sigU (sigU ⊕ₛ sigU) → Prop
  | .busy q, x => x = .run (splitQ e q) ∨ ∃ m, x = .wait (splitQ e q) m
  | _, x => x = .idle

/-- How the visible play relates to the pairing play, from a phase. -/
def Ph.concl (e : Nat) : Ph → List (Move sigU (sigU ⊕ₛ sigU)) → List (Move sigU sigU) → Prop
  | .idle, a, c => c.map (splitRoute e) <+: a ∨ EndsAsk c
  | .fwd q, a, c => c = [] ∨ (.inr (.ask (splitQ e q)) :: c.map (splitRoute e)) <+: a ∨ EndsAsk c
  | .busy _, a, c => c.map (splitRoute e) <+: a ∨ EndsAsk c
  | .back q r, a, c => c = [] ∨ ∃ c', c = .inr (.ans q r) :: c' ∧
      (c'.map (splitRoute e) <+: a ∨ EndsAsk c')

theorem concl_aux {a : List (Move sigU (sigU ⊕ₛ sigU))} {w : List (Move (sigU ⊕ₛ sigU) sigU)}
    {c : List (Move sigU sigU)} (h : Zip a w c) :
    ∀ (φ : Ph) y xa ya, (splitH e).toReduction.toLTS.Run (φ.st e) w y → Path xa a ya →
      φ.ok e xa → φ.concl e a c := by
  induction h with
  | nil =>
    intro φ _ _ _ _ _ _
    cases φ with
    | idle => exact .inl (List.prefix_refl _)
    | fwd q => exact .inl rfl
    | busy q => exact .inl (List.prefix_refl _)
    | back q r => exact .inl rfl
  | @left a' w' c' l _ ih =>
    intro φ y xa ya hr hp hok
    cases hp with
    | @cons _ xa' _ _ _ hs hp' =>
    cases φ with
    | busy q =>
      have hok' : Ph.ok e (.busy q) xa' := by
        rcases hok with rfl | ⟨m, rfl⟩
        · cases hs with | call _ m => exact .inr ⟨m, rfl⟩
        · cases hs with | reply _ _ _ => exact .inl rfl
      rcases ih (.busy q) y xa' ya hr hp' hok' with h | h
      · exact .inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
      · exact .inr (h.cons _)
    | idle => cases hok; cases hs
    | fwd q => cases hok; cases hs
    | back q r => cases hok; cases hs
  | @right a' w' c' o _ ih =>
    intro φ y xa ya hr hp hok
    obtain ⟨z, hs, hr'⟩ := run_cons hr
    cases φ with
    | idle =>
      cases hs with
      | ask q =>
        rcases ih (.fwd q) y xa ya hr' hp hok with h | h | h
        · subst h; exact .inr ⟨[], q, rfl⟩
        · exact .inl h
        · exact .inr (h.cons _)
    | fwd q =>
      cases hs with
      | ret hc =>
        change splitH e q = _ at hc
        by_cases hq : q.1 < e
        · rw [splitH_of_lt hq] at hc; cases hc
        · rw [splitH_of_not_lt hq] at hc; cases hc
    | busy q =>
      by_cases hq : q.1 < e
      · simp only [Ph.st, wst_of_lt hq] at hs; cases hs
      · simp only [Ph.st, wst_of_not_lt hq] at hs; cases hs
    | back q r =>
      cases hs with
      | ret hc =>
        change Prog.pure r = _ at hc
        cases hc
        exact .inr ⟨c', rfl, ih .idle y xa ya hr' hp hok⟩
  | @sync a' w' c' u _ ih =>
    intro φ y xa ya hr hp hok
    obtain ⟨z, hs, hr'⟩ := run_cons hr
    cases hp with
    | @cons _ xa' _ _ _ hs' hp' =>
    cases φ with
    | idle => cases hs
    | fwd q =>
      cases hs with
      | call hc =>
        change splitH e q = _ at hc
        cases hok
        by_cases hq : q.1 < e
        · rw [splitH_of_lt hq] at hc
          cases hc
          cases hs'
          rw [← wst_of_lt hq] at hr'
          have hok' : Ph.ok e (.busy q) (.run (.inl q)) := .inl (by rw [splitQ_of_lt hq])
          rcases ih (.busy q) y _ ya hr' hp' hok' with h | h
          · exact .inr (.inl (by rw [splitQ_of_lt hq]; exact List.cons_prefix_cons.2 ⟨rfl, h⟩))
          · exact .inr (.inr h)
        · rw [splitH_of_not_lt hq] at hc
          cases hc
          cases hs'
          rw [← wst_of_not_lt hq] at hr'
          have hok' : Ph.ok e (.busy q) (.run (.inr (q.1 - e, q.2))) :=
            .inl (by rw [splitQ_of_not_lt hq])
          rcases ih (.busy q) y _ ya hr' hp' hok' with h | h
          · exact .inr (.inl (by rw [splitQ_of_not_lt hq]; exact List.cons_prefix_cons.2 ⟨rfl, h⟩))
          · exact .inr (.inr h)
    | busy q =>
      by_cases hq : q.1 < e
      · simp only [Ph.st, wst_of_lt hq] at hs
        cases hs with
        | resume _ _ _ n =>
        simp only [Ph.ok, splitQ_of_lt hq] at hok
        rcases hok with rfl | ⟨m, rfl⟩ <;> cases hs'
        rcases ih (.back q n) y _ ya hr' hp' rfl with h | ⟨c'', rfl, h | h⟩
        · subst h; exact .inl List.nil_prefix
        · refine .inl ?_
          simp only [List.map_cons, splitRoute, hq, ↓reduceIte]
          exact List.cons_prefix_cons.2 ⟨rfl, h⟩
        · exact .inr (h.cons _)
      · simp only [Ph.st, wst_of_not_lt hq] at hs
        cases hs with
        | resume _ _ _ n =>
        simp only [Ph.ok, splitQ_of_not_lt hq] at hok
        rcases hok with rfl | ⟨m, rfl⟩ <;> cases hs'
        rcases ih (.back q n) y _ ya hr' hp' rfl with h | ⟨c'', rfl, h | h⟩
        · subst h; exact .inl List.nil_prefix
        · refine .inl ?_
          simp only [List.map_cons, splitRoute, hq, ↓reduceIte]
          exact List.cons_prefix_cons.2 ⟨rfl, h⟩
        · exact .inr (h.cons _)
    | back q r =>
      cases hs with
      | call hc => change Prog.pure r = _ at hc; cases hc

/-- **The pairing play under a play through `splitH e`.** If a legal play `a` of
the pairing interacts with a play of `splitH e` with visible part `c`, then
`c.map (splitRoute e)` is a prefix of `a`, unless `c` ends with an outer
question not yet forwarded. -/
theorem route_prefix_of_zip {a : List (Move sigU (sigU ⊕ₛ sigU))}
    {w : List (Move (sigU ⊕ₛ sigU) sigU)} {c : List (Move sigU sigU)} (hz : Zip a w c)
    (hw : w ∈ Strategy.ofHandler (splitH e)) (ha : Legal a) :
    c.map (splitRoute e) <+: a ∨ EndsAsk c := by
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hw
  obtain ⟨ya, hya⟩ := ha
  exact concl_aux hz .idle y .idle ya hy hya rfl

end Silmaril.Proofs.Wasm.Component.DWiringChatter2
