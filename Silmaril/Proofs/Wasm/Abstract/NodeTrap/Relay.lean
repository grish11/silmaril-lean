module

public import Silmaril.Games.Handler.Thms

/-!
# Trap answers relayed through one-shot handlers (proofs)

Generic facts on strategies, used to carry trap propagation from a Core 3.0 instance through the
coercions of `core3Sem` and the wiring of a core node.

* `EndsBelow T σ`: after an answer from below satisfying `T`, the next move of `σ`, if any, is at
  its upper interface. `Relays T T' σ`: it is an answer satisfying `T'`.
* `OneShot T T' h`: every program of the handler `h` returns at once, or makes one call and then
  returns at once, an answer satisfying `T'` when the answer to its call satisfies `T`. Then
  `Strategy.ofHandler h` relays `T` to `T'` (`relays_ofHandler`).
* **Composition.** Below a one-shot relaying handler (`endsBelow_comp_lower`), and above any
  one-shot handler (`endsBelow_comp_upper`), `EndsBelow` is preserved. A visible lower answer
  followed by a visible lower move is an interaction in which only hidden moves happen between the
  two (`zip_snoc_left`, `zip_nil_right`); the first hidden move is an answer at the middle
  interface, after which the middle player is idle and cannot move below (`not_legal_ret_inl`),
  and the upper player answers at once.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeTrap

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- After an answer from below satisfying `T`, the next move is at the upper interface. -/
def EndsBelow (T : (m : E.Op) → E.Ar m → Prop) (σ : Strategy E F) : Prop :=
  ∀ (p : List (Move E F)) (m : E.Op) (n : E.Ar m) (y : Move E F),
    T m n → p ++ [.inl (.ans m n), y] ∈ σ → ∃ g, y = .inr g

/-- After an answer from below satisfying `T`, the next move is an upper answer satisfying
`T'`. -/
def Relays (T : (m : E.Op) → E.Ar m → Prop) (T' : (q : F.Op) → F.Ar q → Prop)
    (σ : Strategy E F) : Prop :=
  ∀ (p : List (Move E F)) (m : E.Op) (n : E.Ar m) (y : Move E F),
    T m n → p ++ [.inl (.ans m n), y] ∈ σ → ∃ q r, y = .inr (.ans q r) ∧ T' q r

/-- **A one-shot handler**: each program returns at once, or calls once and then returns at once;
an answer satisfying `T` is relayed as an answer satisfying `T'`. -/
def OneShot (T : (m : E.Op) → E.Ar m → Prop) (T' : (q : F.Op) → F.Ar q → Prop)
    (h : Handler E F) : Prop :=
  ∀ q, (∃ r, h q = .pure r) ∨
    ∃ m k, h q = .call m k ∧ ∀ n, ∃ r, k n = .pure r ∧ (T m n → T' q r)

theorem Relays.endsBelow {T : (m : E.Op) → E.Ar m → Prop} {T' : (q : F.Op) → F.Ar q → Prop}
    {σ : Strategy E F} (h : Relays T T' σ) : EndsBelow T σ := fun p m n y hT hp =>
  let ⟨_, _, hy, _⟩ := h p m n y hT hp; ⟨_, hy⟩

/-! ## Interactions -/

section Zip

variable {α β γ : Type u}

/-- An interaction with no visible move consists of hidden moves only. -/
theorem zip_nil_right {s : List (α ⊕ β)} {t : List (β ⊕ γ)} (h : Zip s t []) :
    ∃ bs : List β, s = bs.map .inr ∧ t = bs.map .inl := by
  generalize hp : ([] : List (α ⊕ γ)) = p at h
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | left a _ _ => cases hp
  | right c _ _ => cases hp
  | sync b _ ih =>
    obtain ⟨bs, rfl, rfl⟩ := ih hp
    exact ⟨b :: bs, rfl, rfl⟩

/-- An interaction whose last visible move is a left move `a` splits at `a`. -/
theorem zip_snoc_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} {a : α}
    (h : Zip s t (p ++ [.inl a])) :
    ∃ s₁ s₂ t₁ t₂, s = s₁ ++ .inl a :: s₂ ∧ t = t₁ ++ t₂ ∧ Zip s₁ t₁ p ∧ Zip s₂ t₂ [] := by
  generalize hq : p ++ [.inl a] = q at h
  induction h generalizing p with
  | nil => simp at hq
  | @left s t q' a' h ih =>
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Sum.inl.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      exact ⟨[], s, [], t, rfl, rfl, .nil, h⟩
    | cons x p =>
      simp only [List.cons_append, List.cons.injEq] at hq
      obtain ⟨rfl, hq⟩ := hq
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hq
      exact ⟨.inl a' :: s₁, s₂, t₁, t₂, rfl, rfl, .left a' h₁, h₂⟩
  | @right s t q' c h ih =>
    cases p with
    | nil => simp at hq
    | cons x p =>
      simp only [List.cons_append, List.cons.injEq] at hq
      obtain ⟨rfl, hq⟩ := hq
      obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hq
      exact ⟨s₁, s₂, .inr c :: t₁, t₂, rfl, rfl, .right c h₁, h₂⟩
  | @sync s t q' b h ih =>
    obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, h₂⟩ := ih hq
    exact ⟨.inr b :: s₁, s₂, .inl b :: t₁, t₂, rfl, rfl, .sync b h₁, h₂⟩

end Zip

/-! ## Legality -/

theorem gpath_append {x z : Pos E F} {l₁ l₂ : List (Move E F)} (h : Path x (l₁ ++ l₂) z) :
    ∃ y, Path x l₁ y ∧ Path y l₂ z := by
  induction l₁ generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o l ih =>
    rw [List.cons_append] at h
    cases h with
    | cons hs hp =>
      obtain ⟨y, h₁, h₂⟩ := ih hp
      exact ⟨y, .cons hs h₁, h₂⟩

/-- After a lower answer, an upper move is an answer. -/
theorem legal_reply_inr {l : List (Move E F)} {m : E.Op} {n : E.Ar m} {b : Ev F}
    (h : Legal (l ++ [.inl (.ans m n), .inr b])) : ∃ q r, b = .ans q r := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨x, -, hx⟩ := gpath_append hz
  cases hx with
  | cons h₁ hx =>
    cases hx with
    | cons h₂ _ =>
      cases h₁
      cases h₂
      exact ⟨_, _, rfl⟩

/-- After a lower answer and an upper answer, no lower move. -/
theorem not_legal_ret_inl {l : List (Move E F)} {m : E.Op} {n : E.Ar m} {b : Ev F} {e : Ev E}
    (h : Legal (l ++ [.inl (.ans m n), .inr b, .inl e])) : False := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨x, -, hx⟩ := gpath_append hz
  cases hx with
  | cons h₁ hx =>
    cases hx with
    | cons h₂ hx =>
      cases hx with
      | cons h₃ _ =>
        cases h₁
        cases h₂
        cases h₃

/-! ## Composition -/

/-- **Below a relaying strategy**, trap propagation is preserved. -/
theorem endsBelow_comp_lower {T : (m : E.Op) → E.Ar m → Prop} {T' : (q : F.Op) → F.Ar q → Prop}
    {σ : Strategy E F} {τ : Strategy F G} (hσ : Relays T T' σ) (hτ : EndsBelow T' τ) :
    EndsBelow T (σ.comp τ) := by
  intro p m n y hT hp
  obtain ⟨s, hs, t, ht, hz⟩ := Strategy.mem_comp.1 hp
  rcases y with e | g
  · exfalso
    rw [show p ++ [.inl (.ans m n), .inl e] = (p ++ [.inl (.ans m n)]) ++ [.inl e] by simp] at hz
    obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, -⟩ := zip_snoc_left hz
    obtain ⟨s₃, s₄, t₃, t₄, rfl, rfl, -, h₄⟩ := zip_snoc_left h₁
    obtain ⟨bs, rfl, rfl⟩ := zip_nil_right h₄
    cases bs with
    | nil =>
      have h' := σ.of_prefix hs (s := s₃ ++ [.inl (.ans m n), .inl e]) ⟨s₂, by simp⟩
      obtain ⟨_, _, hy, -⟩ := hσ s₃ m n _ hT h'
      cases hy
    | cons b bs =>
      have h' := σ.of_prefix hs (s := s₃ ++ [.inl (.ans m n), .inr b])
        ⟨bs.map .inr ++ .inl e :: s₂, by simp⟩
      obtain ⟨q, r, hb, hT'⟩ := hσ s₃ m n _ hT h'
      simp only [Sum.inr.injEq] at hb
      subst hb
      cases bs with
      | nil =>
        exact not_legal_ret_inl (σ.legal (σ.of_prefix hs
          (s := s₃ ++ [.inl (.ans m n), .inr (.ans q r), .inl e]) ⟨s₂, by simp⟩))
      | cons b' bs =>
        have ht' := τ.of_prefix ht (s := t₃ ++ [.inl (.ans q r), .inl b'])
          ⟨bs.map .inl ++ t₂, by simp⟩
        obtain ⟨_, hg⟩ := hτ t₃ q r _ hT' ht'
        cases hg
  · exact ⟨g, rfl⟩

/-- **Above a strategy that propagates traps, a one-shot strategy keeps it.** -/
theorem endsBelow_comp_upper {T : (m : E.Op) → E.Ar m → Prop} {σ : Strategy E F}
    {τ : Strategy F G} (hσ : EndsBelow T σ) (hτ : Relays (fun _ _ => True) (fun _ _ => True) τ) :
    EndsBelow T (σ.comp τ) := by
  intro p m n y hT hp
  obtain ⟨s, hs, t, ht, hz⟩ := Strategy.mem_comp.1 hp
  rcases y with e | g
  · exfalso
    rw [show p ++ [.inl (.ans m n), .inl e] = (p ++ [.inl (.ans m n)]) ++ [.inl e] by simp] at hz
    obtain ⟨s₁, s₂, t₁, t₂, rfl, rfl, h₁, -⟩ := zip_snoc_left hz
    obtain ⟨s₃, s₄, t₃, t₄, rfl, rfl, -, h₄⟩ := zip_snoc_left h₁
    obtain ⟨bs, rfl, rfl⟩ := zip_nil_right h₄
    cases bs with
    | nil =>
      have h' := σ.of_prefix hs (s := s₃ ++ [.inl (.ans m n), .inl e]) ⟨s₂, by simp⟩
      obtain ⟨_, hg⟩ := hσ s₃ m n _ hT h'
      cases hg
    | cons b bs =>
      have h' := σ.of_prefix hs (s := s₃ ++ [.inl (.ans m n), .inr b])
        ⟨bs.map .inr ++ .inl e :: s₂, by simp⟩
      obtain ⟨q, r, rfl⟩ := legal_reply_inr (σ.legal h')
      cases bs with
      | nil =>
        exact not_legal_ret_inl (σ.legal (σ.of_prefix hs
          (s := s₃ ++ [.inl (.ans m n), .inr (.ans q r), .inl e]) ⟨s₂, by simp⟩))
      | cons b' bs =>
        have ht' := τ.of_prefix ht (s := t₃ ++ [.inl (.ans q r), .inl b'])
          ⟨bs.map .inl ++ t₂, by simp⟩
        obtain ⟨_, _, hy, -⟩ := hτ t₃ q r _ trivial ht'
        cases hy
  · exact ⟨g, rfl⟩

/-! ## One-shot handlers -/

/-- The reachable states of a one-shot handler. -/
def HInv (h : Handler E F) : h.toReduction.State → Prop
  | .idle => True
  | .run q c => c = h q ∨ ∃ r : F.Ar q, c = Prog.pure r
  | .wait q m k => h q = Prog.call m k

theorem hInv_run {T : (m : E.Op) → E.Ar m → Prop} {T' : (q : F.Op) → F.Ar q → Prop}
    {h : Handler E F} (hh : OneShot T T' h) {x z : h.toReduction.toLTS.State}
    {l : List (Move E F)} (hr : h.toReduction.toLTS.Run x l z) (hx : HInv h x) : HInv h z := by
  induction hr with
  | nil => exact hx
  | tau hs _ ih =>
    cases hs with
    | tau hc => exact hc.elim
  | vis hs _ ih =>
    apply ih
    cases hs with
    | ask q => exact Or.inl rfl
    | @call q c m k hc =>
      have hc' : c = Prog.call m k := hc
      rcases hx with rfl | ⟨r, rfl⟩
      · exact hc'
      · cases hc'
    | resume q m k n =>
      have hx' : h q = Prog.call m k := hx
      rcases hh q with ⟨r, hr⟩ | ⟨m', k', hq, hk⟩
      · rw [hr] at hx'; cases hx'
      · rw [hq] at hx'
        cases hx'
        obtain ⟨r, hr, -⟩ := hk n
        exact Or.inr ⟨r, hr⟩
    | ret _ => trivial

theorem lts_run_append {L : LTS E F} {x z : L.State} {l₁ l₂ : List (Move E F)}
    (h : L.Run x (l₁ ++ l₂) z) : ∃ y, L.Run x l₁ y ∧ L.Run y l₂ z := by
  generalize hl : l₁ ++ l₂ = l at h
  induction h generalizing l₁ with
  | nil x =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hl
    exact ⟨x, .nil x, .nil x⟩
  | tau hs _ ih =>
    obtain ⟨y, h₁, h₂⟩ := ih hl
    exact ⟨y, .tau hs h₁, h₂⟩
  | @vis x y z o s hs hr ih =>
    cases l₁ with
    | nil =>
      simp only [List.nil_append] at hl
      subst hl
      exact ⟨x, .nil x, .vis hs hr⟩
    | cons o' l₁ =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      obtain ⟨y', h₁, h₂⟩ := ih hl
      exact ⟨y', .vis hs h₁, h₂⟩

/-- A handler run along a nonempty play starts with a visible step: handlers have no internal
step. -/
theorem hrun_cons {h : Handler E F} {x z : h.toReduction.toLTS.State} {o : Move E F}
    {l : List (Move E F)} (hr : h.toReduction.toLTS.Run x (o :: l) z) :
    ∃ y, h.toReduction.Step x (some o) y ∧ h.toReduction.toLTS.Run y l z := by
  generalize hl : o :: l = l' at hr
  induction hr with
  | nil => cases hl
  | tau hs _ _ => cases hs with | tau hc => exact hc.elim
  | vis hs hr _ =>
    cases hl
    exact ⟨_, hs, hr⟩

/-- **A one-shot handler relays its answers.** -/
theorem relays_ofHandler {T : (m : E.Op) → E.Ar m → Prop} {T' : (q : F.Op) → F.Ar q → Prop}
    {h : Handler E F} (hh : OneShot T T' h) : Relays T T' (Strategy.ofHandler h) := by
  intro p m n y hT hp
  obtain ⟨z, hz⟩ := Strategy.mem_ofHandler.1 hp
  obtain ⟨x, h₁, h₂⟩ := lts_run_append hz
  have hx := hInv_run hh h₁ trivial
  obtain ⟨x', hs, h₂⟩ := hrun_cons h₂
  cases hs with
  | resume q m k n =>
    have hx' : h q = Prog.call m k := hx
    rcases hh q with ⟨r, hr⟩ | ⟨m', k', hq, hk⟩
    · rw [hr] at hx'; cases hx'
    · rw [hq] at hx'
      cases hx'
      obtain ⟨r, hr, hTr⟩ := hk n
      obtain ⟨x'', hs, -⟩ := hrun_cons h₂
      cases hs with
      | @call _ c _ _ hc =>
        have hc' : k n = Prog.call _ _ := hc
        rw [hr] at hc'; cases hc'
      | @ret _ c r' hd =>
        have hd' : k n = Prog.pure r' := hd
        rw [hr] at hd'
        cases hd'
        exact ⟨q, r, rfl, hTr hT⟩

end Silmaril.Proofs.Wasm.Abstract.NodeTrap
