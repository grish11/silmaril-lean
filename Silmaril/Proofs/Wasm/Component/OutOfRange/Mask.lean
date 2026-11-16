module

public import Silmaril.Proofs.Wasm.Component.OutOfRange.Trap

/-!
# `maskH` calls in range only

`maskH e` answers an out-of-range question with `none` itself and forwards the
others: every call it makes below is in range (`maskH_lowerIn`, by an invariant
of its reduction semantics). A composite calls below only what its lower
component calls (`zip_inl_mem`), so the denotation `Comp.denUD C (.mk I ns xs)`
calls only functions below `I.length` (`denUD_lowerIn`). Such a strategy has no
eventually-trap infinite play below `widenH I.length`
(`not_eventuallyTrap_of_lowerIn`): its trap events are answers only, and two
lower answers in a row are illegal.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.OutOfRange

open Silmaril.Games Silmaril.Wasm.Component

universe u

/-- Two lower answers in a row are illegal. -/
theorem not_legal_lower_ans_ans {E F : Sig.{u}} {s : List (Move E F)} {m m' : E.Op}
    {r : E.Ar m} {r' : E.Ar m'} : ¬ Legal (s ++ [.inl (.ans m r), .inl (.ans m' r')]) := by
  rintro ⟨y, h⟩
  obtain ⟨x, -, h⟩ := Path.append_iff.1 h
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ _ => cases h₁; cases h₂

/-- The lower moves of an interaction are moves of its lower component. -/
theorem zip_inl_mem {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p : List (α ⊕ γ)} (h : Zip s t p) {a : α} (ha : .inl a ∈ p) : .inl a ∈ s := by
  induction h with
  | nil => cases ha
  | left a' _ ih =>
    rcases List.mem_cons.1 ha with ha | ha
    · cases ha; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih ha)
  | right c _ ih =>
    rcases List.mem_cons.1 ha with ha | ha
    · cases ha
    · exact ih ha
  | sync b _ ih => exact List.mem_cons_of_mem _ (ih ha)

/-- Every call below is of a function under `e`. -/
def LowerIn {G : Sig.{0}} (e : Nat) (σ : Strategy sigU G) : Prop :=
  ∀ s ∈ σ, ∀ m : Nat × Payload, .inl (.ask m) ∈ s → m.1 < e

theorem lowerIn_comp {G H : Sig.{0}} {e : Nat} {σ : Strategy sigU G} (hσ : LowerIn e σ)
    (τ : Strategy G H) : LowerIn e (σ.comp τ) := by
  rintro p ⟨s, hs, t, -, hz⟩ m hm
  exact hσ s hs m (zip_inl_mem hz hm)

/-- The invariant of `maskH e`: a running program is the handler's own or
returns, and a pending call is in range and returns at once. -/
def MGood (e : Nat) : (maskH e).toReduction.toLTS.State → Prop
  | .idle => True
  | .run q c => c = maskH e q ∨ ∃ r, c = .pure r
  | .wait _ m k => m.1 < e ∧ ∀ n, ∃ r, k n = .pure r

theorem mgood_step {e : Nat} {x y : (maskH e).toReduction.toLTS.State}
    {l : Option (Move sigU sigU)} (hx : MGood e x) (h : (maskH e).toReduction.toLTS.step x l y) :
    MGood e y ∧ ∀ m, l = some (.inl (.ask m)) → m.1 < e := by
  cases h with
  | ask q => exact ⟨.inl rfl, fun _ h => by cases h⟩
  | tau hc => exact hc.elim
  | @call q c m k hc =>
    change c = .call m k at hc
    rcases hx with rfl | ⟨r, rfl⟩
    · simp only [maskH, Target.prog] at hc
      split at hc
      · cases hc
        exact ⟨⟨by assumption, fun n => ⟨n, rfl⟩⟩, fun _ h => by cases h; assumption⟩
      · cases hc
    · cases hc
  | resume q m k n => exact ⟨.inr (hx.2 n), fun _ h => by cases h⟩
  | ret _ => exact ⟨trivial, fun _ h => by cases h⟩

theorem mgood_run {e : Nat} {x y : (maskH e).toReduction.toLTS.State}
    {s : List (Move sigU sigU)} (h : (maskH e).toReduction.toLTS.Run x s y) (hx : MGood e x) :
    MGood e y ∧ ∀ m, .inl (.ask m) ∈ s → m.1 < e := by
  induction h with
  | nil => exact ⟨hx, fun _ h => by cases h⟩
  | tau hs _ ih => exact ih (mgood_step hx hs).1
  | vis hs _ ih =>
    obtain ⟨hy, hl⟩ := mgood_step hx hs
    obtain ⟨hz, hr⟩ := ih hy
    refine ⟨hz, fun m hm => ?_⟩
    rcases List.mem_cons.1 hm with hm | hm
    · exact hl m (by rw [hm])
    · exact hr m hm

/-- **`maskH e` calls in range only.** -/
theorem maskH_lowerIn (e : Nat) : LowerIn e (Strategy.ofHandler (maskH e)) := by
  intro s hs m hm
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hs
  exact (mgood_run hy trivial).2 m hm

variable {M : Type} [CoreModule M]

theorem denNodesD_lowerIn (C : DCoreSem M) {e : Nat} :
    ∀ (e' : Nat) (ns : List (Node M)) (D : DStrategy sigU sigU), LowerIn e D.toStrategy →
      LowerIn e (denNodesD C e' ns D).toStrategy
  | _, [], D, hD => by rw [denNodesD_nil]; exact hD
  | e', n :: ns, D, hD => by
    rw [denNodesD_cons]
    exact denNodesD_lowerIn C _ ns _ (lowerIn_comp hD _)

/-- **A component calls its imports in range only.** -/
theorem denUD_lowerIn (C : DCoreSem M) (c : Comp M) :
    LowerIn c.imports.length (c.denUD C).toStrategy := by
  cases c with
  | mk I ns xs =>
    rw [Comp.denUD]
    exact lowerIn_comp (denNodesD_lowerIn C _ ns _ (maskH_lowerIn _)) _

/-- **In-range strategies have no trap chatter below `widenH`.** -/
theorem not_eventuallyTrap_of_lowerIn {G : Sig.{0}} {n : Nat} {σ : DStrategy sigU G}
    (hσ : LowerIn n σ.toStrategy) {I : Set (List (Move sigU G))} (hI : I ∈ σ.inf) :
    ¬ EventuallyTrap n I := by
  rintro ⟨t₀, ht₀, htr⟩
  have hP := σ.inf_isInf hI
  obtain ⟨s, hs, hl⟩ := hP.unbounded (t₀.length + 2)
  obtain ⟨v, rfl⟩ := hP.prefix_of_length_le ht₀ hs (by omega)
  have hv : 2 ≤ v.length := by simp at hl; omega
  have hpl : ∀ u, u <+: t₀ ++ v → u ∈ σ.toStrategy := fun u hu =>
    σ.inf_sub hI (hP.of_prefix hs hu)
  match v, hv, hs, hpl with
  | a :: b :: rest, _, hs, hpl =>
    have mem : ∀ u, u <+: t₀ ++ a :: b :: rest → u ∈ I := fun u hu => hP.of_prefix hs hu
    obtain ⟨ea, rfl, hea⟩ := htr [] a (mem _ ⟨b :: rest, by simp⟩)
    obtain ⟨eb, rfl, heb⟩ := htr [.inl ea] b (mem _ ⟨rest, by simp⟩)
    cases ea with
    | ask m =>
      have := hσ _ (hpl (t₀ ++ [.inl (.ask m)]) ⟨.inl eb :: rest, by simp⟩) m (by simp)
      exact absurd hea (Nat.not_le.2 this)
    | ans m r =>
      cases eb with
      | ask m' =>
        have := hσ _ (hpl (t₀ ++ [.inl (.ans m r), .inl (.ask m')]) ⟨rest, by simp⟩) m'
          (by simp)
        exact absurd heb (Nat.not_le.2 this)
      | ans m' r' =>
        exact not_legal_lower_ans_ans (s := t₀) (m := m) (m' := m') (r := r) (r' := r')
          (σ.toStrategy.legal (hpl _ ⟨rest, by simp⟩))

end Silmaril.Proofs.Wasm.Component.OutOfRange
