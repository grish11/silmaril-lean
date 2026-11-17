module

public import Silmaril.Semantics.Region.Semantic.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Proofs
universe u v w z
variable {State : Type u} {Lab : Type v} {Event : Type w} {Stop : Type z}
variable {T : TransitionSystem State Lab Event Stop} {U V : Lab → Prop}
variable {A D B E C : State → Prop} {X : Lab → Prop}

theorem sound_iff_outward : Sound T A U X ↔ ∀ l, outward T A U l → X l := by
  constructor
  · rintro h l ⟨s, es, t, ha, hf, rfl⟩
    exact h s es t ha hf
  · intro h s es t ha hf
    exact h _ ⟨s, es, t, ha, hf, rfl⟩

theorem local_sound (cert : Local T U D B)
    (admit : ∀ s, A s → D s) (boundary : ∀ t, B t → X (T.pc t)) : Sound T A U X := by
  intro s es t ha hf
  have hd := admit s ha
  clear ha
  induction hf with
  | leave hu edge out => exact boundary _ ((cert _ _ _ hd hu edge).2 out)
  | @step s t f es rest hu edge tail ih =>
    have ht : U (T.pc t) := by cases tail <;> assumption
    exact ih ((cert _ _ _ hd hu edge).1 ht)

theorem glue_local (disjoint : ∀ l, U l → V l → False)
    (left : Local T U D B) (right : Local T V E C)
    {entryU entryV : Lab}
    (uv : Wiring T U V D B E entryV X) (vu : Wiring T V U E C D entryU X) :
    Local T (fun l => U l ∨ V l)
      (fun s => (U (T.pc s) ∧ D s) ∨ (V (T.pc s) ∧ E s))
      (fun s => X (T.pc s)) := by
  intro s es t hs _ edge
  rcases hs with ⟨hu, hd⟩ | ⟨hv, he⟩
  · obtain ⟨internal, external⟩ := left s es t hd hu edge
    constructor
    · intro ht
      rcases ht with hut | hvt
      · exact .inl ⟨hut, internal hut⟩
      · have hout : ¬ U (T.pc t) := fun h => disjoint _ h hvt
        exact .inr ⟨hvt, ((uv s es t hd hu edge hout (external hout)).1 hvt).2⟩
    · intro ht
      have hout : ¬ U (T.pc t) := fun h => ht (.inl h)
      exact (uv s es t hd hu edge hout (external hout)).2 (fun h => ht (.inr h))
  · obtain ⟨internal, external⟩ := right s es t he hv edge
    constructor
    · intro ht
      rcases ht with hut | hvt
      · have hout : ¬ V (T.pc t) := fun h => disjoint _ hut h
        exact .inl ⟨hut, ((vu s es t he hv edge hout (external hout)).1 hut).2⟩
      · exact .inr ⟨hvt, internal hvt⟩
    · intro ht
      have hout : ¬ V (T.pc t) := fun h => ht (.inr h)
      exact (vu s es t he hv edge hout (external hout)).2 (fun h => ht (.inl h))

theorem wp_iff (Q : Lab → List Event → State → Prop) (R : Stop → List Event → State → Prop) :
    PartialHoare T A U Q R ↔ ∀ s, A s → wp T U Q R s := by
  constructor
  · intro h s ha
    exact ⟨fun t es f eq hf => h.1 t es f (eq ▸ ha) hf,
      fun t es f k eq hi hh => h.2 t es f k (eq ▸ ha) hi hh⟩
  · intro h
    exact ⟨fun s es t ha hf => (h s ha).1 s es t rfl hf,
      fun s es t k ha hi hh => (h s ha).2 s es t k rfl hi hh⟩

theorem family_local {Index : Type*} (supports : Index → Lab → Prop)
    (domains boundaries : Index → State → Prop) (entries : Index → Lab)
    (children : ∀ i, Local T (supports i) (domains i) (boundaries i))
    (wiring : FamilyWiring T supports domains boundaries entries X) :
    Local T (fun l => ∃ i, supports i l)
      (fun s => ∃ i, supports i (T.pc s) ∧ domains i s) (fun s => X (T.pc s)) := by
  rintro s es t ⟨i, hi, hd⟩ _ edge
  obtain ⟨internal, external⟩ := children i s es t hd hi edge
  by_cases ht : supports i (T.pc t)
  · exact ⟨fun _ => ⟨i, ht, internal ht⟩, fun out => False.elim (out ⟨i, ht⟩)⟩
  · obtain ⟨cross, outward⟩ := wiring i s es t hd hi edge ht (external ht)
    refine ⟨?_, outward⟩
    intro inside
    obtain ⟨j, hj, _, he⟩ := cross inside
    exact ⟨j, hj, he⟩

theorem singleEntry_union {edge : Lab → Lab → Prop} {e : Lab}
    (left : SingleEntry edge U e)
    (rightEntries : ∀ x y, edge x y → V y → ¬ V x → U x) :
    SingleEntry edge (fun l => U l ∨ V l) e := by
  refine ⟨.inl left.1, ?_⟩
  intro x y he hx hy
  rcases hy with hu | hv
  · exact left.2 x y he (fun h => hx (.inl h)) hu
  · exact False.elim (hx (.inl (rightEntries x y he hv (fun h => hx (.inr h)))))

theorem finishes_not_diverges {s : State} (finish : Finishes T U s) : ¬ Diverges T U s := by
  rintro ⟨states, events, hzero, edges⟩
  have chain : ∀ t, Acc (fun t s => U (T.pc s) ∧ U (T.pc t) ∧ ∃ es, T.step s es t) t →
      ∀ n, t = states n → False := by
    intro t acc
    induction acc with
    | intro t next ih =>
      intro n heq
      subst t
      exact ih (states (n + 1)) ⟨(edges n).1, (edges (n + 1)).1, events n, (edges n).2⟩ (n + 1) rfl
  exact chain s finish.1 0 hzero.symm

theorem wp_unfold (Q : Lab → List Event → State → Prop)
    (R : Stop → List Event → State → Prop) {s : State} (inside : U (T.pc s)) :
    wp T U Q R s ↔
      (∀ k, T.halt s k → R k [] s) ∧
      ∀ es t, T.step s es t →
        (¬ U (T.pc t) → Q (T.pc t) es t) ∧
        (U (T.pc t) → wp T U (fun l rest f => Q l (es ++ rest) f)
          (fun k rest f => R k (es ++ rest) f) t) := by
  constructor
  · intro h
    refine ⟨fun k halt => h.2 s [] s k rfl (.refl inside) halt, ?_⟩
    intro es t edge
    refine ⟨fun out => h.1 s es t rfl (.leave inside edge out), ?_⟩
    intro ht
    constructor
    · intro t' rest f eq run
      subst t'
      exact h.1 s (es ++ rest) f rfl (.step inside edge run)
    · intro t' rest f k eq run halt
      subst t'
      exact h.2 s (es ++ rest) f k rfl (.step inside edge run) halt
  · rintro ⟨halts, steps⟩
    constructor
    · intro s' es t eq run
      subst s'
      cases run with
      | leave _ edge out => exact (steps _ _ edge).1 out
      | @step _ mid _ _ _ _ edge tail =>
        have ht : U (T.pc mid) := by cases tail <;> assumption
        exact ((steps _ _ edge).2 ht).1 _ _ _ rfl tail
    · intro s' es t k eq run halt
      subst s'
      cases run with
      | refl _ => exact halts k halt
      | @step _ mid _ _ _ _ edge tail =>
        have ht : U (T.pc mid) := by cases tail <;> assumption
        exact ((steps _ _ edge).2 ht).2 _ _ _ _ rfl tail halt

end Silmaril.Semantics.Region.Proofs
