module

public import Silmaril.Wasi.Component.Consequence.Defs
public import Silmaril.Logic.Szs.Thms

/-!
# Components as consequence checkers: proofs

Proofs of `Silmaril.Wasi.Component.Consequence.Thms`: the execution status and its
classification, epochs, policy morphisms and the transport of soundness along them.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Consequence

open Silmaril.Wasi Silmaril.Wasi.Consequence Silmaril.Logic Silmaril.Logic.Szs
open Silmaril.Wasm.Component (Val)

universe u v u₁ u₂ u₃

variable {X : Type u} {C : Type v} {A : Type u₁} {S : Type u₂} {S' : Type u₃}
  {T : Set (List WEv)} {r : Reading X C} {x : X} {c : C}

theorem accepted_iff_sat : Accepted T r x c ↔ Current.SAT (execProblem T r x c) := by
  constructor
  · rintro ⟨s, e, hT, hr⟩
    exact ⟨⟨(s, e), hT, _, hr⟩, (s, e), ⟨hT, _, hr⟩, hr⟩
  · rintro ⟨-, ⟨s, e⟩, ⟨hT, -⟩, hr⟩
    exact ⟨s, e, hT, hr⟩

theorem classify_holds {I : Type} (P : Problem I) : (classify P).holds P := by
  unfold classify
  split_ifs with h0 h1 h2
  · exact h0
  · exact ⟨Set.nonempty_iff_ne_empty.2 h0, h1⟩
  · exact ⟨Set.nonempty_iff_ne_empty.2 h0, h2⟩
  · obtain ⟨i, hi, hc⟩ := Set.not_subset.1 h1
    obtain ⟨j, hj, hc'⟩ := Set.not_subset.1 h2
    exact ⟨Set.nonempty_iff_ne_empty.2 h0, ⟨j, hj, not_not.1 hc'⟩, i, hi, hc⟩

theorem classify_cases {I : Type} (P : Problem I) :
    classify P = .CAX ∨ classify P = .STH ∨ classify P = .SCT ∨ classify P = .NOC := by
  unfold classify
  split_ifs <;> simp

theorem classify_eq_cax_iff {I : Type} (P : Problem I) : classify P = .CAX ↔ Current.CAX P := by
  unfold classify
  split_ifs with h0 <;> simp [Current.CAX, h0]

theorem sat_iff_classify {I : Type} (P : Problem I) :
    Current.SAT P ↔ classify P = .STH ∨ classify P = .NOC := by
  have hh := classify_holds P
  rcases classify_cases P with h | h | h | h <;> rw [h] at hh ⊢
  · simp only [Status.holds, Current.CAX] at hh
    simp [Current.SAT, hh]
  · simp only [Status.holds, Current.STH] at hh
    obtain ⟨⟨i, hi⟩, hs⟩ := hh
    simpa using ⟨⟨i, hi⟩, i, hi, hs hi⟩
  · simp only [Status.holds, Current.SCT] at hh
    simp only [Current.SAT, reduceCtorEq, or_self, iff_false, not_and, not_exists]
    exact fun _ i hi hc => hh.2 hi hc
  · simp only [Status.holds, Current.NOC] at hh
    simpa using ⟨hh.1, hh.2.1⟩

theorem execProblem_cax_iff :
    Current.CAX (execProblem T r x c) ↔ ∀ a, ¬ Answered T r x c a := by
  simp only [Current.CAX, execProblem, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq,
    Answered, Prod.forall, not_exists, not_and]
  constructor
  · intro h a s e hT hr; exact h s e hT a hr
  · intro h s e hT a hr; exact h a s e hT hr

theorem execProblem_thm_iff :
    Current.THM (execProblem T r x c) ↔ ∀ a, Answered T r x c a → a = .yes := by
  simp only [Current.THM, execProblem, Set.subset_def, Set.mem_ofPred_eq, Answered, Prod.forall]
  constructor
  · rintro h a ⟨s, e, hT, hr⟩
    have := h s e ⟨hT, a, hr⟩
    rw [hr] at this
    simpa using this
  · rintro h s e ⟨hT, a, hr⟩
    rw [h a ⟨s, e, hT, hr⟩] at hr
    exact hr

theorem execProblem_csa_iff :
    Current.CSA (execProblem T r x c) ↔ ∃ a, a ≠ .yes ∧ Answered T r x c a := by
  simp only [Current.CSA, execProblem, Set.mem_ofPred_eq, Answered, Prod.exists]
  constructor
  · rintro ⟨-, s, e, ⟨hT, a, hr⟩, hc⟩
    refine ⟨a, fun ha => hc (ha ▸ hr), s, e, hT, hr⟩
  · rintro ⟨a, ha, s, e, hT, hr⟩
    refine ⟨⟨(s, e), hT, a, hr⟩, s, e, ⟨hT, a, hr⟩, fun h => ha ?_⟩
    rw [hr] at h
    simpa using h

theorem classify_of_answered_iff {a₀ : Answer} (h : ∀ a, Answered T r x c a ↔ a = a₀) :
    classify (execProblem T r x c) = if a₀ = .yes then .STH else .SCT := by
  have hne : (execProblem T r x c).ax ≠ ∅ := fun h0 =>
    (execProblem_cax_iff.1 h0) a₀ ((h a₀).2 rfl)
  have hthm : Current.THM (execProblem T r x c) ↔ a₀ = .yes :=
    ⟨fun ht => ht |> execProblem_thm_iff.1 |> (· a₀ ((h a₀).2 rfl)),
      fun hy => execProblem_thm_iff.2 fun a ha => ((h a).1 ha).trans hy⟩
  have hcth : (execProblem T r x c).ax ⊆ (execProblem T r x c).conjᶜ ↔ a₀ ≠ .yes := by
    constructor
    · rintro hs rfl
      obtain ⟨s, e, hT, hr⟩ := (h .yes).2 rfl
      exact hs (a := (s, e)) ⟨hT, _, hr⟩ (show r s e = _ from hr)
    · rintro hy ⟨s, e⟩ ⟨hT, a, hr⟩ hc
      have ha : a = .yes := by
        change r s e = _ at hc; change r s e = _ at hr; rw [hr] at hc; simpa using hc
      exact hy (((h a).1 ⟨s, e, hT, hr⟩).symm.trans ha)
  unfold classify
  have hthm' : (execProblem T r x c).ax ⊆ (execProblem T r x c).conj ↔ a₀ = .yes := hthm
  split_ifs with h0 h1 h2 h3 <;> simp_all

theorem accepted_of_thm (hne : (execProblem T r x c).ax.Nonempty)
    (h : Current.THM (execProblem T r x c)) : Accepted T r x c :=
  accepted_iff_sat.2 ⟨hne, hne.choose, hne.choose_spec, h hne.choose_spec⟩

theorem exists_thm_not_accepted :
    ∃ (T : Set (List WEv)) (r : Reading Unit Unit),
      Current.THM (execProblem T r () ()) ∧ ¬ Accepted T r () () := by
  refine ⟨∅, fun _ _ => some ((), (), .yes), ?_, ?_⟩
  · rintro p ⟨h, -⟩; exact h.elim
  · rintro ⟨_, _, h, -⟩; exact h

theorem importAssert_call_thm {f : FnName} {dec : List Val → Option (X × C)} :
    Current.THM (execProblem T (importAssert .call f dec) x c) := by
  rw [execProblem_thm_iff]
  rintro a ⟨s, e, -, hr⟩
  cases e <;> simp only [importAssert, reduceCtorEq] at hr
  split_ifs at hr
  obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.1 hr
  simp only [Prod.mk.injEq] at hp
  exact hp.2.2.symm

theorem forallHosts_existsHost {H : Set HostFn} (hH : H.Nonempty) (h : ForallHosts H T r x c) :
    ExistsHost H T r x c :=
  ⟨hH.choose, hH.choose_spec, h _ hH.choose_spec⟩

/-! ## Epochs -/

theorem epochState_append_reset (P : Policy A S) (l l' : List (Step A)) :
    epochState P (l ++ .reset :: l') = epochState P l' := by
  simp [epochState, List.foldl_append, Policy.apply]

theorem hom_epochState {P : Policy A S} {Q : Policy A S'} (h : P.Hom Q)
    (l : List (Step A)) : h.toFun (Consequence.epochState P l) = Consequence.epochState Q l := by
  unfold Consequence.epochState
  suffices ∀ s, h.toFun (l.foldl P.apply s) = l.foldl Q.apply (h.toFun s) by
    rw [this, h.map_init]
  induction l with
  | nil => intro s; rfl
  | cons st l ih =>
    intro s
    cases st with
    | add a => simp only [List.foldl_cons, Policy.apply]; rw [ih, h.map_add]
    | reset => simp only [List.foldl_cons, Policy.apply]; rw [ih, h.map_init]

theorem accepted_stateful_hom {P : Policy A S} {Q : Policy A S'} (h : P.Hom Q)
    {stepOf : WEv → Option (Step A)} {claim : WEv → Option (C × Answer)} {y : S'} :
    Accepted T (stateful Q stepOf claim) y c ↔
      ∃ x, h.toFun x = y ∧ Accepted T (stateful P stepOf claim) x c := by
  simp only [Accepted, stateful, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨s, e, hT, ⟨c', a'⟩, hp, rfl, rfl, rfl⟩
    exact ⟨_, hom_epochState h _, s, e, hT, _, hp, rfl, rfl, rfl⟩
  · rintro ⟨x, rfl, s, e, hT, ⟨c', a'⟩, hp, rfl, rfl, rfl⟩
    exact ⟨s, e, hT, _, hp, (hom_epochState h _).symm, rfl, rfl⟩

theorem sound_hom {P : Policy A S} {Q : Policy A S'} (h : P.Hom Q)
    {stepOf : WEv → Option (Step A)} {claim : WEv → Option (C × Answer)}
    {target : S → C → Prop} (hs : Sound (Accepted T (stateful P stepOf claim)) target)
    (hinv : ∀ x x' c, h.toFun x = h.toFun x' → target x c → target x' c) :
    Sound (Accepted T (stateful Q stepOf claim))
      fun y c => ∀ x, h.toFun x = y → target x c := by
  intro y c hy x hx
  obtain ⟨x', rfl, hx'⟩ := (accepted_stateful_hom h).1 hy
  exact hinv x' x c hx.symm (hs _ _ hx')

theorem finset_sound_of_mem_closed [DecidableEq A] {stepOf : WEv → Option (Step A)}
    {claim : WEv → Option (C × Answer)} {target : List A → C → Prop}
    (hs : Sound (Accepted T (stateful Policy.list stepOf claim)) target)
    (hclosed : ∀ xs ys c, (∀ a, a ∈ xs ↔ a ∈ ys) → target xs c → target ys c) :
    Sound (Accepted T (stateful Policy.finset stepOf claim))
      fun s c => ∀ xs : List A, xs.toFinset = s → target xs c :=
  sound_hom Policy.listToFinset hs fun xs ys c h => hclosed xs ys c fun a => by
    have := congrArg (a ∈ ·) h
    simpa [Policy.listToFinset] using this

theorem sound_perm_closure {R target : List A → C → Prop} (hs : Sound R target)
    (hperm : ∀ xs ys c, xs.Perm ys → target xs c → target ys c) :
    Sound (fun ys c => ∃ xs, xs.Perm ys ∧ R xs c) target := by
  rintro ys c ⟨xs, hp, hr⟩
  exact hperm xs ys c hp (hs xs c hr)

end Silmaril.Proofs.Wasi.Component.Consequence
