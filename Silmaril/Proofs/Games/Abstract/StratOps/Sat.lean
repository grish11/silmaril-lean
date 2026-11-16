module

public import Silmaril.Games.Abstract.StratOps.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Games.Abstract.FullFun.Thms
public import Silmaril.Proofs.Games.Abstract.StratOps.Laws

/-!
# Operations on observation triples and saturation (proofs)

* `satP_le`: the call prefixes of `t` are among those of `t'` when the behaviours and streams
  of `t` are among those of `t'` and the pending calls of `t` are call prefixes of `t'`;
* `satP_seqT_sat_right`: saturating the second argument of a sequence does not change its call
  prefixes; `satP_seqT_sat_left`: neither does saturating the first, when the second is total;
* `saturated_seqT`, `saturated_pureT`, `satP_mapT`, `satP_whiskerRightT`, `satP_whiskerLeftT`:
  admissibility is preserved; maps and whiskering commute with saturation;
* `not_sat_seqT`: without totality, saturating the first argument can add call prefixes.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-! ## Streams and call prefixes -/

section Stream

variable {α : Type u}

theorem append_get_lt (c : List α) (ω : Nat → α) {n : Nat} (h : n < c.length) :
    (c ++ₛ ω) n = c[n] := by
  induction c generalizing n with
  | nil => simp at h
  | cons x c ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih (by simpa using h)

theorem append_get_ge (c : List α) (ω : Nat → α) (n : Nat) :
    (c ++ₛ ω) (c.length + n) = ω n := by
  induction c with
  | nil => simp [Stream'.appendStream']
  | cons x c ih =>
    rw [List.length_cons, Nat.add_right_comm]
    exact ih

theorem streamTake_append (c : List α) (ω : Nat → α) (k : Nat) :
    streamTake (c ++ₛ ω) (c.length + k) = c ++ streamTake ω k := by
  apply List.ext_getElem (by simp [streamTake])
  intro i h₁ h₂
  simp only [streamTake, List.getElem_ofFn]
  rcases Nat.lt_or_ge i c.length with h | h
  · rw [append_get_lt c ω h, List.getElem_append_left h]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [append_get_ge, List.getElem_append_right (by omega)]
    simp

theorem streamTake_append_le (c : List α) (ω : Nat → α) {k : Nat} (hk : k ≤ c.length) :
    streamTake (c ++ₛ ω) k = c.take k := by
  apply List.ext_getElem (by simp [streamTake]; omega)
  intro i h₁ h₂
  simp only [streamTake, List.getElem_ofFn, List.getElem_take]
  exact append_get_lt c ω (by simp [streamTake] at h₁; omega)

end Stream

theorem callPre_take {c : List (Call E)} {k : Nat} (hk : k < c.length) :
    CallPre (c.take k) c[k].1 c :=
  ⟨c[k].2, c.drop (k + 1), by rw [List.getElem_cons_drop, List.take_append_drop]⟩

theorem callPre_append_right {c c₁ : List (Call E)} {m : E.Op} (h : CallPre c m c₁)
    (c₂ : List (Call E)) : CallPre c m (c₁ ++ c₂) := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨n, c' ++ c₂, by simp⟩

theorem callPre_append_left {c c₂ : List (Call E)} {m : E.Op} (c₁ : List (Call E))
    (h : CallPre c m c₂) : CallPre (c₁ ++ c) m (c₁ ++ c₂) := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨n, c', by simp⟩

theorem callPre_append {c c₁ c₂ : List (Call E)} {m : E.Op} (h : CallPre c m (c₁ ++ c₂)) :
    CallPre c m c₁ ∨ ∃ c₃, c = c₁ ++ c₃ ∧ CallPre c₃ m c₂ := by
  obtain ⟨n, c', h⟩ := h
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, rfl⟩ | ⟨c'', rfl, h'⟩
  · exact .inr ⟨a', rfl, n, c', rfl⟩
  · cases c'' with
    | nil =>
      simp only [List.nil_append] at h'
      exact .inr ⟨[], by simp, n, c', h'.symm⟩
    | cons y c'' =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 h'
      exact .inl ⟨n, c'', rfl⟩

/-! ## Call prefixes -/

section SatP

theorem pending_satP {t : ObsTriple E S A B} {s : S} {a : A} {x : List (Call E) × E.Op}
    (h : x ∈ t.2.1 s a) : x ∈ satP t s a := .inl h

theorem beh_satP {t : ObsTriple E S A B} {s : S} {a : A} {d c : List (Call E)} {e : End S B}
    {m : E.Op} (h : (d, e) ∈ t.1 s a) (hc : CallPre c m d) : (c, m) ∈ satP t s a :=
  .inr (.inr (.inl ⟨d, e, h, hc⟩))

theorem stream_satP {t : ObsTriple E S A B} {s : S} {a : A} {ω : Nat → Call E}
    (h : ω ∈ t.2.2 s a) (k : Nat) : (streamTake ω k, (ω k).1) ∈ satP t s a :=
  .inr (.inr (.inr ⟨ω, h, k, rfl, rfl⟩))

/-- Saturations are equal when the components and call prefixes are. -/
theorem sat_eq {t t' : ObsTriple E S A B} (h₁ : t.1 = t'.1) (h₂ : satP t = satP t')
    (h₃ : t.2.2 = t'.2.2) : sat t = sat t' := by
  simp only [sat, h₁, h₂, h₃]

theorem satP_le {S' A' B' : Type u} {t : ObsTriple E S A B} {t' : ObsTriple E S' A' B'}
    {s : S} {a : A} {s' : S'} {a' : A'}
    (h₁ : ∀ d e, (d, e) ∈ t.1 s a → ∃ e', (d, e') ∈ t'.1 s' a')
    (h₂ : t.2.1 s a ⊆ satP t' s' a') (h₃ : t.2.2 s a ⊆ t'.2.2 s' a') :
    satP t s a ⊆ satP t' s' a' := by
  rintro ⟨c, m⟩ (h | ⟨d, m', hd, hc⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, hk, hm⟩)
  · exact h₂ h
  · exact satP_prefix (h₂ hd) hc
  · obtain ⟨e', he'⟩ := h₁ d e hd
    exact beh_satP he' hc
  · exact .inr (.inr (.inr ⟨ω, h₃ hω, k, hk, hm⟩))

/-- Saturation is monotone in the pending calls. -/
theorem satP_le_of_pending {t t' : ObsTriple E S A B} (h₁ : t.1 = t'.1) (h₃ : t.2.2 = t'.2.2)
    (h₂ : ∀ s a, t.2.1 s a ⊆ t'.2.1 s a) (s : S) (a : A) : satP t s a ⊆ satP t' s a :=
  satP_le (fun _ e h => ⟨e, h₁ ▸ h⟩) (fun _ hx => .inl (h₂ s a hx)) (h₃ ▸ le_rfl)

end SatP

/-! ## Sequencing -/

section Seq

variable {t : ObsTriple E S A B} {u : ObsTriple E S B C}

/-- A call prefix of `u` after a return of `t` is a call prefix of the sequence. -/
theorem seqT_satP_ret {s : S} {a : A} {c₁ c₂ : List (Call E)} {b : B} {s₁ : S} {m : E.Op}
    (hr : (c₁, End.ret b s₁) ∈ t.1 s a) (h : (c₂, m) ∈ satP u s₁ b) :
    (c₁ ++ c₂, m) ∈ satP (seqT t u) s a := by
  rcases h with h | ⟨d, m', hd, hc⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, rfl, rfl⟩
  · exact .inl (.inr ⟨c₁, b, s₁, c₂, m, hr, h, rfl⟩)
  · exact satP_prefix (.inl (.inr ⟨c₁, b, s₁, d, m', hr, hd, rfl⟩)) (callPre_append_left c₁ hc)
  · exact beh_satP (t := seqT t u) (.inr (.inr ⟨c₁, b, s₁, d, e, hr, hd, rfl⟩))
      (callPre_append_left c₁ hc)
  · have hs : c₁ ++ₛ ω ∈ (seqT t u).2.2 s a := .inr ⟨c₁, b, s₁, ω, hr, hω, rfl⟩
    have := stream_satP hs (c₁.length + k)
    rwa [streamTake_append, append_get_ge] at this

/-- A call prefix of `t` is a call prefix of the sequence, when `u` is total. -/
theorem seqT_satP_left (hu : Total u) {s : S} {a : A} {c : List (Call E)} {m : E.Op}
    (h : (c, m) ∈ satP t s a) : (c, m) ∈ satP (seqT t u) s a := by
  rcases h with h | ⟨d, m', hd, hc⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, rfl, rfl⟩
  · exact .inl (.inl h)
  · exact satP_prefix (.inl (.inl hd)) hc
  · cases e with
    | trap => exact beh_satP (t := seqT t u) (.inl ⟨d, hd, rfl⟩) hc
    | div => exact beh_satP (t := seqT t u) (.inr (.inl ⟨d, hd, rfl⟩)) hc
    | ret b s₁ =>
      rcases hu s₁ b with ⟨⟨d₂, e₂⟩, h₂⟩ | ⟨⟨d₂, m₂⟩, h₂⟩ | ⟨ω, hω⟩
      · exact beh_satP (t := seqT t u) (.inr (.inr ⟨d, b, s₁, d₂, e₂, hd, h₂, rfl⟩))
          (callPre_append_right hc d₂)
      · exact satP_prefix (.inl (.inr ⟨d, b, s₁, d₂, m₂, hd, h₂, rfl⟩))
          (callPre_append_right hc d₂)
      · obtain ⟨n, c', rfl⟩ := hc
        have hs : (c ++ ⟨m, n⟩ :: c') ++ₛ ω ∈ (seqT t u).2.2 s a :=
          .inr ⟨_, b, s₁, ω, hd, hω, rfl⟩
        have := stream_satP hs c.length
        have hk : c.length < (c ++ ⟨m, n⟩ :: c').length := by simp
        rw [streamTake_append_le _ ω hk.le, append_get_lt _ ω hk] at this
        simpa using this
  · exact stream_satP (t := seqT t u) (.inl hω) k

theorem satP_seqT_sat_right : satP (seqT t (sat u)) = satP (seqT t u) := by
  funext s a
  refine le_antisymm (satP_le (fun d e h => ⟨e, h⟩) ?_ le_rfl)
    (satP_le_of_pending (t := seqT t u) (t' := seqT t (sat u)) rfl rfl (fun s a => ?_) s a)
  · rintro _ (h | ⟨c₁, b, s₁, c₂, m, hr, h, rfl⟩)
    · exact .inl (.inl h)
    · exact seqT_satP_ret hr h
  · rintro _ (h | ⟨c₁, b, s₁, c₂, m, hr, h, rfl⟩)
    · exact .inl h
    · exact .inr ⟨c₁, b, s₁, c₂, m, hr, .inl h, rfl⟩

theorem satP_seqT_sat_left (hu : Total u) : satP (seqT (sat t) u) = satP (seqT t u) := by
  funext s a
  refine le_antisymm (satP_le (fun d e h => ⟨e, h⟩) ?_ le_rfl)
    (satP_le_of_pending (t := seqT t u) (t' := seqT (sat t) u) rfl rfl (fun s a => ?_) s a)
  · rintro ⟨c, m⟩ (h | ⟨c₁, b, s₁, c₂, m', hr, h, he⟩)
    · exact seqT_satP_left hu h
    · exact .inl (.inr ⟨c₁, b, s₁, c₂, m', hr, h, he⟩)
  · rintro _ (h | h)
    · exact .inl (.inl h)
    · exact .inr h

theorem total_sat (hu : Total u) : Total (sat u) := by
  intro s b
  rcases hu s b with h | ⟨x, hx⟩ | h
  · exact .inl h
  · exact .inr (.inl ⟨x, .inl hx⟩)
  · exact .inr (.inr h)

/-- **Sequencing commutes with saturation** when the second argument is total. -/
theorem sat_seqT (hu : Total u) : sat (seqT (sat t) (sat u)) = sat (seqT t u) :=
  sat_eq rfl ((satP_seqT_sat_left (total_sat hu)).trans satP_seqT_sat_right) rfl

/-- **Sequencing commutes with saturation** when the first argument is admissible. -/
theorem sat_seqT_of_adm (ht : Admissible t) : sat (seqT (sat t) (sat u)) = sat (seqT t u) := by
  rw [show sat t = t from ht]
  exact sat_eq rfl satP_seqT_sat_right rfl

/-- **Sequencing preserves admissibility.** -/
theorem saturated_seqT (ht : Saturated t) (hu : Saturated u) : Saturated (seqT t u) := by
  rw [saturated_iff] at ht hu ⊢
  funext s a
  refine le_antisymm ?_ fun _ => .inl
  have hP : ∀ {s a c m}, (c, m) ∈ satP t s a → (c, m) ∈ (seqT t u).2.1 s a := fun h =>
    .inl (ht ▸ h)
  have hQ : ∀ {c₁ b s₁ c₂ m}, (c₁, End.ret b s₁) ∈ t.1 s a → (c₂, m) ∈ satP u s₁ b →
      (c₁ ++ c₂, m) ∈ (seqT t u).2.1 s a := fun hr h =>
    .inr ⟨_, _, _, _, _, hr, hu ▸ h, rfl⟩
  rintro ⟨c, m⟩ (h | ⟨d, m', hd, hc⟩ | ⟨d, e, hd, hc⟩ | ⟨ω, hω, k, rfl, rfl⟩)
  · exact h
  · rcases hd with hd | ⟨c₁, b, s₁, c₂, m'', hr, h₂, he⟩
    · exact hP (satP_prefix (.inl hd) hc)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rcases callPre_append hc with hc | ⟨c₃, rfl, hc⟩
      · exact hP (beh_satP hr hc)
      · exact hQ hr (satP_prefix (.inl h₂) hc)
  · rcases hd with ⟨_, hd, he⟩ | ⟨_, hd, he⟩ | ⟨c₁, b, s₁, c₂, e', hr, h₂, he⟩
    · obtain ⟨rfl, -⟩ := Prod.mk.inj he
      exact hP (beh_satP hd hc)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj he
      exact hP (beh_satP hd hc)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj he
      rcases callPre_append hc with hc | ⟨c₃, rfl, hc⟩
      · exact hP (beh_satP hr hc)
      · exact hQ hr (beh_satP h₂ hc)
  · rcases hω with hω | ⟨c₁, b, s₁, ω', hr, hω', rfl⟩
    · exact hP (stream_satP hω k)
    · rcases Nat.lt_or_ge k c₁.length with hk | hk
      · rw [streamTake_append_le c₁ ω' hk.le, append_get_lt c₁ ω' hk]
        exact hP (beh_satP hr (callPre_take hk))
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [streamTake_append, append_get_ge]
        exact hQ hr (stream_satP hω' j)

end Seq

/-- **Saturating the first argument can add call prefixes**: `t` calls once and returns, and `u`
has no observation at all. The call is a call prefix of `t`, but the sequence has no
observation. -/
theorem not_sat_seqT :
    ∃ (E : Sig.{0}) (t u : ObsTriple E PUnit PUnit PUnit),
      sat (seqT (sat t) (sat u)) ≠ sat (seqT t u) := by
  let E : Sig.{0} := ⟨PUnit, fun _ => PUnit⟩
  let t : ObsTriple E PUnit PUnit PUnit :=
    (fun _ _ => {([⟨⟨⟩, ⟨⟩⟩], End.ret ⟨⟩ ⟨⟩)}, fun _ _ => ∅, fun _ _ => ∅)
  let u : ObsTriple E PUnit PUnit PUnit := (fun _ _ => ∅, fun _ _ => ∅, fun _ _ => ∅)
  refine ⟨E, t, u, fun h => ?_⟩
  have hm : (([], ⟨⟩) : List (Call E) × E.Op) ∈ (sat (seqT (sat t) (sat u))).2.1 ⟨⟩ ⟨⟩ :=
    .inl (.inl (beh_satP (t := t) rfl ⟨⟨⟩, [], rfl⟩))
  rw [h] at hm
  rcases hm with (h | ⟨_, _, _, _, _, _, h, _⟩) | ⟨_, _, h | ⟨_, _, _, _, _, _, h, _⟩, -⟩ |
      ⟨d, e, hd, n, c', hc⟩ | ⟨ω, h | ⟨_, _, _, _, _, h, _⟩, -⟩
  · exact h
  · exact h
  · exact h
  · exact h
  · rcases hd with ⟨_, hd, he⟩ | ⟨_, hd, he⟩ | ⟨_, _, _, _, _, _, h, _⟩
    · cases Set.mem_singleton_iff.1 hd
    · cases Set.mem_singleton_iff.1 hd
    · exact h
  · exact h
  · exact h

/-! ## Pure maps, whiskering and the identity -/

theorem saturated_pureT : Saturated (pureT : ObsTriple E S A A) := by
  rw [saturated_iff]
  funext s a
  refine le_antisymm ?_ (fun _ => .inl)
  rintro ⟨c, m⟩ (h | ⟨_, _, h, -⟩ | ⟨d, e, hd, n, c', hc⟩ | ⟨_, h, -⟩)
  · exact h
  · exact h
  · obtain ⟨rfl, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hd)
    simp at hc
  · exact h

theorem logs_map {F : FullFun E S A B} {h : B → C} {s : S} {a : A} {d : List (Call E)} :
    (∃ e, (d, e) ∈ (F.map h).1 s a) ↔ ∃ e, (d, e) ∈ F.1 s a := by
  simp only [FullFun.mem_map]
  constructor
  · rintro ⟨_, c, e, h, he⟩
    obtain ⟨rfl, -⟩ := Prod.mk.inj he
    exact ⟨e, h⟩
  · rintro ⟨e, h⟩
    exact ⟨_, d, e, h, rfl⟩

theorem satP_map_eq {S' A' C' : Type u} {t : ObsTriple E S A B} {t' : ObsTriple E S' A' C'}
    {s : S} {a : A} {s' : S'} {a' : A'}
    (h₁ : ∀ d, (∃ e, (d, e) ∈ t'.1 s' a') ↔ ∃ e, (d, e) ∈ t.1 s a)
    (h₂ : t'.2.1 s' a' = t.2.1 s a) (h₃ : t'.2.2 s' a' = t.2.2 s a) :
    satP t' s' a' = satP t s a :=
  le_antisymm (satP_le (fun d e h => (h₁ d).1 ⟨e, h⟩) (h₂ ▸ fun _ => .inl) h₃.le)
    (satP_le (fun d e h => (h₁ d).2 ⟨e, h⟩) (h₂ ▸ fun _ => .inl) h₃.ge)

theorem satP_mapT (t : ObsTriple E S A B) (h : B → C) : satP (mapT t h) = satP t :=
  funext fun _ => funext fun _ => satP_map_eq (fun _ => logs_map) rfl rfl

theorem satP_whiskerRightT (t : ObsTriple E S A B) (C : Type u) (s : S) (p : A × C) :
    satP (whiskerRightT t C) s p = satP t s p.1 :=
  satP_map_eq (fun _ => logs_map) rfl rfl

theorem satP_whiskerLeftT (C : Type u) (t : ObsTriple E S A B) (s : S) (p : C × A) :
    satP (whiskerLeftT C t) s p = satP t s p.2 :=
  satP_map_eq (fun _ => logs_map) rfl rfl

theorem sat_mapT (t : ObsTriple E S A B) (h : B → C) : sat (mapT t h) = mapT (sat t) h :=
  ext_full rfl (satP_mapT t h)

theorem sat_comapT {A' : Type u} (t : ObsTriple E S A B) (k : A' → A) :
    sat (comapT t k) = comapT (sat t) k := rfl

theorem sat_whiskerRightT (t : ObsTriple E S A B) (C : Type u) :
    sat (whiskerRightT t C) = whiskerRightT (sat t) C :=
  ext_full rfl (funext fun s => funext fun p => satP_whiskerRightT t C s p)

theorem sat_whiskerLeftT (C : Type u) (t : ObsTriple E S A B) :
    sat (whiskerLeftT C t) = whiskerLeftT C (sat t) :=
  ext_full rfl (funext fun s => funext fun p => satP_whiskerLeftT C t s p)

end Silmaril.Proofs.Games.Abstract.StratOps
