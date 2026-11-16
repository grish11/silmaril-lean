module

public import Silmaril.Games.Abstract.SessionLinkAssoc.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

/-!
# Linking sessions: literal associativity and units (basic lemmas)

Membership in `mapStore`, streams, and lists of session rounds.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkAssoc

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionLinkAssoc

universe u

variable {E : Sig.{u}} {S S' A B : Type u}

/-! ## Transport -/

theorem obsTriple_ext {t t' : ObsTriple E S A B} (h₁ : ∀ s a x, x ∈ t.1 s a ↔ x ∈ t'.1 s a)
    (h₂ : ∀ s a x, x ∈ t.2.1 s a ↔ x ∈ t'.2.1 s a)
    (h₃ : ∀ s a x, x ∈ t.2.2 s a ↔ x ∈ t'.2.2 s a) : t = t' :=
  Prod.ext (funext fun s => funext fun a => Set.ext (h₁ s a))
    (Prod.ext (funext fun s => funext fun a => Set.ext (h₂ s a))
      (funext fun s => funext fun a => Set.ext (h₃ s a)))

theorem mapEnd_mapEnd {S'' : Type u} (e : S → S') (e' : S' → S'') (x : End S B) :
    mapEnd e' (mapEnd e x) = mapEnd (e' ∘ e) x := by
  cases x <;> rfl

theorem mapEnd_id (x : End S B) : mapEnd id x = x := by
  cases x <;> rfl

theorem mapStore_symm_mapStore (e : S ≃ S') (t : ObsTriple E S A B) :
    mapStore e.symm (mapStore e t) = t := by
  refine obsTriple_ext (fun s a x => ?_) (fun s a x => ?_) (fun s a x => ?_)
  · simp only [mapStore, Equiv.symm_symm, Equiv.symm_apply_apply, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa [mapEnd_mapEnd, mapEnd_id] using hz
    · intro hx
      exact ⟨(x.1, mapEnd e x.2), ⟨x, hx, rfl⟩, by simp [mapEnd_mapEnd, mapEnd_id]⟩
  · simp [mapStore]
  · simp [mapStore]

theorem mapStore_injective (e : S ≃ S') :
    Function.Injective (mapStore (E := E) (A := A) (B := B) e) := fun t t' h => by
  rw [← mapStore_symm_mapStore e t, h, mapStore_symm_mapStore]

theorem dropTrap_eq_iff {t : ObsTriple E S A B} :
    dropTrap t = t ↔ ∀ s a c, (c, End.trap) ∉ t.1 s a := by
  constructor
  · intro h s a c hc
    have : (c, End.trap) ∈ (dropTrap t).1 s a := by rw [h]; exact hc
    exact this.2 rfl
  · intro h
    refine obsTriple_ext (fun s a x => ?_) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun he => h s a x.1 ?_⟩⟩
    rw [← he]
    exact hx

/-! ## Streams -/

theorem streamTake_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

@[simp] theorem streamTake_zero {α : Type u} (ω : ℕ → α) : streamTake ω 0 = [] := rfl

@[simp] theorem length_streamTake {α : Type u} (ω : ℕ → α) (k : ℕ) :
    (streamTake ω k).length = k := by
  simp [streamTake]

theorem getElem_streamTake {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j < (streamTake ω k).length) :
    (streamTake ω k)[j] = ω j := by
  simp [streamTake]

theorem stream_ext {α : Type u} {ω ω' : ℕ → α} (h : ∀ k, streamTake ω k = streamTake ω' k) :
    ω = ω' := by
  funext k
  have := List.getElem_of_eq (h (k + 1)) (by simp : k < (streamTake ω (k + 1)).length)
  rwa [getElem_streamTake, getElem_streamTake] at this

theorem streamTake_prefix {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j ≤ k) :
    streamTake ω j <+: streamTake ω k := by
  induction k with
  | zero => cases Nat.le_zero.1 h; exact List.prefix_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h' | h'
    · rw [streamTake_succ]; exact (ih (by omega)).trans (List.prefix_append _ _)
    · cases le_antisymm h h'; exact List.prefix_refl _

theorem streamTake_add {α : Type u} (f : ℕ → α) (N j : ℕ) :
    streamTake f (N + j) = streamTake f N ++ streamTake (fun i => f (N + i)) j := by
  induction j with
  | zero => simp
  | succ j ih => rw [← Nat.add_assoc, streamTake_succ, ih, streamTake_succ, List.append_assoc]

theorem logTake_succ (l : ℕ → List (Call E)) (n : ℕ) :
    logTake l (n + 1) = logTake l n ++ l n := by
  simp [logTake, streamTake_succ]

@[simp] theorem logTake_zero (l : ℕ → List (Call E)) : logTake l 0 = [] := rfl

theorem logTake_mono (l : ℕ → List (Call E)) {j k : ℕ} (h : j ≤ k) :
    logTake l j <+: logTake l k := by
  obtain ⟨r, hr⟩ := streamTake_prefix l h
  exact ⟨r.flatten, by rw [logTake, logTake, ← hr, List.flatten_append]⟩

/-- Logs that are eventually empty: the log of the first `n` rounds is the whole log. -/
theorem logTake_of_nil {l : ℕ → List (Call E)} {n : ℕ} (hl : ∀ k, n ≤ k → l k = []) {k : ℕ}
    (hk : n ≤ k) : logTake l k = logTake l n := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [logTake_succ, ih, hl k hk, List.append_nil]

/-! ## Session rounds -/

section Rounds

variable {E : Sig.{u}} {S A B : Type u}

@[simp] theorem served_nil :
    served ([] : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) = [] := rfl

@[simp] theorem served_cons (r : A × List (Call E) × (B ⊕ PUnit.{u + 1}))
    (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    served (r :: rs) = ⟨r.1, r.2.2⟩ :: served rs := rfl

@[simp] theorem served_append (rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    served (rs ++ rs') = served rs ++ served rs' := by
  simp [served]

@[simp] theorem servedLog_nil :
    servedLog ([] : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) = [] := rfl

@[simp] theorem servedLog_cons (r : A × List (Call E) × (B ⊕ PUnit.{u + 1}))
    (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    servedLog (r :: rs) = r.2.1 ++ servedLog rs := rfl

@[simp] theorem servedLog_append (rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    servedLog (rs ++ rs') = servedLog rs ++ servedLog rs' := by
  simp [servedLog]

@[simp] theorem length_served (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (served rs).length = rs.length := by
  simp [served]

theorem served_eq_nil {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    served rs = [] ↔ rs = [] := by
  simp [served]

/-- Split session rounds along their served calls. -/
theorem served_eq_append {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {c d : List (Call (sig1 A B))} (h : served rs = c ++ d) :
    ∃ rs₁ rs₂, rs = rs₁ ++ rs₂ ∧ served rs₁ = c ∧ served rs₂ = d := by
  obtain ⟨rs₁, rs₂, h₁, h₂, h₃⟩ := List.map_eq_append_iff.1 h
  exact ⟨rs₁, rs₂, h₁, h₂, h₃⟩

variable {B' : Type u} {t : ObsTriple E S A B'}

theorem rounds_append {s s₁ s₂ : S} {rs rs' : List (A × List (Call E) × B')}
    (h : Rounds t s rs s₁) (h' : Rounds t s₁ rs' s₂) : Rounds t s (rs ++ rs') s₂ := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h (ih h')

theorem rounds_of_append {s s₂ : S} {rs rs' : List (A × List (Call E) × B')}
    (h : Rounds t s (rs ++ rs') s₂) : ∃ s₁, Rounds t s rs s₁ ∧ Rounds t s₁ rs' s₂ := by
  induction rs generalizing s with
  | nil => exact ⟨s, .nil _, h⟩
  | cons r rs ih =>
    cases h with
    | cons hr h =>
      obtain ⟨s₁, h₁, h₂⟩ := ih h
      exact ⟨s₁, .cons hr h₁, h₂⟩

theorem rounds_nil_iff {s s' : S} : Rounds t s ([] : List (A × List (Call E) × B')) s' ↔ s = s' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .nil _⟩

theorem rounds_singleton_iff {s s' : S} {r : A × List (Call E) × B'} :
    Rounds t s [r] s' ↔ (r.2.1, End.ret r.2.2 s') ∈ t.1 s r.1 := by
  constructor
  · rintro (_ | ⟨h, h'⟩)
    cases h'
    exact h
  · intro h
    exact .cons h (.nil _)

end Rounds

end Silmaril.Proofs.Games.Abstract.SessionLinkAssoc
