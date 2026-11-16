module

public import Silmaril.Games.Abstract.SessionLinkAssoc.Thms

/-!
# Coherence of linking sessions (basic lemmas)

Membership in `mapStore`; functoriality of `mapStore`; `mapStore` commutes with `sat` and
`dropTrap`; session rounds, coherent services and call prefixes are transported along a store
equivalence.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCoh

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionLinkAssoc

universe u

variable {E : Sig.{u}} {S S' S'' A B : Type u}

theorem obsTriple_ext {t t' : ObsTriple E S A B} (h₁ : ∀ s a x, x ∈ t.1 s a ↔ x ∈ t'.1 s a)
    (h₂ : ∀ s a x, x ∈ t.2.1 s a ↔ x ∈ t'.2.1 s a)
    (h₃ : ∀ s a x, x ∈ t.2.2 s a ↔ x ∈ t'.2.2 s a) : t = t' :=
  Prod.ext (funext fun s => funext fun a => Set.ext (h₁ s a))
    (Prod.ext (funext fun s => funext fun a => Set.ext (h₂ s a))
      (funext fun s => funext fun a => Set.ext (h₃ s a)))

/-! ## Ends -/

theorem mapEnd_mapEnd (e : S → S') (e' : S' → S'') (x : End S B) :
    mapEnd e' (mapEnd e x) = mapEnd (e' ∘ e) x := by
  cases x <;> rfl

theorem mapEnd_id (x : End S B) : mapEnd id x = x := by
  cases x <;> rfl

@[simp] theorem mapEnd_symm_mapEnd (e : S ≃ S') (x : End S B) :
    mapEnd e.symm (mapEnd e x) = x := by
  cases x <;> simp [mapEnd]

@[simp] theorem mapEnd_mapEnd_symm (e : S ≃ S') (x : End S' B) :
    mapEnd e (mapEnd e.symm x) = x := by
  cases x <;> simp [mapEnd]

theorem mapEnd_eq_trap {e : S → S'} {x : End S B} : mapEnd e x = End.trap ↔ x = End.trap := by
  cases x <;> simp [mapEnd]

/-! ## Membership -/

theorem mem_mapStore_fst {e : S ≃ S'} {t : ObsTriple E S A B} {s : S'} {a : A}
    {x : List (Call E) × End S' B} :
    x ∈ (mapStore e t).1 s a ↔ (x.1, mapEnd e.symm x.2) ∈ t.1 (e.symm s) a := by
  simp only [mapStore, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem mem_mapStore_ret {e : S ≃ S'} {t : ObsTriple E S A B} {s : S'} {a : A}
    {c : List (Call E)} {b : B} {s₁ : S'} :
    (c, End.ret b s₁) ∈ (mapStore e t).1 s a ↔ (c, End.ret b (e.symm s₁)) ∈ t.1 (e.symm s) a :=
  mem_mapStore_fst

theorem mem_mapStore_div {e : S ≃ S'} {t : ObsTriple E S A B} {s : S'} {a : A}
    {c : List (Call E)} :
    (c, (End.div : End S' B)) ∈ (mapStore e t).1 s a ↔ (c, End.div) ∈ t.1 (e.symm s) a :=
  mem_mapStore_fst

/-! ## Functoriality -/

theorem mapStore_refl (t : ObsTriple E S A B) : mapStore (Equiv.refl S) t = t := by
  refine obsTriple_ext (fun s a x => ?_) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
  rw [mem_mapStore_fst]
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  rw [show (⇑(Equiv.refl S) : S → S) = id from rfl, mapEnd_id]

theorem mapStore_trans (e : S ≃ S') (e' : S' ≃ S'') (t : ObsTriple E S A B) :
    mapStore (e.trans e') t = mapStore e' (mapStore e t) := by
  refine obsTriple_ext (fun s a x => ?_) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
  rw [mem_mapStore_fst, mem_mapStore_fst, mem_mapStore_fst, mapEnd_mapEnd]
  rfl

/-! ## Saturation and plain traps -/

theorem satP_mapStore (e : S ≃ S') (t : ObsTriple E S A B) (s : S') (a : A) :
    satP (mapStore e t) s a = satP t (e.symm s) a := by
  ext x
  simp only [satP, Set.mem_ofPred_eq]
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ Iff.rfl))
  · constructor
    · rintro ⟨d, en, h, hc⟩
      exact ⟨d, _, mem_mapStore_fst.1 h, hc⟩
    · rintro ⟨d, en, h, hc⟩
      exact ⟨d, mapEnd e en, mem_mapStore_fst.2 (by simpa using h), hc⟩

theorem sat_mapStore (e : S ≃ S') (t : ObsTriple E S A B) :
    sat (mapStore e t) = mapStore e (sat t) := by
  refine obsTriple_ext (fun _ _ _ => Iff.rfl) (fun s a x => ?_) (fun _ _ _ => Iff.rfl)
  change x ∈ satP (mapStore e t) s a ↔ x ∈ satP t (e.symm s) a
  rw [satP_mapStore]

theorem dropTrap_mapStore (e : S ≃ S') (t : ObsTriple E S A B) :
    dropTrap (mapStore e t) = mapStore e (dropTrap t) := by
  refine obsTriple_ext (fun s a x => ?_) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
  rw [mem_mapStore_fst]
  simp only [dropTrap, Set.mem_ofPred_eq, mem_mapStore_fst, ne_eq, mapEnd_eq_trap]

/-! ## Rounds, services and call prefixes along a store equivalence -/

theorem rounds_mapStore_of {e : S ≃ S'} {t : ObsTriple E S A B} {s : S'}
    {rs : List (A × List (Call E) × B)} {s₁ : S'} (h : Rounds (mapStore e t) s rs s₁) :
    Rounds t (e.symm s) rs (e.symm s₁) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (mem_mapStore_ret.1 h) ih

theorem rounds_mapStore_to {e : S ≃ S'} {t : ObsTriple E S A B} {s : S}
    {rs : List (A × List (Call E) × B)} {s₁ : S} (h : Rounds t s rs s₁) :
    Rounds (mapStore e t) (e s) rs (e s₁) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (mem_mapStore_ret.2 (by simpa using h)) ih

theorem rounds_mapStore {e : S ≃ S'} {t : ObsTriple E S A B} {s : S'}
    {rs : List (A × List (Call E) × B)} {s₁ : S'} :
    Rounds (mapStore e t) s rs s₁ ↔ Rounds t (e.symm s) rs (e.symm s₁) :=
  ⟨rounds_mapStore_of, fun h => by simpa using rounds_mapStore_to (e := e) h⟩

variable {B₀ : Type u}

theorem infServe_mapStore_of {e : S ≃ S'} {t : ObsTriple E S A (B₀ ⊕ PUnit.{u + 1})} {s : S'}
    {ω : ℕ → Call (sig1 A B₀)} {l : ℕ → List (Call E)} {st : ℕ → S'}
    (h : InfServe (mapStore e t) s ω l st) : InfServe t (e.symm s) ω l (fun k => e.symm (st k)) :=
  ⟨by rw [h.zero], fun k => mem_mapStore_ret.1 (h.step k)⟩

theorem infServe_mapStore_to {e : S ≃ S'} {t : ObsTriple E S A (B₀ ⊕ PUnit.{u + 1})} {s : S}
    {ω : ℕ → Call (sig1 A B₀)} {l : ℕ → List (Call E)} {st : ℕ → S}
    (h : InfServe t s ω l st) : InfServe (mapStore e t) (e s) ω l (fun k => e (st k)) :=
  ⟨by rw [h.zero], fun k => mem_mapStore_ret.2 (by simpa using h.step k)⟩

/-! ## Congruence of `linkS` in the server -/

theorem rounds_congr {t t' : ObsTriple E S A B}
    (h : ∀ s a c b s₁, (c, End.ret b s₁) ∈ t.1 s a ↔ (c, End.ret b s₁) ∈ t'.1 s a) :
    Rounds t = Rounds t' := by
  have key : ∀ {t t' : ObsTriple E S A B},
      (∀ s a c b s₁, (c, End.ret b s₁) ∈ t.1 s a → (c, End.ret b s₁) ∈ t'.1 s a) →
      ∀ {s rs s₁}, Rounds t s rs s₁ → Rounds t' s rs s₁ := by
    intro t t' h s rs s₁ hr
    induction hr with
    | nil => exact .nil _
    | cons hm _ ih => exact .cons (h _ _ _ _ _ hm) ih
  funext s rs s₁
  exact propext ⟨key fun s a c b s₁ => (h s a c b s₁).1, key fun s a c b s₁ => (h s a c b s₁).2⟩

theorem infServe_congr {t t' : ObsTriple E S A (B₀ ⊕ PUnit.{u + 1})}
    (h : ∀ s a c b s₁, (c, End.ret b s₁) ∈ t.1 s a ↔ (c, End.ret b s₁) ∈ t'.1 s a) :
    InfServe t = InfServe t' := by
  funext s ω l st
  exact propext ⟨fun hs => ⟨hs.zero, fun k => (h _ _ _ _ _).1 (hs.step k)⟩,
    fun hs => ⟨hs.zero, fun k => (h _ _ _ _ _).2 (hs.step k)⟩⟩

end Silmaril.Proofs.Games.Abstract.SessionLinkCoh
