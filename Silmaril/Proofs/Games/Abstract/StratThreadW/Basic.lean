module

public import Silmaril.Games.Abstract.StratThreadW.Defs
public import Silmaril.Games.Abstract.StratSession.Thms

/-!
# Threading with coherent execution witnesses: proofs

* Store determinism: the witnessed infinite plays are the infinite plays of `threadT`
  (`winfs_eq_of_storeDet`).
* The countdown triple (a local copy of the one behind `StratThread.not_coherent`, generic in
  the returned value): its trace-limit threading has an infinite play (`countdown_mem`), its
  witness threading has none (`not_mem_winfs_countdown`).
* Bisimulation: bisimilar stores have the same completed rounds up to related final stores
  (`rounds_of_isBisim`) and the same coherent sequences (`infRounds_of_isBisim`), so the same
  witnessed infinite plays (`winfs_subset_of_obsEq`).
* Relabelling the witnessed plays of a store-retaining triple (`image_lim`,
  `image_streamPlay`, `image_roundsPlay`, `mem_sinf_iff`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.StratThreadW

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratThreadW Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.StratObs (callMoves satP)

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Store determinism -/

theorem winfs_eq_of_storeDet {t : ObsTriple E S A B} {s₀ : S} (ht : StoreDet t) :
    winfs t s₀ = (threadT t s₀).inf := by
  ext I
  rw [mem_inf_iff_of_storeDet ht]
  constructor
  · rintro (⟨rs, s, a, ω, hrs, hω, rfl⟩ | h)
    · exact .inl ⟨_, s, a, ω, run_idle_iff.2 ⟨rs, rfl, hrs⟩, hω, rfl⟩
    · exact .inr h
  · rintro (⟨pre, s, a, ω, hpre, hω, rfl⟩ | h)
    · obtain ⟨rs, rfl, hrs⟩ := run_idle_iff.1 hpre
      exact .inl ⟨rs, s, a, ω, hrs, hω, rfl⟩
    · exact .inr h

/-! ## The countdown -/

namespace Counter

variable {E : Sig.{0}} {B : Type}

/-- A countdown returning `b`: from `none` a call may return to any `some n`, and from
`some (n + 1)` it returns to `some n`. -/
def countdown (b : B) : ObsTriple E (Option ℕ) PUnit B :=
  (fun s _ => {e | ∃ n, (s = none ∨ s = some (n + 1)) ∧ e = ([], .ret b (some n))},
    fun _ _ => ∅, fun _ _ => ∅)

theorem streamTake_const {α : Type} (x : α) (n : ℕ) :
    streamTake (fun _ => x) (n + 1) = x :: streamTake (fun _ => x) n := by
  simp [streamTake, List.ofFn_succ]

theorem countdown_rounds (b : B) (n : ℕ) :
    Rounds (countdown (E := E) b) (some n)
      (streamTake (fun _ => ((), ([] : List (Call E)), b)) n) (some 0) := by
  induction n with
  | zero => exact .nil _
  | succ n ih => rw [streamTake_const]; exact .cons ⟨n, .inr rfl, rfl⟩ ih

theorem countdown_mem (b : B) :
    roundsPlay (fun _ => ()) (fun _ => (([] : List (Call E)), b)) ∈
      (threadT (countdown (E := E) b) none).inf := by
  refine roundsPlay_mem fun k => ?_
  cases k with
  | zero => exact ⟨_, .nil _⟩
  | succ k =>
    refine ⟨some 0, ?_⟩
    rw [streamTake_const]
    exact .cons ⟨k, .inl rfl, rfl⟩ (countdown_rounds b k)

theorem countdown_not_infRounds (b : B) {a : ℕ → PUnit} {r : ℕ → List (Call E) × B}
    {s : ℕ → Option ℕ} : ¬ InfRounds (countdown (E := E) b) none a r s := by
  intro h
  obtain ⟨n₀, -, h₀⟩ := h.step 0
  have key : ∀ j, ∃ m, s (j + 1) = some m ∧ m + j = n₀ := by
    intro j
    induction j with
    | zero => exact ⟨n₀, by simp at h₀; exact h₀.2.2, rfl⟩
    | succ j ih =>
      obtain ⟨m, hm, hmj⟩ := ih
      obtain ⟨n, hn, hr⟩ := h.step (j + 1)
      rw [hm] at hn
      simp only [Prod.mk.injEq, End.ret.injEq] at hr
      rcases hn with hn | hn
      · cases hn
      · cases hn
        exact ⟨n, hr.2.2, by omega⟩
  obtain ⟨m, -, hm⟩ := key (n₀ + 1)
  omega

/-- The countdown has no witnessed infinite play from `none`. -/
theorem not_mem_winfs_countdown (b : B) {I : Set (List (Move E (sig1 PUnit B)))} :
    I ∉ winfs (countdown (E := E) b) none := by
  rintro (⟨rs, s, a, ω, -, hω, -⟩ | ⟨a, r, s, h, -⟩)
  · simp [countdown] at hω
  · exact countdown_not_infRounds b h

end Counter

/-! ## Bisimulation -/

section Bisim

variable {S' : Type u} {t : ObsTriple E S A B} {t' : ObsTriple E S' A B} {R : S → S' → Prop}

theorem rounds_of_isBisim (hR : IsBisim t t' R) {s : S} {s' : S'} (hs : R s s')
    {rs : List (A × List (Call E) × B)} {s₁ : S} (h : Rounds t s rs s₁) :
    ∃ s₁', Rounds t' s' rs s₁' ∧ R s₁ s₁' := by
  induction h generalizing s' with
  | nil => exact ⟨s', .nil _, hs⟩
  | cons hr _ ih =>
    obtain ⟨s₂', hr', h₂⟩ := (hR _ _ hs).ret _ _ _ _ hr
    obtain ⟨s₃', h₃, h₄⟩ := ih h₂
    exact ⟨s₃', .cons hr' h₃, h₄⟩

theorem infRounds_of_isBisim (hR : IsBisim t t' R) {s₀ : S} {s₀' : S'} (hs : R s₀ s₀')
    {a : ℕ → A} {r : ℕ → List (Call E) × B} {σ : ℕ → S} (h : InfRounds t s₀ a r σ) :
    ∃ σ', InfRounds t' s₀' a r σ' := by
  have hstep : ∀ k (x : {x // R (σ k) x}), ∃ y : {y // R (σ (k + 1)) y},
      ((r k).1, End.ret (r k).2 y.1) ∈ t'.1 x.1 (a k) := fun k x =>
    let ⟨y, hy, hR'⟩ := (hR _ _ x.2).ret _ _ _ _ (h.step k)
    ⟨⟨y, hR'⟩, hy⟩
  choose g hg using hstep
  have h0 : R (σ 0) s₀' := by rw [h.zero]; exact hs
  let f : (k : ℕ) → {x // R (σ k) x} :=
    fun k => Nat.rec (motive := fun k => {x // R (σ k) x}) ⟨s₀', h0⟩ g k
  exact ⟨fun k => (f k).1, ⟨rfl, fun k => hg k (f k)⟩⟩

theorem winfs_subset_of_obsEq {s : S} {s' : S'} (h : ObsEq t t' s s') :
    winfs t s ⊆ winfs t' s' := by
  obtain ⟨R, hR, hs⟩ := h
  rintro I (⟨rs, s₁, a, ω, hrs, hω, rfl⟩ | ⟨a, r, σ, hσ, rfl⟩)
  · obtain ⟨s₁', hrs', h₁⟩ := rounds_of_isBisim hR hs hrs
    exact .inl ⟨rs, s₁', a, ω, hrs', by rw [← (hR _ _ h₁).inf]; exact hω, rfl⟩
  · obtain ⟨σ', hσ'⟩ := infRounds_of_isBisim hR hs hσ
    exact .inr ⟨a, r, σ', hσ', rfl⟩

theorem winfs_eq_of_obsEq {s : S} {s' : S'} (h : ObsEq t t' s s') : winfs t s = winfs t' s' :=
  (winfs_subset_of_obsEq h).antisymm (winfs_subset_of_obsEq h.symm)

end Bisim

/-! ## Sessions -/

section Session

theorem map_callMoves (c : List (Call E)) :
    (callMoves c : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))).map relMove = callMoves c := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    simp only [callMoves, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]; rfl

theorem map_roundMoves (r : A × List (Call E) × (B ⊕ PUnit.{u + 1})) :
    (roundMoves r).map relMove = (sroundMoves r : List (Move E (sig1 A B))) := by
  simp [roundMoves, sroundMoves, map_callMoves, relMove, merge]

theorem map_roundsMoves (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (roundsMoves rs).map relMove = (sroundsMoves rs : List (Move E (sig1 A B))) := by
  simp [roundsMoves, sroundsMoves, List.map_flatMap, map_roundMoves]

theorem image_lim {α β : Type u} (f : α → β) (c : Chain α) :
    List.map f '' Chain.lim c = Chain.lim fun n => (c n).map f := by
  ext q
  constructor
  · rintro ⟨p, ⟨n, hp⟩, rfl⟩
    exact ⟨n, hp.map f⟩
  · rintro ⟨n, hq⟩
    refine ⟨(c n).take q.length, ⟨n, List.take_prefix _ _⟩, ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hq).symm

theorem image_streamPlay (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (a : A)
    (ω : ℕ → Call E) :
    List.map relMove '' streamPlay (roundsMoves rs) a ω =
      (streamPlay (sroundsMoves rs) a ω : Set (List (Move E (sig1 A B)))) := by
  have := image_lim (relMove (E := E) (A := A) (B := B))
    (fun k => roundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω k))
  simp only [List.map_append, List.map_cons, map_callMoves, map_roundsMoves] at this
  exact this

theorem image_roundsPlay (a : ℕ → A) (r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})) :
    List.map relMove '' roundsPlay a r = (sroundsPlay a r : Set (List (Move E (sig1 A B)))) := by
  rw [roundsPlay, image_lim]
  simp only [map_roundsMoves]
  rfl

theorem mem_sinf_iff {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}
    {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadSW t s₀).inf ↔
      (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds t s₀ a r s ∧ I = sroundsPlay a r := by
  constructor
  · rintro ⟨J, ⟨rs, s, a, ω, hrs, hω, rfl⟩ | ⟨a, r, s, hr, rfl⟩, rfl⟩
    · exact .inl ⟨rs, s, a, ω, hrs, hω, image_streamPlay rs a ω⟩
    · exact .inr ⟨a, r, s, hr, image_roundsPlay a r⟩
  · rintro (⟨rs, s, a, ω, hrs, hω, rfl⟩ | ⟨a, r, s, hr, rfl⟩)
    · exact ⟨_, .inl ⟨rs, s, a, ω, hrs, hω, rfl⟩, (image_streamPlay rs a ω).symm⟩
    · exact ⟨_, .inr ⟨a, r, s, hr, rfl⟩, (image_roundsPlay a r).symm⟩

end Session

end Silmaril.Proofs.Games.Abstract.StratThreadW
