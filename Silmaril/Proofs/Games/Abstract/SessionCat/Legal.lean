module

public import Silmaril.Proofs.Games.Abstract.SessionCat.Det
public import Silmaril.Games.Abstract.SessionPair.Thms
public import Silmaril.Games.Abstract.StratLegal.Defs

/-!
# Session-level category laws: legality (proofs)

The logs of the linked triple are concatenations of logs of the server (served rounds, a server
divergence, the rounds of hidden chatter, call prefixes of the server, server streams), so a legal
server gives a legal linked triple (`legal_linkS`); the answers of the linked triple are those of
the client (`ansLegal_linkS`). The client calls served by a server with legal answers are legal
(`logLegal_served`), so only the legal part of the (saturated) client matters
(`linkS_legalPart`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {L : (m : E.Op) → E.Ar m → Prop}

theorem logLegal_append {c d : List (Call E)} :
    LogLegal L (c ++ d) ↔ LogLegal L c ∧ LogLegal L d := by
  simp only [LogLegal, List.mem_append, or_imp, forall_and]

theorem logLegal_streamTake {ω : ℕ → Call E} (h : ∀ k, L (ω k).1 (ω k).2) (n : ℕ) :
    LogLegal L (streamTake ω n) := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact h i

theorem mem_streamTake {α : Type u} (ω : ℕ → α) {i n : ℕ} (h : i < n) : ω i ∈ streamTake ω n :=
  List.mem_ofFn.2 ⟨⟨i, h⟩, rfl⟩

theorem logLegal_logTake {l : ℕ → List (Call E)} (h : ∀ k, LogLegal L (l k)) (n : ℕ) :
    LogLegal L (logTake l n) := by
  intro x hx
  obtain ⟨_, hl, hx⟩ := List.mem_flatten.1 hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
  exact h i x hx

variable {S A B : Type u}

/-- Call prefixes of a legal triple have legal logs. -/
theorem logLegal_satP {t : ObsTriple E S A B} (ht : Legal L t) {s : S} {a : A}
    {x : List (Call E) × E.Op} (h : x ∈ satP t s a) : LogLegal L x.1 := by
  rcases h with h | ⟨d, m', hd, n, c', hc⟩ | ⟨d, e, hd, n, c', hc⟩ | ⟨ω, hω, k, hk, -⟩
  · exact ht.2.1 _ _ _ h
  · exact (logLegal_append.1 (hc ▸ ht.2.1 _ _ _ hd)).1
  · exact (logLegal_append.1 (hc ▸ ht.1 _ _ _ hd)).1
  · exact hk ▸ logLegal_streamTake (ht.2.2 _ _ _ hω) k

variable {S' A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

theorem logLegal_servedLog (ht : ∀ s a x, x ∈ t.1 s a → LogLegal L x.1) {s s₁ : S}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} (h : Rounds t s rs s₁) :
    LogLegal L (servedLog rs) := by
  induction h with
  | nil => intro _ h; simp [servedLog] at h
  | cons hr _ ih =>
    simp only [servedLog, List.flatMap_cons] at ih ⊢
    exact logLegal_append.2 ⟨ht _ _ _ hr, ih⟩

/-- **Linking with a legal server is legal.** -/
theorem legal_linkS (ht : Legal L t) : Legal L (linkS t u) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro σ a' x (⟨rs, s₁, e, hR, -, rfl⟩ | ⟨rs, s₁, a, c, hR, -, hc, rfl⟩ |
      ⟨ω, -, l, st, n, hI, -, rfl⟩)
    · exact logLegal_servedLog ht.1 hR
    · exact logLegal_append.2 ⟨logLegal_servedLog ht.1 hR, ht.1 _ _ _ hc⟩
    · exact logLegal_logTake (fun k => ht.1 _ _ _ (hI.step k)) n
  · rintro σ a' x ⟨rs, s₁, a, c, hR, -, hc, hx⟩
    rw [hx]
    exact logLegal_append.2 ⟨logLegal_servedLog ht.1 hR, logLegal_satP ht hc⟩
  · rintro σ a' ω (⟨rs, s₁, a, ω', hR, -, hω', hk⟩ | ⟨ω', -, l, st, hI, hunb, hk⟩) i
    · have hmem := mem_streamTake ω (n := (servedLog rs).length + (i + 1)) (i := i) (by omega)
      rw [hk] at hmem
      rcases List.mem_append.1 hmem with h | h
      · exact logLegal_servedLog ht.1 hR _ h
      · exact logLegal_streamTake (ht.2.2 _ _ _ hω') _ _ h
    · obtain ⟨k, hk'⟩ := hunb (i + 1)
      have hmem := mem_streamTake ω (n := (logTake l k).length) (i := i) (by omega)
      rw [hk] at hmem
      exact logLegal_logTake (fun k => ht.1 _ _ _ (hI.step k)) k _ hmem

/-- **The answers of a linked triple are the client's.** -/
theorem ansLegal_linkS {L' : A' → B' ⊕ PUnit.{u + 1} → Prop} (hu : AnsLegal L' u) :
    AnsLegal L' (linkS t u) := by
  rintro σ a' c y σ₁ (⟨rs, s₁, e, -, he, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩ |
    ⟨_, _, _, _, _, _, _, hx⟩)
  · obtain ⟨rfl, -⟩ := linkEnd_eq_ret (Prod.ext_iff.1 hx).2.symm
    exact hu _ _ _ _ _ he
  · cases (Prod.ext_iff.1 hx).2
  · cases (Prod.ext_iff.1 hx).2

/-- **Calls served by a server with legal answers are legal.** -/
theorem logLegal_served {L₁ : A → B ⊕ PUnit.{u + 1} → Prop} (ht : AnsLegal L₁ t) {s s₁ : S}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} (h : Rounds t s rs s₁) :
    LogLegal (E := sig1 A B) L₁ (served rs) := by
  induction h with
  | nil => intro _ h; simp [served] at h
  | cons hr _ ih =>
    intro x hx
    simp only [served, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ht _ _ _ _ _ hr
    · exact ih x hx

theorem satP_legalPart_sat {S₀ A₀ B₀ : Type u} {L₀ : (m : E.Op) → E.Ar m → Prop}
    {v : ObsTriple E S₀ A₀ B₀} {s : S₀} {a : A₀} {x : List (Call E) × E.Op} :
    x ∈ satP (legalPart L₀ (sat v)) s a ↔ x ∈ satP v s a ∧ LogLegal L₀ x.1 := by
  obtain ⟨c, m⟩ := x
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h with ⟨h, -⟩ | ⟨d, m', ⟨hd, -⟩, hc⟩ | ⟨d, e, ⟨hd, -⟩, hc⟩ | ⟨ω, ⟨hω, -⟩, k, hk, hm⟩
      · exact h
      · exact satP_prefix hd hc
      · exact .inr (.inr (.inl ⟨d, e, hd, hc⟩))
      · exact .inr (.inr (.inr ⟨ω, hω, k, hk, hm⟩))
    · rcases h with ⟨-, h⟩ | ⟨d, m', ⟨-, hd⟩, n, c', hc⟩ | ⟨d, e, ⟨-, hd⟩, n, c', hc⟩ |
        ⟨ω, ⟨-, hω⟩, k, hk, -⟩
      · exact h
      · exact (logLegal_append.1 (hc ▸ hd)).1
      · exact (logLegal_append.1 (hc ▸ hd)).1
      · exact hk ▸ logLegal_streamTake hω k
  · rintro ⟨h, hl⟩
    exact .inl ⟨h, hl⟩

/-- **Only the legal part of the client is exercised** by a server with legal answers. -/
theorem linkS_legalPart {L₁ : A → B ⊕ PUnit.{u + 1} → Prop} (ht : AnsLegal L₁ t) :
    linkS t (legalPart (E := sig1 A B) L₁ (sat u)) = linkS t u := by
  have hP : ∀ {σ' a' s s₁ rs a}, Rounds t s rs s₁ →
      ((served rs, a) ∈ satP (legalPart (E := sig1 A B) L₁ (sat u)) σ' a' ↔
        (served rs, a) ∈ satP u σ' a') := fun hR =>
    satP_legalPart_sat.trans (and_iff_left (logLegal_served ht hR))
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext σ a' <;> ext x
  · constructor
    · rintro (⟨rs, s₁, e, hR, ⟨hb, -⟩, rfl⟩ | ⟨rs, s₁, a, c, hR, hp, hc, rfl⟩ |
        ⟨ω, ⟨hω, -⟩, l, st, n, hI, hn, rfl⟩)
      · exact .inl ⟨rs, s₁, e, hR, hb, rfl⟩
      · exact .inr (.inl ⟨rs, s₁, a, c, hR, (hP hR).1 hp, hc, rfl⟩)
      · exact .inr (.inr ⟨ω, hω, l, st, n, hI, hn, rfl⟩)
    · rintro (⟨rs, s₁, e, hR, hb, rfl⟩ | ⟨rs, s₁, a, c, hR, hp, hc, rfl⟩ |
        ⟨ω, hω, l, st, n, hI, hn, rfl⟩)
      · exact .inl ⟨rs, s₁, e, hR, ⟨hb, logLegal_served ht hR⟩, rfl⟩
      · exact .inr (.inl ⟨rs, s₁, a, c, hR, (hP hR).2 hp, hc, rfl⟩)
      · exact .inr (.inr ⟨ω, ⟨hω, fun k => ht _ _ _ _ _ (hI.step k)⟩, l, st, n, hI, hn, rfl⟩)
  · constructor
    · rintro ⟨rs, s₁, a, c, hR, hp, hc, hx⟩
      exact ⟨rs, s₁, a, c, hR, (hP hR).1 hp, hc, hx⟩
    · rintro ⟨rs, s₁, a, c, hR, hp, hc, hx⟩
      exact ⟨rs, s₁, a, c, hR, (hP hR).2 hp, hc, hx⟩
  · constructor
    · rintro (⟨rs, s₁, a, ω', hR, hp, hω', hk⟩ | ⟨ω', ⟨hω', -⟩, l, st, hI, hunb, hk⟩)
      · exact .inl ⟨rs, s₁, a, ω', hR, (hP hR).1 hp, hω', hk⟩
      · exact .inr ⟨ω', hω', l, st, hI, hunb, hk⟩
    · rintro (⟨rs, s₁, a, ω', hR, hp, hω', hk⟩ | ⟨ω', hω', l, st, hI, hunb, hk⟩)
      · exact .inl ⟨rs, s₁, a, ω', hR, (hP hR).2 hp, hω', hk⟩
      · exact .inr ⟨ω', ⟨hω', fun k => ht _ _ _ _ _ (hI.step k)⟩, l, st, hI, hunb, hk⟩

/-- **The legal play object sees only the legal part.** -/
theorem restrict_legalPart {S₀ A₀ B₀ : Type u} (v : ObsTriple E S₀ A₀ B₀) :
    StratLegal.restrict L (legalPart L v) = StratLegal.restrict L v := by
  have hl : ∀ c : List (Call (StratLegal.legalSig E L)),
      LogLegal L (c.map StratLegal.liftCall) := by
    intro c x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact y.2.2
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext s a <;> ext x
  · exact and_iff_left (hl _)
  · exact and_iff_left (hl _)
  · exact and_iff_left fun k => (x k).2.2

section Pair

variable {S₁ S₂ A₁ A₂ B₁ B₂ : Type u} {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
  {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}

/-- **Pairing legal triples is legal.** -/
theorem legal_pairS (h₁ : Legal L t₁) (h₂ : Legal L t₂) : Legal L (pairS t₁ t₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro σ (a | a) x hx
    · obtain ⟨e, he, -⟩ := mem_pairS_inl.1 hx
      exact h₁.1 _ _ _ he
    · obtain ⟨e, he, -⟩ := mem_pairS_inr.1 hx
      exact h₂.1 _ _ _ he
  · rintro σ (a | a) x hx
    · exact h₁.2.1 _ _ _ hx
    · exact h₂.2.1 _ _ _ hx
  · rintro σ (a | a) ω hω
    · exact h₁.2.2 _ _ _ hω
    · exact h₂.2.2 _ _ _ hω

/-- **The answers of a paired triple are those of its components.** -/
theorem ansLegal_pairS {L₁ : A₁ → B₁ ⊕ PUnit.{u + 1} → Prop} {L₂ : A₂ → B₂ ⊕ PUnit.{u + 1} → Prop}
    (h₁ : AnsLegal L₁ t₁) (h₂ : AnsLegal L₂ t₂) : AnsLegal (pairAns L₁ L₂) (pairS t₁ t₂) := by
  rintro σ (a | a) c x σ₁ hx
  · obtain ⟨e, he, hex⟩ := mem_pairS_inl.1 hx
    cases e with
    | ret y s =>
      simp only [pairEndL, End.ret.injEq] at hex
      exact ⟨y, h₁ _ _ _ _ _ he, hex.1⟩
    | trap => cases hex
    | div => cases hex
  · obtain ⟨e, he, hex⟩ := mem_pairS_inr.1 hx
    cases e with
    | ret y s =>
      simp only [pairEndR, End.ret.injEq] at hex
      exact ⟨y, h₂ _ _ _ _ _ he, hex.1⟩
    | trap => cases hex
    | div => cases hex

end Pair

end Silmaril.Proofs.Games.Abstract.SessionCat
