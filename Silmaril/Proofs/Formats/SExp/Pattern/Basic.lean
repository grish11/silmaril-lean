module

public import Silmaril.Formats.SExp.Pattern.Defs

/-! # Proofs: patterns, combinators and AST encodings -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Pattern

open Silmaril.Formats

variable {α β : Type}

theorem mem_pair {L₁ L₂ : Set (SExp α)} {x : SExp α} :
    x ∈ pair L₁ L₂ ↔ ∃ a b, x = SExp.ofList [a, b] ∧ a ∈ L₁ ∧ b ∈ L₂ := by
  constructor
  · rintro ⟨cs, rfl, h⟩
    rcases h with _ | ⟨ha, _ | ⟨hb, h⟩⟩
    cases h
    exact ⟨_, _, rfl, ha, hb⟩
  · rintro ⟨a, b, rfl, ha, hb⟩
    exact ⟨[a, b], rfl, .cons ha (.cons hb .nil)⟩

theorem tuple_inter (Ls Ms : List (Set (SExp α))) (h : Ls.length = Ms.length) :
    tuple (List.zipWith (· ∩ ·) Ls Ms) = tuple Ls ∩ tuple Ms := by
  ext x
  constructor
  · rintro ⟨cs, rfl, hc⟩
    refine ⟨⟨cs, rfl, ?_⟩, ⟨cs, rfl, ?_⟩⟩
    · induction Ls generalizing cs Ms with
      | nil => cases Ms <;> simp_all
      | cons L Ls ih =>
          cases Ms with
          | nil => simp at h
          | cons M Ms =>
              rcases hc with _ | ⟨hm, hc⟩
              exact .cons hm.1 (ih Ms (by simpa using h) _ hc)
    · induction Ls generalizing cs Ms with
      | nil => cases Ms <;> simp_all
      | cons L Ls ih =>
          cases Ms with
          | nil => simp at h
          | cons M Ms =>
              rcases hc with _ | ⟨hm, hc⟩
              exact .cons hm.2 (ih Ms (by simpa using h) _ hc)
  · rintro ⟨⟨cs, rfl, hc⟩, ⟨ds, hd, hd'⟩⟩
    have := SExp.ofList_injective hd
    subst this
    clear hd
    refine ⟨cs, rfl, ?_⟩
    induction cs generalizing Ls Ms with
    | nil => cases hc; cases hd'; exact .nil
    | cons c cs ih =>
        rcases hc with _ | ⟨hL, hc⟩
        rcases hd' with _ | ⟨hM, hd'⟩
        exact .cons ⟨hL, hM⟩ (ih _ _ (by simpa using h) hc hd')

theorem pair_inter_left (L L' M : Set (SExp α)) : pair (L ∩ L') M = pair L M ∩ pair L' M := by
  ext x
  simp only [Set.mem_inter_iff, mem_pair]
  constructor
  · rintro ⟨a, b, rfl, ⟨ha, ha'⟩, hb⟩
    exact ⟨⟨a, b, rfl, ha, hb⟩, ⟨a, b, rfl, ha', hb⟩⟩
  · rintro ⟨⟨a, b, rfl, ha, hb⟩, ⟨a', b', h, ha', -⟩⟩
    have := SExp.ofList_injective h
    simp only [List.cons.injEq] at this
    obtain ⟨rfl, rfl, -⟩ := this
    exact ⟨a, b, rfl, ⟨ha, ha'⟩, hb⟩

theorem pair_union_left (L L' M : Set (SExp α)) : pair (L ∪ L') M = pair L M ∪ pair L' M := by
  ext x
  simp only [Set.mem_union, mem_pair]
  constructor
  · rintro ⟨a, b, rfl, ha | ha, hb⟩
    · exact .inl ⟨a, b, rfl, ha, hb⟩
    · exact .inr ⟨a, b, rfl, ha, hb⟩
  · rintro (⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩)
    · exact ⟨a, b, rfl, .inl ha, hb⟩
    · exact ⟨a, b, rfl, .inr ha, hb⟩

theorem tuple_subset_star (L : Set (SExp α)) (Ls : List (Set (SExp α))) (h : ∀ M ∈ Ls, M ⊆ L) :
    tuple Ls ⊆ star L := by
  rintro x ⟨cs, rfl, hc⟩
  refine ⟨cs, rfl, ?_⟩
  induction hc with
  | nil => simp
  | cons hm _ ih =>
      intro c hcm
      rcases List.mem_cons.1 hcm with rfl | hcm
      · exact h _ List.mem_cons_self hm
      · exact ih (fun M hM => h M (List.mem_cons_of_mem _ hM)) c hcm

theorem pat_lang_ground : ∀ e : SExp α, Pat.lang (Pat.ground e) = {e} := by
  intro e
  induction e with
  | atom a => rfl
  | list n cs ih =>
      ext x
      simp only [Pat.ground, SExp.map, Pat.lang, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ds, rfl, h⟩
        congr 1
        funext i
        have := h i
        simp only [Pat.ground] at ih
        rw [ih i] at this
        exact this
      · rintro rfl
        refine ⟨cs, rfl, fun i => ?_⟩
        simp only [Pat.ground] at ih
        rw [ih i]; rfl

/-- Widening holes widens the language. -/
theorem pat_lang_mono {f : Set (SExp α) → Set (SExp α)} (hf : ∀ L, L ⊆ f L) :
    ∀ p : Pat α, Pat.lang p ⊆ Pat.lang (p.map (Sum.map id f)) := by
  intro p
  induction p with
  | atom a =>
      rcases a with a | L
      · exact le_rfl
      · exact hf L
  | list n ps ih =>
      rintro x ⟨cs, rfl, h⟩
      exact ⟨cs, rfl, fun i => ih i (h i)⟩

theorem encode_injective {S : AstSig} {tagEnc : S.Tag → SExp β} {argEnc : ∀ t, S.Arg t → List (SExp β)}
    (ht : Function.Injective tagEnc) (ha : ∀ t, Function.Injective (argEnc t))
    (hl : AST.ArgLenFixed argEnc) : Function.Injective (AST.encode tagEnc argEnc) := by
  intro x
  induction x with
  | atom e => exact e.elim
  | tag v n cs ih =>
      intro y hxy
      cases y with
      | atom e => exact e.elim
      | tag w m ds =>
          obtain ⟨t, a⟩ := v
          obtain ⟨t', a'⟩ := w
          simp only [AST.encode, AST.encodeWith] at hxy
          have h1 := SExp.ofList_injective hxy
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨htt, hrest⟩ := h1
          have := ht htt
          subst this
          obtain ⟨haa, hcs⟩ := List.append_inj hrest (hl t a a')
          have := ha t haa
          subst this
          have hnm : n = m := by simpa using congrArg List.length hcs
          subst hnm
          congr 1
          funext i
          apply ih i
          have := congrArg (fun l => l[i]?) hcs
          simpa [AST.encode] using this

end Silmaril.Proofs.Formats.SExp.Pattern

namespace Silmaril.Proofs.Formats.SExp.Pattern

open Silmaril.Formats

variable {α : Type}

theorem pat2_lang_ground : ∀ e : SExp2 α, Pat2.lang (Pat2.ground e) = {e}
  | .nil => rfl
  | .atom a => rfl
  | .cons x y => by
      ext z
      simp only [Pat2.ground, SExp2.map, Pat2.lang, Set.mem_singleton_iff]
      have hx := pat2_lang_ground x
      have hy := pat2_lang_ground y
      simp only [Pat2.ground] at hx hy
      rw [hx, hy]
      constructor
      · rintro ⟨a, b, rfl, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨x, y, rfl, rfl, rfl⟩

theorem pat2_lang_mono {f : Set (SExp2 α) → Set (SExp2 α)} (hf : ∀ L, L ⊆ f L) :
    ∀ p : Pat2 α, Pat2.lang p ⊆ Pat2.lang (p.map (Sum.map id f))
  | .nil => le_rfl
  | .atom (.inl a) => le_rfl
  | .atom (.inr L) => hf L
  | .cons p q => by
      rintro z ⟨a, b, rfl, ha, hb⟩
      exact ⟨a, b, rfl, pat2_lang_mono hf p ha, pat2_lang_mono hf q hb⟩

theorem patAST_lang_ground {S : AstSig} : ∀ e : AST S, PatAST.lang (PatAST.ground e) = {e} := by
  intro e
  induction e with
  | atom e => exact e.elim
  | tag v n cs ih =>
      ext x
      simp only [PatAST.ground, TExpr.map, PatAST.lang, Set.mem_singleton_iff]
      simp only [PatAST.ground] at ih
      constructor
      · rintro ⟨ds, rfl, h⟩
        congr 1
        funext i
        have := h i
        rw [ih i] at this
        exact this
      · rintro rfl
        exact ⟨cs, rfl, fun i => by rw [ih i]; rfl⟩

theorem patAST_lang_mono {S : AstSig} {f : Set (AST S) → Set (AST S)} (hf : ∀ L, L ⊆ f L) :
    ∀ p : PatAST S, PatAST.lang p ⊆ PatAST.lang (p.map f) := by
  intro p
  induction p with
  | atom L => exact hf L
  | tag v n ps ih =>
      rintro x ⟨cs, rfl, h⟩
      exact ⟨cs, rfl, fun i => ih i (h i)⟩

theorem pat2_lang_ofList : ∀ qs : List (Pat2 α),
    Pat2.lang (SExp2.ofList qs) =
      {x | ∃ xs, x = SExp2.ofList xs ∧ List.Forall₂ (fun x q => x ∈ Pat2.lang q) xs qs}
  | [] => by
      ext x
      simp only [SExp2.ofList, Pat2.lang, Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact ⟨[], rfl, .nil⟩
      · rintro ⟨xs, rfl, h⟩; cases h; rfl
  | q :: qs => by
      ext x
      simp only [SExp2.ofList, Pat2.lang, pat2_lang_ofList qs]
      constructor
      · rintro ⟨a, b, rfl, ha, xs, rfl, h⟩
        exact ⟨a :: xs, rfl, .cons ha h⟩
      · rintro ⟨xs, rfl, h⟩
        rcases h with _ | ⟨ha, h⟩
        exact ⟨_, _, rfl, ha, _, rfl, h⟩

theorem forall₂_ofFn {β γ : Type} {n : Nat} {R : β → γ → Prop} {f : Fin n → β} {g : Fin n → γ} :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) ↔ ∀ i, R (f i) (g i) := by
  rw [List.forall₂_iff_get]
  simp only [List.length_ofFn, List.get_eq_getElem, List.getElem_ofFn, true_and]
  exact ⟨fun h i => h i.1 i.2 i.2, fun h i h1 _ => h ⟨i, h1⟩⟩

/-- **Proper patterns and their dotted translation match the same trees.** -/
theorem toSExp2_image_lang : ∀ p : Pat α, SExp.toSExp2 '' Pat.lang p = Pat2.lang (Pat.toPat2 p) := by
  intro p
  induction p with
  | atom a =>
      rcases a with a | L
      · simp [Pat.lang, Pat.toPat2, Pat2.lang, SExp.toSExp2]
      · rfl
  | list n ps ih =>
      ext x
      simp only [Pat.toPat2, pat2_lang_ofList, Set.mem_image, Pat.lang]
      constructor
      · rintro ⟨_, ⟨cs, rfl, hcs⟩, rfl⟩
        refine ⟨List.ofFn fun i => SExp.toSExp2 (cs i), rfl, forall₂_ofFn.2 fun i => ?_⟩
        rw [← ih i]
        exact ⟨cs i, hcs i, rfl⟩
      · rintro ⟨xs, rfl, h⟩
        obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 h
        simp only [List.length_ofFn] at hlen
        have hc : ∀ i : Fin n, ∃ c ∈ Pat.lang (ps i), SExp.toSExp2 c = xs[i.1]'(hlen ▸ i.2) :=
          fun i => by
            have := hget i.1 (hlen ▸ i.2) (by simp)
            simp only [List.get_eq_getElem, List.getElem_ofFn] at this
            rw [← ih i] at this
            exact this
        choose cs hcs hcx using hc
        refine ⟨SExp.list n cs, ⟨cs, rfl, hcs⟩, ?_⟩
        simp only [SExp.toSExp2, hcx]
        congr 1
        apply List.ext_getElem (by simp [hlen])
        intro k h1 h2
        simp

end Silmaril.Proofs.Formats.SExp.Pattern
