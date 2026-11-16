module

public import Silmaril.Games.Abstract.IterUniform.Defs
import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Uniformity along silent maps: the shape of the map and of the hypothesis (proofs)

A silent, deterministic, trap-free, defined map diverges silently or returns one result in one
state (`shape`). Sequencing after it is the second function at that result and state
(`mem_seq_ret`, `seq_inf_ret`), or silent divergence (`mem_seq_div`, `seq_inf_div`).

Under the uniformity hypothesis `h ; F = G ; [inl, inr ∘ h]`, where `h` returns `(x, t)` at
`(s, a)`, the behaviours of `F` at `(t, x)` are those of `G` at `(s, a)`, a continuation
`inr a₁` in `s₁` of `G` becoming the continuation `h (s₁, a₁)` of `F`, or a divergence if `h`
diverges there (`exit_iff`, `trap_iff`, `div_iff`, `cont_iff`, `inf_eq`). Where `h`
diverges, `G` only diverges silently or continues silently to points where `h` diverges, and
has no productive run (`of_div`, `inf_div`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniform

open Silmaril.Games Silmaril.Games.Abstract

universe u v

variable {E : Sig.{u}} {S A A' B C : Type u}

/-- `h` returns `x` in state `t` at `(s, a)`, silently and as its only behaviour. -/
def RetAt (h : FullFun E S A' A) (s : S) (a : A') (x : A) (t : S) : Prop :=
  h.1 s a = {([], End.ret x t)}

/-- `h` diverges silently at `(s, a)`, as its only behaviour. -/
def DivAt (h : FullFun E S A' A) (s : S) (a : A') : Prop := h.1 s a = {([], End.div)}

/-- **Dependent choice** along a sequence of predicates. -/
theorem exists_chain {α : Type v} (Q : ℕ → α → Prop) (R : ℕ → α → α → Prop)
    (hs : ∀ n p, Q n p → ∃ p', R n p p' ∧ Q (n + 1) p') {p₀ : α} (h₀ : Q 0 p₀) :
    ∃ σ : ℕ → α, σ 0 = p₀ ∧ ∀ n, Q n (σ n) ∧ R n (σ n) (σ (n + 1)) := by
  let g : (n : ℕ) → {p // Q n p} := fun n =>
    Nat.rec (motive := fun n => {p // Q n p}) ⟨p₀, h₀⟩
      (fun n p => ⟨Classical.choose (hs n p.1 p.2), (Classical.choose_spec (hs n p.1 p.2)).2⟩) n
  exact ⟨fun n => (g n).1, rfl,
    fun n => ⟨(g n).2, (Classical.choose_spec (hs n (g n).1 (g n).2)).1⟩⟩

section Shape

variable {h : FullFun E S A' A}

/-- **The shape of a silent, deterministic, trap-free, defined map.** -/
theorem shape (hh : FullFun.SilentDetNoTrap h) (s : S) (a : A') :
    DivAt h s a ∨ ∃ x t, RetAt h s a x t := by
  obtain ⟨⟨-, hs1⟩, hdet, hnt, hne⟩ := hh
  obtain ⟨⟨c, e⟩, hm⟩ := hne s a
  have hc : c = [] := hs1 s a _ hm
  subst hc
  have hset : h.1 s a = {([], e)} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hm, fun y hy => ?_⟩
    obtain ⟨c', e'⟩ := y
    have hc' : c' = [] := hs1 s a _ hy
    subst hc'
    have hag : e' = e := hdet s a _ _ hy hm
    rw [hag]
  cases e with
  | ret x t => exact .inr ⟨x, t, hset⟩
  | trap => exact absurd ⟨[], hm⟩ (hnt s a)
  | div => exact .inl hset

theorem not_ret_div {s : S} {a : A'} {x : A} {t : S} (hr : RetAt h s a x t) (hd : DivAt h s a) :
    False := by
  have : ([], End.ret x t) ∈ h.1 s a := hr ▸ rfl
  rw [hd] at this
  cases (Prod.mk.inj this).2

theorem retAt_unique {s : S} {a : A'} {x x' : A} {t t' : S} (hr : RetAt h s a x t)
    (hr' : RetAt h s a x' t') : x = x' ∧ t = t' := by
  have : ([], End.ret x t) ∈ h.1 s a := hr ▸ rfl
  rw [hr'] at this
  cases (Prod.mk.inj this).2
  exact ⟨rfl, rfl⟩

/-- Membership in a silent deterministic map determines it. -/
theorem retAt_of_mem (hh : FullFun.SilentDetNoTrap h) {s : S} {a : A'} {x : A} {t : S}
    (hm : ([], End.ret x t) ∈ h.1 s a) : RetAt h s a x t := by
  rcases shape hh s a with hd | ⟨x', t', hr⟩
  · rw [hd] at hm; cases (Prod.mk.inj hm).2
  · rw [hr] at hm
    cases (Prod.mk.inj hm).2
    exact hr

theorem divAt_of_mem (hh : FullFun.SilentDetNoTrap h) {s : S} {a : A'}
    (hm : ([], End.div) ∈ h.1 s a) : DivAt h s a := by
  rcases shape hh s a with hd | ⟨x', t', hr⟩
  · exact hd
  · rw [hr] at hm; cases (Prod.mk.inj hm).2

/-- After a return of `h`, sequencing is the second function. -/
theorem mem_seq_ret {X : FullFun E S A C} {s : S} {a : A'} {x : A} {t : S}
    (hr : RetAt h s a x t) (y : CallBeh E S C) :
    y ∈ (FullFun.seq h X).1 s a ↔ y ∈ X.1 t x := by
  constructor
  · rintro (⟨c, hc, -⟩ | ⟨c, hc, -⟩ | ⟨c₁, b, s₁, c₂, e, hc, hm, rfl⟩)
    · rw [hr] at hc; cases (Prod.mk.inj hc).2
    · rw [hr] at hc; cases (Prod.mk.inj hc).2
    · rw [hr] at hc
      obtain ⟨rfl, he⟩ := Prod.mk.inj hc
      cases he
      exact hm
  · intro hm
    exact .inr (.inr ⟨[], x, t, y.1, y.2, hr ▸ rfl, hm, rfl⟩)

/-- After a divergence of `h`, sequencing diverges. -/
theorem mem_seq_div {X : FullFun E S A C} {s : S} {a : A'} (hd : DivAt h s a)
    (y : CallBeh E S C) : y ∈ (FullFun.seq h X).1 s a ↔ y = ([], End.div) := by
  constructor
  · rintro (⟨c, hc, -⟩ | ⟨c, hc, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hc, -, -⟩)
    · rw [hd] at hc; cases (Prod.mk.inj hc).2
    · rw [hd] at hc; rw [(Prod.mk.inj hc).1]
    · rw [hd] at hc; cases (Prod.mk.inj hc).2
  · rintro rfl
    exact .inr (.inl ⟨[], hd ▸ rfl, rfl⟩)

theorem seq_inf_ret (hh : FullFun.SilentDetNoTrap h) {X : FullFun E S A C} {s : S} {a : A'}
    {x : A} {t : S} (hr : RetAt h s a x t) : (FullFun.seq h X).2 s a = X.2 t x := by
  ext ω
  constructor
  · rintro (hω | ⟨c, b, s₁, ω', hc, hω, rfl⟩)
    · rw [hh.1.1 s a] at hω; exact hω.elim
    · rw [hr] at hc
      obtain ⟨rfl, he⟩ := Prod.mk.inj hc
      cases he
      exact hω
  · intro hω
    exact .inr ⟨[], x, t, ω, hr ▸ rfl, hω, rfl⟩

theorem seq_inf_div (hh : FullFun.SilentDetNoTrap h) {X : FullFun E S A C} {s : S} {a : A'}
    (hd : DivAt h s a) : (FullFun.seq h X).2 s a = ∅ := by
  ext ω
  constructor
  · rintro (hω | ⟨c, b, s₁, ω', hc, -, -⟩)
    · rw [hh.1.1 s a] at hω; exact hω
    · rw [hd] at hc; cases (Prod.mk.inj hc).2
  · intro hω; exact hω.elim


/-- **Characterisation**: one silent divergence or one silent return, and no productive run. -/
theorem silentDetNoTrap_iff :
    FullFun.SilentDetNoTrap h ↔
      ∀ s a, h.2 s a = ∅ ∧ (DivAt h s a ∨ ∃ x t, RetAt h s a x t) := by
  constructor
  · exact fun hh s a => ⟨hh.1.1 s a, shape hh s a⟩
  · intro H
    have hsing : ∀ s a, ∃ e : End S A, h.1 s a = {([], e)} := fun s a => by
      rcases (H s a).2 with hd | ⟨x, t, hr⟩
      · exact ⟨_, hd⟩
      · exact ⟨_, hr⟩
    refine ⟨⟨fun s a => (H s a).1, fun s a y hy => ?_⟩, fun s a y z hy hz => ?_, fun s a => ?_,
      fun s a => ?_⟩
    · obtain ⟨e, he⟩ := hsing s a
      rw [he] at hy
      rw [hy]
    · obtain ⟨e, he⟩ := hsing s a
      rw [he] at hy hz
      rw [hy, hz]
      exact (rfl : e = e)
    · rintro ⟨c, hc⟩
      rcases (H s a).2 with hd | ⟨x, t, hr⟩
      · rw [hd] at hc; cases (Prod.mk.inj hc).2
      · rw [hr] at hc; cases (Prod.mk.inj hc).2
    · obtain ⟨e, he⟩ := hsing s a
      rw [he]
      exact Set.singleton_nonempty _

/-- **Characterisation**: one silent return, and no productive run. -/
theorem silentTotalDet_iff :
    FullFun.SilentTotalDet h ↔ ∀ s a, h.2 s a = ∅ ∧ ∃ x t, RetAt h s a x t := by
  constructor
  · rintro ⟨hs, hdet, hret⟩
    have hh : FullFun.SilentDetNoTrap h :=
      ⟨hs, hdet, fun s a ⟨c, hc⟩ => (hret s a).2 _ hc trivial, fun s a => (hret s a).1⟩
    intro s a
    refine ⟨hs.1 s a, ?_⟩
    rcases shape hh s a with hd | hr
    · exact ((hret s a).2 ([], .div) (by rw [hd]; rfl) trivial).elim
    · exact hr
  · intro H
    have hh : FullFun.SilentDetNoTrap h := silentDetNoTrap_iff.2 fun s a =>
      ⟨(H s a).1, .inr (H s a).2⟩
    refine ⟨hh.1, hh.2.1, fun s a => ⟨hh.2.2.2 s a, fun y hy => ?_⟩⟩
    obtain ⟨x, t, hr⟩ := (H s a).2
    rw [hr] at hy
    rw [hy]
    exact id

/-- A silent, total, deterministic map is silent, deterministic, trap-free and defined. -/
theorem silentDetNoTrap_of_silentTotalDet (hh : FullFun.SilentTotalDet h) :
    FullFun.SilentDetNoTrap h :=
  silentDetNoTrap_iff.2 fun s a => ⟨(silentTotalDet_iff.1 hh s a).1,
    .inr (silentTotalDet_iff.1 hh s a).2⟩

end Shape

/-! ## The uniformity hypothesis, pointwise -/

/-- The copairing `[inl, inr ∘ h]`. -/
abbrev caseK (h : FullFun E S A' A) : FullFun E S (B ⊕ A') (B ⊕ A) :=
  FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)

theorem mem_caseK_inl {h : FullFun E S A' A} {s₁ : S} {b : B} {c : List (Call E)}
    {e : End S (B ⊕ A)} : (c, e) ∈ (caseK h).1 s₁ (.inl b) ↔ c = [] ∧ e = .ret (.inl b) s₁ := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨([], .ret b s₁), rfl, rfl⟩

theorem mem_caseK_inr {h : FullFun E S A' A} {s₁ : S} {a₁ : A'} {c : List (Call E)}
    {e : End S (B ⊕ A)} :
    (c, e) ∈ (caseK h).1 s₁ (.inr a₁) ↔
      ∃ e₀, (c, e₀) ∈ h.1 s₁ a₁ ∧ e = FullFun.endMap Sum.inr e₀ := by
  constructor
  · rintro ⟨⟨c₀, e₀⟩, hy, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨e₀, hy, rfl⟩
  · rintro ⟨e₀, hy, rfl⟩
    exact ⟨(c, e₀), hy, rfl⟩

section Hyp

variable {h : FullFun E S A' A} {F : FullFun E S A (B ⊕ A)} {G : FullFun E S A' (B ⊕ A')}
  (hh : FullFun.SilentDetNoTrap h) (hFG : FullFun.seq h F = FullFun.seq G (caseK h))
include hh hFG

omit hh in
theorem mem_hyp (s : S) (a : A') (y : CallBeh E S (B ⊕ A)) :
    y ∈ (FullFun.seq h F).1 s a ↔ y ∈ (FullFun.seq G (caseK h)).1 s a := by
  rw [hFG]

/-- The productive runs of `G ; [inl, inr ∘ h]` are those of `G`. -/
theorem inf_hyp (s : S) (a : A') : (FullFun.seq h F).2 s a = G.2 s a := by
  rw [hFG]
  ext ω
  constructor
  · rintro (hω | ⟨c, b, s₁, ω', -, hω, -⟩)
    · exact hω
    · cases b with
      | inl b => exact hω.elim
      | inr b =>
        have hω' : ω' ∈ h.2 s₁ b := hω
        rw [hh.1.1 s₁ b] at hω'
        exact hω'.elim
  · exact .inl

omit hFG in
/-- A behaviour of `G ; [inl, inr ∘ h]`, by cases. -/
theorem mem_seqK {s : S} {a : A'} {y : CallBeh E S (B ⊕ A)} :
    y ∈ (FullFun.seq G (caseK h)).1 s a ↔
      (∃ c, (c, End.trap) ∈ G.1 s a ∧ y = (c, End.trap)) ∨
      (∃ c, (c, End.div) ∈ G.1 s a ∧ y = (c, End.div)) ∨
      (∃ c b s', (c, End.ret (.inl b) s') ∈ G.1 s a ∧ y = (c, End.ret (.inl b) s')) ∨
      (∃ c a₁ s₁, (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ DivAt h s₁ a₁ ∧ y = (c, End.div)) ∨
      ∃ c a₁ s₁ x' t', (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ RetAt h s₁ a₁ x' t' ∧
        y = (c, End.ret (.inr x') t') := by
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c₁, b₁, s₁, c₂, e, hc, hm, rfl⟩)
    · exact .inl ⟨c, hc, rfl⟩
    · exact .inr (.inl ⟨c, hc, rfl⟩)
    · cases b₁ with
      | inl b₁ =>
        obtain ⟨rfl, rfl⟩ := mem_caseK_inl.1 hm
        exact .inr (.inr (.inl ⟨c₁, b₁, s₁, hc, by rw [List.append_nil]⟩))
      | inr a₁ =>
        obtain ⟨e₀, hy, rfl⟩ := mem_caseK_inr.1 hm
        have hc₂ : c₂ = [] := hh.1.2 s₁ a₁ _ hy
        subst hc₂
        rw [List.append_nil]
        cases e₀ with
        | trap => exact absurd ⟨[], hy⟩ (hh.2.2.1 s₁ a₁)
        | div => exact .inr (.inr (.inr (.inl ⟨c₁, a₁, s₁, hc, divAt_of_mem hh hy, rfl⟩)))
        | ret x' t' =>
          exact .inr (.inr (.inr (.inr ⟨c₁, a₁, s₁, x', t', hc, retAt_of_mem hh hy, rfl⟩)))
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, b, s', hc, rfl⟩ | ⟨c, a₁, s₁, hc, hd, rfl⟩ |
      ⟨c, a₁, s₁, x', t', hc, hr, rfl⟩)
    · exact .inl ⟨c, hc, rfl⟩
    · exact .inr (.inl ⟨c, hc, rfl⟩)
    · exact .inr (.inr ⟨c, .inl b, s', [], _, hc, mem_caseK_inl.2 ⟨rfl, rfl⟩,
        by rw [List.append_nil]⟩)
    · exact .inr (.inr ⟨c, .inr a₁, s₁, [], _, hc, mem_caseK_inr.2 ⟨.div, hd ▸ rfl, rfl⟩,
        by rw [List.append_nil]; rfl⟩)
    · exact .inr (.inr ⟨c, .inr a₁, s₁, [], _, hc,
        mem_caseK_inr.2 ⟨.ret x' t', hr ▸ rfl, rfl⟩, by rw [List.append_nil]; rfl⟩)

theorem exit_iff {s : S} {a : A'} {x : A} {t : S} (hr : RetAt h s a x t) {c : List (Call E)}
    {b : B} {s' : S} :
    (c, End.ret (.inl b) s') ∈ F.1 t x ↔ (c, End.ret (.inl b) s') ∈ G.1 s a := by
  rw [← mem_seq_ret hr, mem_hyp hFG, mem_seqK hh]
  constructor
  · rintro (⟨_, -, he⟩ | ⟨_, -, he⟩ | ⟨c', b', s'', hc, he⟩ | ⟨_, _, _, -, -, he⟩ |
      ⟨_, _, _, _, _, -, -, he⟩) <;> cases he
    exact hc
  · exact fun hm => .inr (.inr (.inl ⟨c, b, s', hm, rfl⟩))

theorem trap_iff {s : S} {a : A'} {x : A} {t : S} (hr : RetAt h s a x t) {c : List (Call E)} :
    (c, End.trap) ∈ F.1 t x ↔ (c, End.trap) ∈ G.1 s a := by
  rw [← mem_seq_ret hr, mem_hyp hFG, mem_seqK hh]
  constructor
  · rintro (⟨c', hc, he⟩ | ⟨_, -, he⟩ | ⟨_, _, _, -, he⟩ | ⟨_, _, _, -, -, he⟩ |
      ⟨_, _, _, _, _, -, -, he⟩) <;> cases he
    exact hc
  · exact fun hm => .inl ⟨c, hm, rfl⟩

theorem div_iff {s : S} {a : A'} {x : A} {t : S} (hr : RetAt h s a x t) {c : List (Call E)} :
    (c, End.div) ∈ F.1 t x ↔
      (c, End.div) ∈ G.1 s a ∨ ∃ a₁ s₁, (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ DivAt h s₁ a₁ := by
  rw [← mem_seq_ret hr, mem_hyp hFG, mem_seqK hh]
  constructor
  · rintro (⟨_, -, he⟩ | ⟨c', hc, he⟩ | ⟨_, _, _, -, he⟩ | ⟨c', a₁, s₁, hc, hd, he⟩ |
      ⟨_, _, _, _, _, -, -, he⟩) <;> cases he
    · exact .inl hc
    · exact .inr ⟨a₁, s₁, hc, hd⟩
  · rintro (hm | ⟨a₁, s₁, hm, hd⟩)
    · exact .inr (.inl ⟨c, hm, rfl⟩)
    · exact .inr (.inr (.inr (.inl ⟨c, a₁, s₁, hm, hd, rfl⟩)))

theorem cont_iff {s : S} {a : A'} {x : A} {t : S} (hr : RetAt h s a x t) {c : List (Call E)}
    {x' : A} {t' : S} :
    (c, End.ret (.inr x') t') ∈ F.1 t x ↔
      ∃ a₁ s₁, (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ RetAt h s₁ a₁ x' t' := by
  rw [← mem_seq_ret hr, mem_hyp hFG, mem_seqK hh]
  constructor
  · rintro (⟨_, -, he⟩ | ⟨_, -, he⟩ | ⟨_, _, _, -, he⟩ | ⟨_, _, _, -, -, he⟩ |
      ⟨c', a₁, s₁, _, _, hc, hr₁, he⟩) <;> cases he
    exact ⟨a₁, s₁, hc, hr₁⟩
  · rintro ⟨a₁, s₁, hm, hr₁⟩
    exact .inr (.inr (.inr (.inr ⟨c, a₁, s₁, x', t', hm, hr₁, rfl⟩)))

theorem inf_eq {s : S} {a : A'} {x : A} {t : S} (hr : RetAt h s a x t) : F.2 t x = G.2 s a := by
  rw [← inf_hyp hh hFG, seq_inf_ret hh hr]

/-- Where `h` diverges, `G` diverges silently or continues silently to where `h` diverges. -/
theorem of_div {s : S} {a : A'} (hd : DivAt h s a) {y : CallBeh E S (B ⊕ A')}
    (hy : y ∈ G.1 s a) :
    y = ([], End.div) ∨ ∃ a₁ s₁, y = ([], End.ret (.inr a₁) s₁) ∧ DivAt h s₁ a₁ := by
  obtain ⟨c, e⟩ := y
  have key : ∀ z, z ∈ (FullFun.seq G (caseK h)).1 s a → z = ([], End.div) := fun z hz =>
    (mem_seq_div hd z).1 ((mem_hyp hFG s a z).2 hz)
  cases e with
  | trap => cases (Prod.mk.inj (key _ ((mem_seqK hh).2 (.inl ⟨c, hy, rfl⟩)))).2
  | div =>
    rw [(Prod.mk.inj (key _ ((mem_seqK hh).2 (.inr (.inl ⟨c, hy, rfl⟩))))).1]
    exact .inl rfl
  | ret b s₁ =>
    cases b with
    | inl b =>
      cases (Prod.mk.inj (key _ ((mem_seqK hh).2 (.inr (.inr (.inl ⟨c, b, s₁, hy, rfl⟩)))))).2
    | inr a₁ =>
      rcases shape hh s₁ a₁ with hd₁ | ⟨x', t', hr₁⟩
      · have hk := key _ ((mem_seqK hh).2 (.inr (.inr (.inr (.inl ⟨c, a₁, s₁, hy, hd₁, rfl⟩)))))
        rw [(Prod.mk.inj hk).1]
        exact .inr ⟨a₁, s₁, rfl, hd₁⟩
      · cases (Prod.mk.inj (key _ ((mem_seqK hh).2
          (.inr (.inr (.inr (.inr ⟨c, a₁, s₁, x', t', hy, hr₁, rfl⟩))))))).2

theorem inf_div {s : S} {a : A'} (hd : DivAt h s a) : G.2 s a = ∅ := by
  rw [← inf_hyp hh hFG, seq_inf_div hh hd]

end Hyp

end Silmaril.Proofs.Games.Abstract.IterUniform
