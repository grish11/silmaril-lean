module

public import Silmaril.Games.Abstract.IterUniformFin.Defs

/-!
# Uniformity along silent, finitely branching maps: the hypothesis, pointwise (proofs)

A silent, trap-free map has only behaviours `([], div)` and `([], ret x t)` (`beh_cases`).
Sequencing after it is the union, over its returns `(x, t)`, of the second function at
`(t, x)`, together with a silent divergence where it may diverge (`mem_seq`, `mem_seq_inf`).

Under `h ; F = G ; [inl, inr ∘ h]` the behaviours of `F` at one return of `h` are only bounded
by the union over all returns. The pointwise consequences used in the proof:

* **from `G` to `F`**, a behaviour of `G` at `(s, a)` is one of `F` at *some* return of `h` at
  `(s, a)` (`exit_of_G`, `trap_of_G`, `div_of_G`, `cont_of_G`, `contDiv_of_G`); a continuation
  of `G` into one return `(x₁, t₁)` of `h` becomes a continuation of `F` into `(x₁, t₁)`;
* **from `F` to `G`**, a behaviour of `F` at *any* return of `h` at `(s, a)` is one of `G` at
  `(s, a)` (`exit_of_F`, `trap_of_F`, `div_of_F`, `cont_of_F`);
* where `h` may diverge, `G` diverges silently or continues silently to a point where `h` may
  diverge (`of_mayDiv`). Where `h` never returns, `G` continues only silently, to points where
  `h` never returns (`of_noRet`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniformFin

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A A' B C : Type u}

section Shape

variable {h : FullFun E S A' A}

/-- The behaviours of a silent, trap-free map. -/
theorem beh_cases (hh : FullFun.SilentFinNoTrap h) {s : S} {a : A'} {y : CallBeh E S A}
    (hy : y ∈ h.1 s a) : y = ([], End.div) ∨ ∃ x t, y = ([], End.ret x t) := by
  obtain ⟨c, e⟩ := y
  have hc : c = [] := hh.1.2 s a _ hy
  subst hc
  cases e with
  | ret x t => exact .inr ⟨x, t, rfl⟩
  | trap => exact absurd ⟨[], hy⟩ (hh.2.1 s a)
  | div => exact .inl rfl

/-- **Sequencing after a silent, trap-free map**: a silent divergence of the map, or a
behaviour of the second function at one of its returns. -/
theorem mem_seq (hh : FullFun.SilentFinNoTrap h) {X : FullFun E S A C} {s : S} {a : A'}
    {y : CallBeh E S C} :
    y ∈ (FullFun.seq h X).1 s a ↔
      (([], End.div) ∈ h.1 s a ∧ y = ([], End.div)) ∨
        ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ y ∈ X.1 t x := by
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hc, hm, rfl⟩)
    · exact absurd ⟨c, hc⟩ (hh.2.1 s a)
    · have hc' : c = [] := hh.1.2 s a _ hc
      subst hc'
      exact .inl ⟨hc, rfl⟩
    · have hc' : c₁ = [] := hh.1.2 s a _ hc
      subst hc'
      exact .inr ⟨b, s₁, hc, hm⟩
  · rintro (⟨hd, rfl⟩ | ⟨x, t, hr, hm⟩)
    · exact .inr (.inl ⟨[], hd, rfl⟩)
    · exact .inr (.inr ⟨[], x, t, _, _, hr, hm, rfl⟩)

/-- **Productive runs after a silent map**: a productive run of the second function at one of
its returns. -/
theorem mem_seq_inf (hh : FullFun.SilentFinNoTrap h) {X : FullFun E S A C} {s : S} {a : A'}
    {ω : ℕ → Call E} :
    ω ∈ (FullFun.seq h X).2 s a ↔ ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ ω ∈ X.2 t x := by
  constructor
  · rintro (hω | ⟨c, b, s₁, ω', hc, hω, rfl⟩)
    · rw [hh.1.1 s a] at hω; exact hω.elim
    · have hc' : c = [] := hh.1.2 s a _ hc
      subst hc'
      exact ⟨b, s₁, hc, hω⟩
  · rintro ⟨x, t, hr, hω⟩
    exact .inr ⟨[], x, t, ω, hr, hω, rfl⟩

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
  (hh : FullFun.SilentFinNoTrap h) (hFG : FullFun.seq h F = FullFun.seq G (caseK h))
include hh hFG

omit hh in
theorem mem_hyp {s : S} {a : A'} {y : CallBeh E S (B ⊕ A)} :
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
      (∃ c a₁ s₁, (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ ([], End.div) ∈ h.1 s₁ a₁ ∧
        y = (c, End.div)) ∨
      ∃ c a₁ s₁ x' t', (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ ([], End.ret x' t') ∈ h.1 s₁ a₁ ∧
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
        | trap => exact absurd ⟨[], hy⟩ (hh.2.1 s₁ a₁)
        | div => exact .inr (.inr (.inr (.inl ⟨c₁, a₁, s₁, hc, hy, rfl⟩)))
        | ret x' t' => exact .inr (.inr (.inr (.inr ⟨c₁, a₁, s₁, x', t', hc, hy, rfl⟩)))
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, b, s', hc, rfl⟩ | ⟨c, a₁, s₁, hc, hd, rfl⟩ |
      ⟨c, a₁, s₁, x', t', hc, hr, rfl⟩)
    · exact .inl ⟨c, hc, rfl⟩
    · exact .inr (.inl ⟨c, hc, rfl⟩)
    · exact .inr (.inr ⟨c, .inl b, s', [], _, hc, mem_caseK_inl.2 ⟨rfl, rfl⟩,
        by rw [List.append_nil]⟩)
    · exact .inr (.inr ⟨c, .inr a₁, s₁, [], _, hc, mem_caseK_inr.2 ⟨.div, hd, rfl⟩,
        by rw [List.append_nil]; rfl⟩)
    · exact .inr (.inr ⟨c, .inr a₁, s₁, [], _, hc, mem_caseK_inr.2 ⟨.ret x' t', hr, rfl⟩,
        by rw [List.append_nil]; rfl⟩)

/-- A behaviour of `G ; [inl, inr ∘ h]` that is not a silent divergence comes from `F` at one
return of `h`. -/
theorem of_seqK {s : S} {a : A'} {c : List (Call E)} {e : End S (B ⊕ A)}
    (hm : (c, e) ∈ (FullFun.seq G (caseK h)).1 s a) :
    (([], End.div) ∈ h.1 s a ∧ c = [] ∧ e = .div) ∨
      ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ (c, e) ∈ F.1 t x := by
  rcases (mem_seq hh).1 ((mem_hyp hFG).2 hm) with ⟨hd, he⟩ | ⟨x, t, hr, hm'⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact .inl ⟨hd, rfl, rfl⟩
  · exact .inr ⟨x, t, hr, hm'⟩

/-! ### From `G` to `F` -/

theorem exit_of_G {s : S} {a : A'} {c : List (Call E)} {b : B} {s' : S}
    (hm : (c, End.ret (.inl b) s') ∈ G.1 s a) :
    ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ (c, End.ret (.inl b) s') ∈ F.1 t x := by
  rcases of_seqK hh hFG ((mem_seqK hh).2 (.inr (.inr (.inl ⟨c, b, s', hm, rfl⟩)))) with
    ⟨-, -, he⟩ | hx
  · cases he
  · exact hx

theorem trap_of_G {s : S} {a : A'} {c : List (Call E)} (hm : (c, End.trap) ∈ G.1 s a) :
    ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ (c, End.trap) ∈ F.1 t x := by
  rcases of_seqK hh hFG ((mem_seqK hh).2 (.inl ⟨c, hm, rfl⟩)) with ⟨-, -, he⟩ | hx
  · cases he
  · exact hx

theorem div_of_G {s : S} {a : A'} {c : List (Call E)} (hm : (c, End.div) ∈ G.1 s a) :
    (([], End.div) ∈ h.1 s a ∧ c = []) ∨
      ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ (c, End.div) ∈ F.1 t x := by
  rcases of_seqK hh hFG ((mem_seqK hh).2 (.inr (.inl ⟨c, hm, rfl⟩))) with ⟨hd, hc, -⟩ | hx
  · exact .inl ⟨hd, hc⟩
  · exact .inr hx

/-- A continuation of `G` into a point where `h` may diverge. -/
theorem contDiv_of_G {s : S} {a : A'} {c : List (Call E)} {a₁ : A'} {s₁ : S}
    (hm : (c, End.ret (.inr a₁) s₁) ∈ G.1 s a) (hd₁ : ([], End.div) ∈ h.1 s₁ a₁) :
    (([], End.div) ∈ h.1 s a ∧ c = []) ∨
      ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ (c, End.div) ∈ F.1 t x := by
  rcases of_seqK hh hFG ((mem_seqK hh).2 (.inr (.inr (.inr (.inl ⟨c, a₁, s₁, hm, hd₁, rfl⟩)))))
    with ⟨hd, hc, -⟩ | hx
  · exact .inl ⟨hd, hc⟩
  · exact .inr hx

/-- A continuation of `G` into one return `(x₁, t₁)` of `h` is a continuation of `F` into
`(x₁, t₁)` at some return of `h`. -/
theorem cont_of_G {s : S} {a : A'} {c : List (Call E)} {a₁ : A'} {s₁ : S} {x₁ : A} {t₁ : S}
    (hm : (c, End.ret (.inr a₁) s₁) ∈ G.1 s a) (hr₁ : ([], End.ret x₁ t₁) ∈ h.1 s₁ a₁) :
    ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ (c, End.ret (.inr x₁) t₁) ∈ F.1 t x := by
  rcases of_seqK hh hFG
    ((mem_seqK hh).2 (.inr (.inr (.inr (.inr ⟨c, a₁, s₁, x₁, t₁, hm, hr₁, rfl⟩))))) with
    ⟨-, -, he⟩ | hx
  · cases he
  · exact hx

/-! ### From `F` to `G` -/

theorem mem_seqK_of_F {s : S} {a : A'} {x : A} {t : S} (hr : ([], End.ret x t) ∈ h.1 s a)
    {y : CallBeh E S (B ⊕ A)} (hm : y ∈ F.1 t x) : y ∈ (FullFun.seq G (caseK h)).1 s a :=
  (mem_hyp hFG).1 ((mem_seq hh).2 (.inr ⟨x, t, hr, hm⟩))

theorem exit_of_F {s : S} {a : A'} {x : A} {t : S} (hr : ([], End.ret x t) ∈ h.1 s a)
    {c : List (Call E)} {b : B} {s' : S} (hm : (c, End.ret (.inl b) s') ∈ F.1 t x) :
    (c, End.ret (.inl b) s') ∈ G.1 s a := by
  rcases (mem_seqK hh).1 (mem_seqK_of_F hh hFG hr hm) with ⟨_, -, he⟩ | ⟨_, -, he⟩ |
      ⟨c', b', s'', hc, he⟩ | ⟨_, _, _, -, -, he⟩ | ⟨_, _, _, _, _, -, -, he⟩ <;> cases he
  exact hc

theorem trap_of_F {s : S} {a : A'} {x : A} {t : S} (hr : ([], End.ret x t) ∈ h.1 s a)
    {c : List (Call E)} (hm : (c, End.trap) ∈ F.1 t x) : (c, End.trap) ∈ G.1 s a := by
  rcases (mem_seqK hh).1 (mem_seqK_of_F hh hFG hr hm) with ⟨c', hc, he⟩ | ⟨_, -, he⟩ |
      ⟨_, _, _, -, he⟩ | ⟨_, _, _, -, -, he⟩ | ⟨_, _, _, _, _, -, -, he⟩ <;> cases he
  exact hc

theorem div_of_F {s : S} {a : A'} {x : A} {t : S} (hr : ([], End.ret x t) ∈ h.1 s a)
    {c : List (Call E)} (hm : (c, End.div) ∈ F.1 t x) :
    (c, End.div) ∈ G.1 s a ∨
      ∃ a₁ s₁, (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ ([], End.div) ∈ h.1 s₁ a₁ := by
  rcases (mem_seqK hh).1 (mem_seqK_of_F hh hFG hr hm) with ⟨_, -, he⟩ | ⟨c', hc, he⟩ |
      ⟨_, _, _, -, he⟩ | ⟨c', a₁, s₁, hc, hd, he⟩ | ⟨_, _, _, _, _, -, -, he⟩ <;> cases he
  · exact .inl hc
  · exact .inr ⟨a₁, s₁, hc, hd⟩

theorem cont_of_F {s : S} {a : A'} {x : A} {t : S} (hr : ([], End.ret x t) ∈ h.1 s a)
    {c : List (Call E)} {x' : A} {t' : S} (hm : (c, End.ret (.inr x') t') ∈ F.1 t x) :
    ∃ a₁ s₁, (c, End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ ([], End.ret x' t') ∈ h.1 s₁ a₁ := by
  rcases (mem_seqK hh).1 (mem_seqK_of_F hh hFG hr hm) with ⟨_, -, he⟩ | ⟨_, -, he⟩ |
      ⟨_, _, _, -, he⟩ | ⟨_, _, _, -, -, he⟩ | ⟨c', a₁, s₁, _, _, hc, hr₁, he⟩ <;> cases he
  exact ⟨a₁, s₁, hc, hr₁⟩

/-- At a return of `h`, the productive runs of `F` are among those of `G`. -/
theorem inf_of_F {s : S} {a : A'} {x : A} {t : S} (hr : ([], End.ret x t) ∈ h.1 s a)
    {ω : ℕ → Call E} (hω : ω ∈ F.2 t x) : ω ∈ G.2 s a := by
  rw [← inf_hyp hh hFG]
  exact (mem_seq_inf hh).2 ⟨x, t, hr, hω⟩

/-- A productive run of `G` is one of `F` at some return of `h`. -/
theorem inf_of_G {s : S} {a : A'} {ω : ℕ → Call E} (hω : ω ∈ G.2 s a) :
    ∃ x t, ([], End.ret x t) ∈ h.1 s a ∧ ω ∈ F.2 t x := by
  rw [← inf_hyp hh hFG] at hω
  exact (mem_seq_inf hh).1 hω

/-! ### Divergence of `h` -/

/-- Where `h` may diverge, `G` diverges silently or continues silently to a point where `h`
may diverge. -/
theorem of_mayDiv {s : S} {a : A'} (hd : ([], End.div) ∈ h.1 s a) :
    ([], End.div) ∈ G.1 s a ∨
      ∃ a₁ s₁, ([], End.ret (.inr a₁) s₁) ∈ G.1 s a ∧ ([], End.div) ∈ h.1 s₁ a₁ := by
  have hm : ([], End.div) ∈ (FullFun.seq G (caseK h)).1 s a :=
    (mem_hyp hFG).1 ((mem_seq hh).2 (.inl ⟨hd, rfl⟩))
  rcases (mem_seqK hh).1 hm with ⟨_, -, he⟩ | ⟨c, hc, he⟩ | ⟨_, _, _, -, he⟩ |
      ⟨c, a₁, s₁, hc, hd₁, he⟩ | ⟨_, _, _, _, _, -, -, he⟩ <;> cases he
  · exact .inl hc
  · exact .inr ⟨a₁, s₁, hc, hd₁⟩

/-- `h` never returns at `(s, a)`. -/
def NoRet (h : FullFun E S A' A) (s : S) (a : A') : Prop := ∀ x t, ([], End.ret x t) ∉ h.1 s a

/-- Where `h` never returns, `G` continues only silently, to points where `h` never returns. -/
theorem of_noRet {s : S} {a : A'} (hn : NoRet h s a) {c : List (Call E)} {a₁ : A'} {s₁ : S}
    (hm : (c, End.ret (.inr a₁) s₁) ∈ G.1 s a) : c = [] ∧ NoRet h s₁ a₁ := by
  have hn₁ : NoRet h s₁ a₁ := fun x₁ t₁ hr₁ => by
    obtain ⟨x, t, hr, -⟩ := cont_of_G hh hFG hm hr₁
    exact hn x t hr
  refine ⟨?_, hn₁⟩
  obtain ⟨y, hy⟩ := hh.2.2.1 s₁ a₁
  rcases beh_cases hh hy with rfl | ⟨x₁, t₁, rfl⟩
  · rcases contDiv_of_G hh hFG hm hy with ⟨-, hc⟩ | ⟨x, t, hr, -⟩
    · exact hc
    · exact (hn x t hr).elim
  · exact (hn₁ x₁ t₁ hy).elim

end Hyp

end Silmaril.Proofs.Games.Abstract.IterUniformFin
