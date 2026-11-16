module

public import Silmaril.Games.Abstract.FullFun.Defs
import Silmaril.Proofs.Games.Abstract.FullFun.Tensor

/-!
# Naturality and uniformity of iteration (proofs)

* **Naturality in the output**: `iter (F.map (Sum.map h id)) = (iter F).map h`. Mapping the
  exit value changes no continuing iteration (`mem_cont_map`), so chains are the same
  (`contChain_map`), and an exit `inl b` of the last iteration becomes `inl (h b)`.
* **Uniformity** for a pure `k : A' → A`: if `F.comap k = G.map (Sum.map id k)` then
  `(iter F).comap k = iter G`. A run of `G` maps to a run of `F` by applying `k` to every
  continuing argument; conversely a run of `F` from `k a` lifts, one iteration at a time, to a
  run of `G` from `a`. The infinite silent chains (`AFun.IterBeh.spin`) and the infinite
  productive chains are lifted by dependent choice (`exists_lift`).

The finite parts are stated for `AFun` with `mapBeh`, the finite part of `FullFun.map`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u v w

variable {E : Sig.{u}} {S A A' B C : Type u}

/-- The finite behaviours of `f` with `h` applied to returned values: the finite part of
`FullFun.map`. -/
def mapBeh (h : B → C) (f : AFun E S A B) : AFun E S A C :=
  fun s a => (fun x => (x.1, FullFun.endMap h x.2)) '' f s a

theorem mem_mapBeh_ret {h : B → C} {f : AFun E S A B} {s : S} {a : A} {c : List (Call E)}
    {b' : C} {s' : S} :
    (c, End.ret b' s') ∈ mapBeh h f s a ↔ ∃ b, (c, End.ret b s') ∈ f s a ∧ h b = b' :=
  mem_map_ret (f, fun _ _ => ∅) h s a c b' s'

theorem mem_mapBeh_trap {h : B → C} {f : AFun E S A B} {s : S} {a : A} {c : List (Call E)} :
    (c, End.trap) ∈ mapBeh h f s a ↔ (c, End.trap) ∈ f s a :=
  mem_map_trap (f, fun _ _ => ∅) h s a c

theorem mem_mapBeh_div {h : B → C} {f : AFun E S A B} {s : S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ mapBeh h f s a ↔ (c, End.div) ∈ f s a :=
  mem_map_div (f, fun _ _ => ∅) h s a c

/-- **Dependent choice** along a sequence: lift `x : ℕ → X` through `k : Y → X`, one step at a
time, keeping a step relation `R`. -/
theorem exists_lift {X : Type v} {Y : Type w} (k : Y → X) (x : ℕ → X) (R : ℕ → Y → Y → Prop)
    {y₀ : Y} (h₀ : k y₀ = x 0) (hs : ∀ n y, k y = x n → ∃ y', R n y y' ∧ k y' = x (n + 1)) :
    ∃ y : ℕ → Y, y 0 = y₀ ∧ ∀ n, k (y n) = x n ∧ R n (y n) (y (n + 1)) := by
  let g : (n : ℕ) → {y // k y = x n} := fun n =>
    Nat.rec (motive := fun n => {y // k y = x n}) ⟨y₀, h₀⟩
      (fun n p => ⟨Classical.choose (hs n p.1 p.2), (Classical.choose_spec (hs n p.1 p.2)).2⟩) n
  exact ⟨fun n => (g n).1, rfl,
    fun n => ⟨(g n).2, (Classical.choose_spec (hs n (g n).1 (g n).2)).1⟩⟩

/-! ## Naturality in the output -/

section Map

variable {f : AFun E S A (B ⊕ A)} {h : B → C}

/-- Mapping the exit value keeps the continuing iterations. -/
theorem mem_cont_map {s : S} {a : A} {c : List (Call E)} {a' : A} {s' : S} :
    (c, End.ret (.inr a') s') ∈ mapBeh (Sum.map h id) f s a ↔
      (c, End.ret (.inr a') s') ∈ f s a := by
  rw [mem_mapBeh_ret]
  constructor
  · rintro ⟨b | b, hb, he⟩
    · cases he
    · cases he; exact hb
  · exact fun hm => ⟨.inr a', hm, rfl⟩

/-- Mapping the exit value keeps the continuing chains. -/
theorem contChain_map {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A} :
    FullFun.ContChain (mapBeh (Sum.map h id) f) s a c s' a' ↔ FullFun.ContChain f s a c s' a' := by
  constructor
  · intro hc
    induction hc with
    | refl => exact .refl
    | step hm _ ih => exact .step (mem_cont_map.1 hm) ih
  · intro hc
    induction hc with
    | refl => exact .refl
    | step hm _ ih => exact .step (mem_cont_map.2 hm) ih

theorem iterBeh_map_of {s : S} {a : A} {y : CallBeh E S C}
    (hy : AFun.IterBeh (mapBeh (Sum.map h id) f) s a y) :
    ∃ c e, AFun.IterBeh f s a (c, e) ∧ y = (c, FullFun.endMap h e) := by
  induction hy with
  | exit hm =>
    obtain ⟨b₀ | b₀, hb, he⟩ := mem_mapBeh_ret.1 hm
    · cases he; exact ⟨_, _, .exit hb, rfl⟩
    · cases he
  | trap hm => exact ⟨_, _, .trap (mem_mapBeh_trap.1 hm), rfl⟩
  | div hm => exact ⟨_, _, .div (mem_mapBeh_div.1 hm), rfl⟩
  | step hm _ ih =>
    obtain ⟨c, e, hr, he⟩ := ih
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨_, e, .step (mem_cont_map.1 hm) hr, rfl⟩
  | spin σ h0 hσ => exact ⟨[], .div, .spin σ h0 fun n => mem_cont_map.1 (hσ n), rfl⟩

theorem iterBeh_map {s : S} {a : A} {y : CallBeh E S B} (hy : AFun.IterBeh f s a y) :
    AFun.IterBeh (mapBeh (Sum.map h id) f) s a (y.1, FullFun.endMap h y.2) := by
  induction hy with
  | exit hm => exact .exit (mem_mapBeh_ret.2 ⟨_, hm, rfl⟩)
  | trap hm => exact .trap (mem_mapBeh_trap.2 hm)
  | div hm => exact .div (mem_mapBeh_div.2 hm)
  | step hm _ ih => exact .step (mem_cont_map.2 hm) ih
  | spin σ h0 hσ => exact .spin σ h0 fun n => mem_cont_map.2 (hσ n)

/-- **Naturality of iteration in the output**, finite behaviours. -/
theorem iter_map_fin (f : AFun E S A (B ⊕ A)) (h : B → C) :
    AFun.iter (mapBeh (Sum.map h id) f) = mapBeh h (AFun.iter f) := by
  funext s a
  ext y
  constructor
  · intro hy
    obtain ⟨c, e, hb, rfl⟩ := iterBeh_map_of hy
    exact ⟨(c, e), hb, rfl⟩
  · rintro ⟨y, hb, rfl⟩
    exact iterBeh_map hb

/-- **Naturality of iteration in the output.** -/
theorem iter_map (F : FullFun E S A (B ⊕ A)) (h : B → C) :
    FullFun.iter (F.map (Sum.map h id)) = (FullFun.iter F).map h := by
  refine Prod.ext (iter_map_fin F.1 h) (funext fun s => funext fun a => ?_)
  ext ω
  constructor
  · rintro (⟨c, s', a', ω', hc, hω, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · exact .inl ⟨c, s', a', ω', contChain_map.1 hc, hω, rfl⟩
    · exact .inr ⟨σ, l, h0, fun n => mem_cont_map.1 (hσ n), hl⟩
  · rintro (⟨c, s', a', ω', hc, hω, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · exact .inl ⟨c, s', a', ω', contChain_map.2 hc, hω, rfl⟩
    · exact .inr ⟨σ, l, h0, fun n => mem_cont_map.2 (hσ n), hl⟩

end Map

/-! ## Uniformity -/

section Uniform

variable {f : AFun E S A (B ⊕ A)} {g : AFun E S A' (B ⊕ A')} {k : A' → A}

theorem mem_exit_uniform (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S} {a : A'}
    {c : List (Call E)} {b : B} {s' : S} :
    (c, End.ret (.inl b) s') ∈ f s (k a) ↔ (c, End.ret (.inl b) s') ∈ g s a := by
  rw [hfg, mem_mapBeh_ret]
  constructor
  · rintro ⟨b₀ | b₀, hb, he⟩
    · cases he; exact hb
    · cases he
  · exact fun hm => ⟨.inl b, hm, rfl⟩

theorem mem_cont_uniform (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S} {a : A'}
    {c : List (Call E)} {x : A} {s' : S} :
    (c, End.ret (.inr x) s') ∈ f s (k a) ↔ ∃ a', (c, End.ret (.inr a') s') ∈ g s a ∧ k a' = x := by
  rw [hfg, mem_mapBeh_ret]
  constructor
  · rintro ⟨b₀ | b₀, hb, he⟩
    · cases he
    · cases he; exact ⟨b₀, hb, rfl⟩
  · rintro ⟨a', hm, rfl⟩
    exact ⟨.inr a', hm, rfl⟩

/-- A continuing chain of `g` maps to one of `f`. -/
theorem contChain_uniform (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S}
    {a : A'} {c : List (Call E)} {s' : S} {a' : A'} (hc : FullFun.ContChain g s a c s' a') :
    FullFun.ContChain f s (k a) c s' (k a') := by
  induction hc with
  | refl => exact .refl
  | step hm _ ih => exact .step ((mem_cont_uniform hfg).2 ⟨_, hm, rfl⟩) ih

/-- A continuing chain of `f` from `k a` lifts to one of `g` from `a`. -/
theorem contChain_lift (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S} {x : A}
    {c : List (Call E)} {s' : S} {x' : A} (hc : FullFun.ContChain f s x c s' x') :
    ∀ a, k a = x → ∃ a', k a' = x' ∧ FullFun.ContChain g s a c s' a' := by
  induction hc with
  | refl => exact fun a ha => ⟨a, ha, .refl⟩
  | step hm _ ih =>
    rintro a rfl
    obtain ⟨a₁, hm₁, rfl⟩ := (mem_cont_uniform hfg).1 hm
    obtain ⟨a', ha', hc'⟩ := ih a₁ rfl
    exact ⟨a', ha', .step hm₁ hc'⟩

/-- An infinite continuing chain of `f` from `k a` lifts to one of `g` from `a`. -/
theorem chain_lift (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S} {a : A'}
    {σ : ℕ → S × A} {l : ℕ → List (Call E)} (h0 : σ 0 = (s, k a))
    (hσ : ∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ f (σ n).1 (σ n).2) :
    ∃ τ : ℕ → S × A', τ 0 = (s, a) ∧
      ∀ n, (l n, End.ret (.inr (τ (n + 1)).2) (τ (n + 1)).1) ∈ g (τ n).1 (τ n).2 := by
  obtain ⟨y, hy0, hy⟩ := exists_lift k (fun n => (σ n).2)
    (fun n p p' => (l n, End.ret (.inr p') (σ (n + 1)).1) ∈ g (σ n).1 p)
    (by rw [h0]) fun n p hp => (mem_cont_uniform hfg).1 (hp ▸ hσ n)
  refine ⟨fun n => ((σ n).1, y n), ?_, fun n => (hy n).2⟩
  show ((σ 0).1, y 0) = (s, a)
  rw [hy0, h0]

theorem iterBeh_uniform (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S}
    {a : A'} {y : CallBeh E S B} (hy : AFun.IterBeh g s a y) : AFun.IterBeh f s (k a) y := by
  induction hy with
  | exit hm => exact .exit ((mem_exit_uniform hfg).2 hm)
  | trap hm => exact .trap (by rw [hfg]; exact mem_mapBeh_trap.2 hm)
  | div hm => exact .div (by rw [hfg]; exact mem_mapBeh_div.2 hm)
  | step hm _ ih => exact .step ((mem_cont_uniform hfg).2 ⟨_, hm, rfl⟩) ih
  | spin σ h0 hσ =>
    refine .spin (fun n => ((σ n).1, k (σ n).2)) (by simp [h0]) fun n => ?_
    exact (mem_cont_uniform hfg).2 ⟨_, hσ n, rfl⟩

theorem iterBeh_lift (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) {s : S} {x : A}
    {y : CallBeh E S B} (hy : AFun.IterBeh f s x y) : ∀ a, k a = x → AFun.IterBeh g s a y := by
  induction hy with
  | exit hm => rintro a rfl; exact .exit ((mem_exit_uniform hfg).1 hm)
  | trap hm => rintro a rfl; rw [hfg] at hm; exact .trap (mem_mapBeh_trap.1 hm)
  | div hm => rintro a rfl; rw [hfg] at hm; exact .div (mem_mapBeh_div.1 hm)
  | step hm _ ih =>
    rintro a rfl
    obtain ⟨a₁, hm₁, rfl⟩ := (mem_cont_uniform hfg).1 hm
    exact .step hm₁ (ih a₁ rfl)
  | spin σ h0 hσ =>
    rintro a rfl
    obtain ⟨τ, hτ0, hτ⟩ := chain_lift hfg h0 hσ
    exact .spin τ hτ0 hτ

/-- **Uniformity of iteration**, finite behaviours. -/
theorem iter_uniform_fin (hfg : ∀ s a, f s (k a) = mapBeh (Sum.map id k) g s a) (s : S)
    (a : A') : AFun.iter f s (k a) = AFun.iter g s a := by
  ext y
  exact ⟨fun hy => iterBeh_lift hfg hy a rfl, iterBeh_uniform hfg⟩

/-- The finite part of the uniformity hypothesis. -/
theorem fin_of_comap {F : FullFun E S A (B ⊕ A)} {G : FullFun E S A' (B ⊕ A')}
    (hFG : F.comap k = G.map (Sum.map id k)) :
    ∀ s a, F.1 s (k a) = mapBeh (Sum.map id k) G.1 s a := fun s a =>
  congrFun (congrFun (congrArg Prod.fst hFG) s) a

/-- **Uniformity of iteration** with respect to a pure map. -/
theorem iter_uniform_comap {F : FullFun E S A (B ⊕ A)} {G : FullFun E S A' (B ⊕ A')}
    (hFG : F.comap k = G.map (Sum.map id k)) : (FullFun.iter F).comap k = FullFun.iter G := by
  have hfg := fin_of_comap hFG
  have hp : ∀ s a, F.2 s (k a) = G.2 s a := fun s a =>
    congrFun (congrFun (congrArg Prod.snd hFG) s) a
  refine Prod.ext (funext fun s => funext fun a => iter_uniform_fin hfg s a)
    (funext fun s => funext fun a => ?_)
  ext ω
  constructor
  · rintro (⟨c, s', x', ω', hc, hω, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · obtain ⟨a', rfl, hc'⟩ := contChain_lift hfg hc a rfl
      exact .inl ⟨c, s', a', ω', hc', (hp s' a') ▸ hω, rfl⟩
    · obtain ⟨τ, hτ0, hτ⟩ := chain_lift hfg h0 hσ
      exact .inr ⟨τ, l, hτ0, hτ, hl⟩
  · rintro (⟨c, s', a', ω', hc, hω, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · exact .inl ⟨c, s', k a', ω', contChain_uniform hfg hc, (hp s' a').symm ▸ hω, rfl⟩
    · refine .inr ⟨fun n => ((σ n).1, k (σ n).2), l, by simp [h0], fun n => ?_, hl⟩
      exact (mem_cont_uniform hfg).2 ⟨_, hσ n, rfl⟩

/-- Copairing of pure maps is a pure map. -/
theorem case_pure_map_map {X : Type u} (h₁ : A → X) (h₂ : B → X) :
    FullFun.case ((FullFun.pure : FullFun E S A A).map h₁)
        ((FullFun.pure : FullFun E S B B).map h₂) =
      (FullFun.pure : FullFun E S (A ⊕ B) (A ⊕ B)).map (Sum.elim h₁ h₂) := by
  refine Prod.ext (funext fun s => funext fun x => ?_) (funext fun s => funext fun x => ?_)
  · cases x with
    | inl y =>
      exact (pure_map_fst (E := E) h₁ s y).trans
        (pure_map_fst (E := E) (Sum.elim h₁ h₂) s (.inl y)).symm
    | inr y =>
      exact (pure_map_fst (E := E) h₂ s y).trans
        (pure_map_fst (E := E) (Sum.elim h₁ h₂) s (.inr y)).symm
  · cases x <;> rfl

/-- **Uniformity of iteration**, in the Elgot form: if `h ; F = G ; (id + h)` for a pure `h`,
then `h ; iter F = iter G`. -/
theorem iter_uniform {F : FullFun E S A (B ⊕ A)} {G : FullFun E S A' (B ⊕ A')}
    (h : A' → A)
    (hFG : FullFun.seq (FullFun.pure.map h) F =
      FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (FullFun.pure.map (Sum.inr ∘ h)))) :
    FullFun.seq (FullFun.pure.map h) (FullFun.iter F) = FullFun.iter G := by
  rw [case_pure_map_map, seq_pure_map, pure_map_seq] at hFG
  rw [pure_map_seq]
  exact iter_uniform_comap (hFG.trans (congrArg G.map (funext fun x => by cases x <;> rfl)))

end Uniform

end Silmaril.Proofs.Games.Abstract.FullFun
