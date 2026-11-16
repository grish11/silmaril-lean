module

public import Silmaril.Proofs.Games.Abstract.StratOps.Laws
import Silmaril.Games.Abstract.FullFun.Thms
public import Silmaril.Proofs.Games.Abstract.FullFun.Dinat
public import Silmaril.Proofs.Games.Abstract.FullFun.Codiag

/-!
# Dinaturality and the codiagonal law of iteration for triples (proofs)

The full part is `FullFun.iter_dinat`. The pending calls of `iterT (t ; [inl, u])` are those of
`t`, or of `u` after a continuing return of `t`, after a finite chain of continuing iterations;
the pending calls of `t ; [id, iterT (u ; [inl, t])]` group the same runs as a first run of `t`
followed by a chain of `(u, t)` iterations.

The codiagonal law `iterT (iterT t) = iterT (t.map [id, inr])` has full part
`FullFun.iter_codiag`. A pending call of the nested loop comes after a chain of outer iterations
and a chain of inner steps, which together are a chain of the merged body, and conversely
(`codiag_chain_split`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps
open Silmaril.Proofs.Games.Abstract.FullFun (body body_cont body_of_g contChain_append
  codiag_outer_chain codiag_inner_chain codiag_chain_split)

universe u

variable {E : Sig.{u}} {S A B C X : Type u}

/-- The pending calls of `t ; [p, v]` when `p` has none. -/
theorem mem_seqT_caseT_pending {t : ObsTriple E S A (B ⊕ C)} {p : ObsTriple E S B X}
    {v : ObsTriple E S C X} (hp : ∀ s b, p.2.1 s b = ∅) {s : S} {a : A}
    {x : List (Call E) × E.Op} :
    x ∈ (seqT t (caseT p v)).2.1 s a ↔ x ∈ t.2.1 s a ∨
      ∃ c s₁ y c₂ m, (c, End.ret (.inr y) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ v.2.1 s₁ y ∧
        x = (c ++ c₂, m) := by
  constructor
  · rintro (h | ⟨c, b | y, s₁, c₂, m, ht, hv, rfl⟩)
    · exact .inl h
    · have hv' : (c₂, m) ∈ p.2.1 s₁ b := hv
      rw [hp] at hv'
      exact hv'.elim
    · exact .inr ⟨c, s₁, y, c₂, m, ht, hv, rfl⟩
  · rintro (h | ⟨c, s₁, y, c₂, m, ht, hv, rfl⟩)
    · exact .inl h
    · exact .inr ⟨c, .inr y, s₁, c₂, m, ht, hv, rfl⟩

/-- A pending call of the body is one of the iteration. -/
theorem iterT_pending_of_body {T : ObsTriple E S A (B ⊕ A)} {s : S} {a : A}
    {c : List (Call E)} {m : E.Op} (h : (c, m) ∈ T.2.1 s a) : (c, m) ∈ (iterT T).2.1 s a :=
  ⟨[], s, a, c, m, .refl, h, rfl⟩

/-- A continuing iteration in front of a pending call of the iteration. -/
theorem iterT_pending_cons {T : ObsTriple E S A (B ⊕ A)} {s : S} {a : A} {c : List (Call E)}
    {a' : A} {s' : S} (hm : (c, End.ret (.inr a') s') ∈ T.1 s a) {d : List (Call E)}
    {m : E.Op} (h : (d, m) ∈ (iterT T).2.1 s' a') : (c ++ d, m) ∈ (iterT T).2.1 s a := by
  obtain ⟨c₀, s'', a'', c', m', hc, hp, he⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨c ++ c₀, s'', a'', c', m, .step hm hc, hp, by simp⟩

section Dinat

variable {t : ObsTriple E S A (B ⊕ C)} {u : ObsTriple E S C (B ⊕ A)}

/-- The left-hand side body `t ; [inl, u]`. -/
abbrev bodyT (t : ObsTriple E S A (B ⊕ C)) (u : ObsTriple E S C (B ⊕ X)) :
    ObsTriple E S A (B ⊕ X) :=
  seqT t (caseT (mapT pureT Sum.inl) u)

theorem mem_bodyT_pending {u : ObsTriple E S C (B ⊕ X)} {s : S} {a : A}
    {x : List (Call E) × E.Op} :
    x ∈ (bodyT t u).2.1 s a ↔ x ∈ t.2.1 s a ∨
      ∃ c s₁ y c₂ m, (c, End.ret (.inr y) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ u.2.1 s₁ y ∧
        x = (c ++ c₂, m) :=
  mem_seqT_caseT_pending fun _ _ => rfl

/-- The right-hand side of dinaturality. -/
abbrev dinatRT (t : ObsTriple E S A (B ⊕ C)) (u : ObsTriple E S C (B ⊕ A)) :
    ObsTriple E S A B :=
  seqT t (caseT pureT (iterT (bodyT u t)))

theorem pending_psi_cons {s₁ : S} {x : C} {c₂ : List (Call E)} {a' : A} {s' : S}
    (hu : (c₂, End.ret (.inr a') s') ∈ u.1 s₁ x) {d : List (Call E)} {m : E.Op}
    (h : (d, m) ∈ (dinatRT t u).2.1 s' a') :
    (c₂ ++ d, m) ∈ (iterT (bodyT u t)).2.1 s₁ x := by
  rcases (mem_seqT_caseT_pending fun _ _ => rfl).1 h with ht | ⟨c₃, s₂, y, d', m', ht, hi, he⟩
  · exact iterT_pending_of_body (mem_bodyT_pending.2 (.inr ⟨c₂, s', a', d, m, hu, ht, rfl⟩))
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have := iterT_pending_cons
      (body_of_g (f := full u) (g := full t) hu ht) hi
    rwa [List.append_assoc] at this

theorem dinat_pending_lr_chain {s : S} {a : A} {c : List (Call E)} {s' : S} {a' : A}
    (hc : FullFun.ContChain (body (full t) (full u)).1 s a c s' a') :
    ∀ {d : List (Call E)} {m : E.Op}, (d, m) ∈ (bodyT t u).2.1 s' a' →
      (c ++ d, m) ∈ (dinatRT t u).2.1 s a := by
  induction hc with
  | refl =>
    intro d m h
    rcases mem_bodyT_pending.1 h with h | ⟨c₁, s₁, y, c₂, m', ht, hu, he⟩
    · exact .inl h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact (mem_seqT_caseT_pending fun _ _ => rfl).2 (.inr ⟨c₁, s₁, y, c₂, m, ht,
        iterT_pending_of_body (mem_bodyT_pending.2 (.inl hu)), rfl⟩)
  | step hm _ ih =>
    intro d m h
    obtain ⟨c₁, s₁, y, c₂, ht, hu, rfl⟩ := (body_cont (f := full t) (g := full u)).1 hm
    exact (mem_seqT_caseT_pending fun _ _ => rfl).2
      (.inr ⟨c₁, s₁, y, _, m, ht, pending_psi_cons hu (ih h), by simp⟩)

theorem dinat_pending_rl_chain {s₁ : S} {x : C} {c : List (Call E)} {s' : S} {x' : C}
    (hc : FullFun.ContChain (body (full u) (full t)).1 s₁ x c s' x') :
    ∀ {s : S} {a : A} {c₁ : List (Call E)}, (c₁, End.ret (.inr x) s₁) ∈ t.1 s a →
      ∀ {d : List (Call E)} {m : E.Op}, (d, m) ∈ (bodyT u t).2.1 s' x' →
        (c₁ ++ (c ++ d), m) ∈ (iterT (bodyT t u)).2.1 s a := by
  induction hc with
  | refl =>
    intro s a c₁ ht d m h
    rcases mem_bodyT_pending.1 h with hu | ⟨c₂, s₂, a', c₃, m', hu, ht', he⟩
    · exact iterT_pending_of_body (mem_bodyT_pending.2 (.inr ⟨c₁, _, _, d, m, ht, hu, rfl⟩))
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have := iterT_pending_cons (body_of_g (f := full t) (g := full u) ht hu)
        (iterT_pending_of_body (mem_bodyT_pending.2 (.inl ht')))
      simpa only [List.nil_append, List.append_assoc] using this
  | step hm _ ih =>
    intro s a c₁ ht d m h
    obtain ⟨c₂, s₂, a', c₃, hu, ht', rfl⟩ := (body_cont (f := full u) (g := full t)).1 hm
    have := iterT_pending_cons (body_of_g (f := full t) (g := full u) ht hu) (ih ht' h)
    simpa only [List.append_assoc] using this

/-- **Dinaturality**, pending calls. -/
theorem iterT_dinat_pending (t : ObsTriple E S A (B ⊕ C)) (u : ObsTriple E S C (B ⊕ A)) :
    (iterT (bodyT t u)).2.1 = (dinatRT t u).2.1 := by
  funext s a
  ext ⟨d, m⟩
  constructor
  · rintro ⟨c, s', a', c', m', hc, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact dinat_pending_lr_chain hc hp
  · intro h
    rcases (mem_seqT_caseT_pending fun _ _ => rfl).1 h with ht | ⟨c₁, s₁, x, d', m', ht, hi, he⟩
    · exact iterT_pending_of_body (mem_bodyT_pending.2 (.inl ht))
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      obtain ⟨c, s', x', c', m'', hc, hp, he'⟩ := hi
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
      exact dinat_pending_rl_chain hc ht hp

/-- **Dinaturality of iteration** for triples. -/
theorem iterT_dinat (t : ObsTriple E S A (B ⊕ C)) (u : ObsTriple E S C (B ⊕ A)) :
    iterT (bodyT t u) = dinatRT t u :=
  ext_full (FullFun.iter_dinat (full t) (full u)) (iterT_dinat_pending t u)

end Dinat

/-- **The codiagonal law**, pending calls. -/
theorem iterT_codiag_pending (t : ObsTriple E S A ((B ⊕ A) ⊕ A)) :
    (iterT (iterT t)).2.1 = (iterT (mapT t (Sum.elim id Sum.inr))).2.1 := by
  funext s a
  ext ⟨d, m⟩
  constructor
  · rintro ⟨c, s', a', c', m', hc, ⟨c'', s'', a'', c''', m'', hc', hp, he'⟩, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨c ++ c'', s'', a'', c''', _, contChain_append (codiag_outer_chain (F := full t) hc)
      (codiag_inner_chain (F := full t) hc'), hp, by simp⟩
  · rintro ⟨c, s', a', c', m', hc, hp, he⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨c₁, s₁, a₁, c₂, ho, hi, rfl⟩ := codiag_chain_split (F := full t) hc
    exact ⟨c₁, s₁, a₁, c₂ ++ c', _, ho, ⟨c₂, s', a', c', _, hi, hp, rfl⟩, by simp⟩

/-- **The codiagonal law** for triples. -/
theorem iterT_codiag (t : ObsTriple E S A ((B ⊕ A) ⊕ A)) :
    iterT (iterT t) = iterT (mapT t (Sum.elim id Sum.inr)) :=
  ext_full (FullFun.iter_codiag (full t)) (iterT_codiag_pending t)

end Silmaril.Proofs.Games.Abstract.StratOps
