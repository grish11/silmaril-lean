module

public import Silmaril.Games.Abstract.CanonStrat.Defs

/-!
# The canonical play objects as a category: theorems

**Realizability.** `realizable_iff`: a strategy is realizable iff it is a play object
`toDStrat t`; `realizable_iff_adm`: iff it is the play object of an admissible triple.
**Closure**: every game-level operation gives a realizable strategy, whatever its arguments
(`realizable_seqD`, …, `realizable_iterD`), since each is a `toDStrat`.

**Representation.** `CanonStrat.equivAdm` has round trips `toCanon (rep σ) = σ`
(`CanonStrat.toCanon_rep`) and `rep (toCanon t) = t` for admissible `t`
(`CanonStrat.rep_toCanon_adm`); `rep` is injective (`CanonStrat.rep_injective`). It sends each
operation to the triple operation (`CanonStrat.rep_seq`, …), because the triple operations
preserve admissibility.

**Laws on `CanonStrat`, with no hypothesis** (from the triple laws through `rep`):

* a category: `seq_assoc`, `seq_pure`, `pure_seq`;
* pure maps: `map_id`, `map_map`, `comap_id`, `comap_comap`, `map_comap`, `seq_pure_map`,
  `pure_map_seq`, `seq_map`, `map_seq`, `comap_seq`;
* whiskering: `whiskerRight_pure`, `whiskerLeft_pure`, `whiskerRight_seq`, `whiskerLeft_seq`;
  `not_interchange`: **the interchange law fails**, so `CanonStrat` is premonoidal and not
  monoidal;
* copairing: `comap_inl_case`, `comap_inr_case`, `pure_map_inl_seq_case`,
  `pure_map_inr_seq_case`, `case_pure_map`, `seq_case`;
* iteration: `iter_unfold` (**the fixpoint law** `iter σ = seq σ (case pure (iter σ))`),
  `iter_map` (**naturality in the output**) and `iter_uniform` (**uniformity** for a pure map
  `h`: `h ; F = G ; [inl, inr ∘ h]` implies `h ; iter F = iter G`) and `iter_dinat`
  (**dinaturality** `iter (σ ; [inl, τ]) = σ ; [id, iter (τ ; [inl, σ])]`).

These are laws of `CanonStrat` only; no law is claimed for general prefix-closed strategies.
-/

public section

namespace Silmaril.Games.Abstract

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-! ## Realizability -/

namespace StratOps

/-- **The realizable strategies are the play objects.** -/
theorem realizable_iff {σ : DStrategy E (funSig S A B)} :
    Realizable σ ↔ ∃ t : ObsTriple E S A B, σ = toDStrat t :=
  ⟨fun h => ⟨_, h.symm⟩, fun ⟨t, h⟩ => h ▸ realizable_toDStrat t⟩

/-- **The realizable strategies are the play objects of admissible triples.** -/
theorem realizable_iff_adm {σ : DStrategy E (funSig S A B)} :
    Realizable σ ↔ ∃ t : ObsTriple E S A B, Admissible t ∧ σ = toDStrat t :=
  ⟨fun h => ⟨_, CanonStrat.admissible_rep ⟨σ, h⟩, h.symm⟩,
    fun ⟨t, _, h⟩ => h ▸ realizable_toDStrat t⟩

/-! ### Closure: every game-level operation gives a realizable strategy -/

theorem realizable_seqD (σ : DStrategy E (funSig S A B)) (τ : DStrategy E (funSig S B C)) :
    Realizable (seqD σ τ) := realizable_toDStrat _

theorem realizable_pureD : Realizable (pureD : DStrategy E (funSig S A A)) :=
  realizable_toDStrat _

theorem realizable_mapD (σ : DStrategy E (funSig S A B)) (h : B → C) :
    Realizable (mapD σ h) := realizable_toDStrat _

theorem realizable_comapD {A' : Type u} (σ : DStrategy E (funSig S A B)) (k : A' → A) :
    Realizable (comapD σ k) := realizable_toDStrat _

theorem realizable_whiskerRightD (σ : DStrategy E (funSig S A B)) (C : Type u) :
    Realizable (whiskerRightD σ C) := realizable_toDStrat _

theorem realizable_whiskerLeftD (C : Type u) (σ : DStrategy E (funSig S A B)) :
    Realizable (whiskerLeftD C σ) := realizable_toDStrat _

theorem realizable_caseD (σ : DStrategy E (funSig S A C)) (τ : DStrategy E (funSig S B C)) :
    Realizable (caseD σ τ) := realizable_toDStrat _

theorem realizable_iterD (σ : DStrategy E (funSig S A (B ⊕ A))) : Realizable (iterD σ) :=
  realizable_toDStrat _

end StratOps

namespace CanonStrat

/-! ## Representation -/

/-- Round trip through the representative. -/
theorem toCanon_rep (σ : CanonStrat E S A B) : toCanon (rep σ) = σ := Subtype.ext σ.2

/-- The representative of a play object is the saturation of its triple. -/
theorem rep_toCanon (t : ObsTriple E S A B) : rep (toCanon t) = sat t := readback_toDStrat t

/-- Round trip through an admissible triple. -/
theorem rep_toCanon_adm {t : ObsTriple E S A B} (ht : Admissible t) : rep (toCanon t) = t :=
  readback_toDStrat_adm ht

/-- A canonical play object is determined by its representative. -/
theorem rep_injective : Function.Injective (rep : CanonStrat E S A B → ObsTriple E S A B) :=
  fun σ τ h => by rw [← toCanon_rep σ, h, toCanon_rep]

theorem equivAdm_apply (σ : CanonStrat E S A B) : (equivAdm σ).1 = rep σ := rfl

theorem equivAdm_symm_apply (t : AdmTriple E S A B) : equivAdm.symm t = toCanon t.1 := rfl

/-! ### The operations on representatives -/

section Rep

variable (σ : CanonStrat E S A B)

theorem rep_seq (τ : CanonStrat E S B C) : rep (seq σ τ) = seqT (rep σ) (rep τ) :=
  rep_toCanon_adm (admissible_seqT (admissible_rep σ) (admissible_rep τ))

theorem rep_pure : rep (pure : CanonStrat E S A A) = pureT := rep_toCanon_adm admissible_pureT

theorem rep_map (h : B → C) : rep (map σ h) = mapT (rep σ) h :=
  rep_toCanon_adm (admissible_mapT (admissible_rep σ) h)

theorem rep_comap {A' : Type u} (k : A' → A) : rep (comap σ k) = comapT (rep σ) k :=
  rep_toCanon_adm (admissible_comapT (admissible_rep σ) k)

theorem rep_whiskerRight (C : Type u) : rep (whiskerRight σ C) = whiskerRightT (rep σ) C :=
  rep_toCanon_adm (admissible_whiskerRightT (admissible_rep σ) C)

theorem rep_whiskerLeft (C : Type u) : rep (whiskerLeft C σ) = whiskerLeftT C (rep σ) :=
  rep_toCanon_adm (admissible_whiskerLeftT (admissible_rep σ) C)

theorem rep_case {X : Type u} (σ : CanonStrat E S A X) (τ : CanonStrat E S B X) :
    rep (case σ τ) = caseT (rep σ) (rep τ) :=
  rep_toCanon_adm (admissible_caseT (admissible_rep σ) (admissible_rep τ))

theorem rep_iter (σ : CanonStrat E S A (B ⊕ A)) : rep (iter σ) = iterT (rep σ) :=
  rep_toCanon_adm (admissible_iterT (admissible_rep σ))

end Rep

/-! ## Laws -/

section Laws

variable (σ : CanonStrat E S A B)

/-- **Associativity.** -/
theorem seq_assoc (τ : CanonStrat E S B C) (υ : CanonStrat E S C D) :
    seq (seq σ τ) υ = seq σ (seq τ υ) :=
  rep_injective (by simp only [rep_seq, seqT_assoc])

theorem seq_pure : seq σ pure = σ := rep_injective (by simp only [rep_seq, rep_pure, seqT_pureT])

theorem pure_seq : seq pure σ = σ := rep_injective (by simp only [rep_seq, rep_pure, pureT_seqT])

theorem map_id : map σ id = σ := rep_injective (by simp only [rep_map, mapT_id])

theorem map_map (h : B → C) (h' : C → D) : map (map σ h) h' = map σ (h' ∘ h) :=
  rep_injective (by simp only [rep_map, mapT_mapT])

theorem comap_id : comap σ id = σ := rep_injective (by simp only [rep_comap, comapT_id])

theorem comap_comap {A' A'' : Type u} (k : A' → A) (k' : A'' → A') :
    comap (comap σ k) k' = comap σ (k ∘ k') :=
  rep_injective (by simp only [rep_comap, comapT_comapT])

theorem map_comap {A' : Type u} (k : A' → A) (h : B → C) :
    map (comap σ k) h = comap (map σ h) k :=
  rep_injective (by simp only [rep_map, rep_comap, mapT_comapT])

theorem seq_pure_map (h : B → C) : seq σ (map pure h) = map σ h :=
  rep_injective (by simp only [rep_seq, rep_map, rep_pure, seqT_pureT_mapT])

theorem pure_map_seq (h : A → B) (τ : CanonStrat E S B C) : seq (map pure h) τ = comap τ h :=
  rep_injective (by simp only [rep_seq, rep_map, rep_pure, rep_comap, pureT_mapT_seqT])

theorem seq_map (h : B → C) (τ : CanonStrat E S C D) : seq (map σ h) τ = seq σ (comap τ h) :=
  rep_injective (by simp only [rep_seq, rep_map, rep_comap, seqT_mapT])

theorem map_seq (τ : CanonStrat E S B C) (h : C → D) : map (seq σ τ) h = seq σ (map τ h) :=
  rep_injective (by simp only [rep_seq, rep_map, mapT_seqT])

theorem comap_seq {A' : Type u} (τ : CanonStrat E S B C) (k : A' → A) :
    comap (seq σ τ) k = seq (comap σ k) τ :=
  rep_injective (by simp only [rep_seq, rep_comap, comapT_seqT])

theorem whiskerRight_pure : whiskerRight (pure : CanonStrat E S A A) C = pure :=
  rep_injective (by simp only [rep_whiskerRight, rep_pure, whiskerRightT_pureT])

theorem whiskerLeft_pure : whiskerLeft C (pure : CanonStrat E S A A) = pure :=
  rep_injective (by simp only [rep_whiskerLeft, rep_pure, whiskerLeftT_pureT])

/-- **Right whiskering preserves sequencing.** -/
theorem whiskerRight_seq (τ : CanonStrat E S B D) (C : Type u) :
    whiskerRight (seq σ τ) C = seq (whiskerRight σ C) (whiskerRight τ C) :=
  rep_injective (by simp only [rep_whiskerRight, rep_seq, whiskerRightT_seqT])

/-- **Left whiskering preserves sequencing.** -/
theorem whiskerLeft_seq (τ : CanonStrat E S B D) (C : Type u) :
    whiskerLeft C (seq σ τ) = seq (whiskerLeft C σ) (whiskerLeft C τ) :=
  rep_injective (by simp only [rep_whiskerLeft, rep_seq, whiskerLeftT_seqT])

end Laws

/-- **The interchange law fails**: `CanonStrat` is premonoidal, not monoidal. -/
theorem not_interchange :
    ∃ (E : Sig.{0}) (σ τ : CanonStrat E PUnit PUnit PUnit),
      seq (whiskerRight σ PUnit) (whiskerLeft PUnit τ) ≠
        seq (whiskerLeft PUnit τ) (whiskerRight σ PUnit) :=
  let ⟨E, t, u, h⟩ := not_interchangeD
  ⟨E, toCanon t, toCanon u, fun he => h (congrArg Subtype.val he)⟩

/-! ### Copairing -/

section Case

variable (σ : CanonStrat E S A C) (τ : CanonStrat E S B C)

theorem comap_inl_case : comap (case σ τ) Sum.inl = σ :=
  rep_injective (by simp only [rep_comap, rep_case, comapT_inl_caseT])

theorem comap_inr_case : comap (case σ τ) Sum.inr = τ :=
  rep_injective (by simp only [rep_comap, rep_case, comapT_inr_caseT])

/-- Copairing after the left injection is the left component. -/
theorem pure_map_inl_seq_case : seq (map pure Sum.inl) (case σ τ) = σ :=
  rep_injective (by simp only [rep_seq, rep_map, rep_pure, rep_case, pureT_mapT_inl_seqT_caseT])

/-- Copairing after the right injection is the right component. -/
theorem pure_map_inr_seq_case : seq (map pure Sum.inr) (case σ τ) = τ :=
  rep_injective (by simp only [rep_seq, rep_map, rep_pure, rep_case, pureT_mapT_inr_seqT_caseT])

/-- The copairing of the injections is the identity. -/
theorem case_pure_map :
    case (map pure Sum.inl) (map pure Sum.inr) = (pure : CanonStrat E S (A ⊕ B) (A ⊕ B)) :=
  rep_injective (by simp only [rep_case, rep_map, rep_pure, caseT_pureT_mapT])

/-- Sequencing distributes over copairing on the left. -/
theorem seq_case (υ : CanonStrat E S C D) : seq (case σ τ) υ = case (seq σ υ) (seq τ υ) :=
  rep_injective (by simp only [rep_seq, rep_case, seqT_caseT])

end Case

/-! ### Iteration -/

/-- **The fixpoint law.** -/
theorem iter_unfold (σ : CanonStrat E S A (B ⊕ A)) : iter σ = seq σ (case pure (iter σ)) :=
  rep_injective (by simp only [rep_iter, rep_seq, rep_case, rep_pure]; exact iterT_unfold _)

/-- **Naturality of iteration in the output.** -/
theorem iter_map (σ : CanonStrat E S A (B ⊕ A)) (h : B → C) :
    iter (map σ (Sum.map h id)) = map (iter σ) h :=
  rep_injective (by simp only [rep_iter, rep_map, iterT_mapT])

/-- **Uniformity of iteration** for a pure map `h`: if `h ; F = G ; [inl, inr ∘ h]` then
`h ; iter F = iter G`. -/
theorem iter_uniform {A' : Type u} {F : CanonStrat E S A (B ⊕ A)} {G : CanonStrat E S A' (B ⊕ A')}
    (h : A' → A)
    (hFG : seq (map pure h) F = seq G (case (map pure Sum.inl) (map pure (Sum.inr ∘ h)))) :
    seq (map pure h) (iter F) = iter G := by
  have := congrArg rep hFG
  simp only [rep_seq, rep_map, rep_pure, rep_case] at this
  exact rep_injective
    (by simp only [rep_seq, rep_map, rep_pure, rep_iter]; exact iterT_uniform h this)

/-- **Dinaturality of iteration**: for `σ : A → B ⊕ C` and `τ : C → B ⊕ A`,
`iter (σ ; [inl, τ]) = σ ; [id, iter (τ ; [inl, σ])]`. -/
theorem iter_dinat (σ : CanonStrat E S A (B ⊕ C)) (τ : CanonStrat E S C (B ⊕ A)) :
    iter (seq σ (case (map pure Sum.inl) τ)) =
      seq σ (case pure (iter (seq τ (case (map pure Sum.inl) σ)))) :=
  rep_injective (by
    simp only [rep_iter, rep_seq, rep_case, rep_map, rep_pure]
    exact iterT_dinat _ _)

end CanonStrat

end Silmaril.Games.Abstract
