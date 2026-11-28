module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Distributivity.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.DistributivityProofs

open LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
  {K A B C : τ}

local notation "prod" => ProductModel.productEquiv (D := D)
local notation "sum" => CoproductModel.coprodEquiv (D := D)
local notation "pack[" A "," B "]" => Equiv.symm (prod A B)
local notation "tag[" A "," B "]" => Equiv.symm (sum A B)

theorem run_distribLeft (k : D K) (value : D (coprod A B)) :
    (Program.distribLeft (Φ := Φ) K A B).run M (pack[K, coprod A B] (k, value)) =
      pure (tag[product K A, product K B]
        ((sum A B value).map (fun a => pack[K, A] (k, a)) (fun b => pack[K, B] (k, b)))) := by
  simp only [Program.distribLeft, Program.run, Derivation.denote, BoundEnv.snoc_zero]
  erw [pure_bind, Equiv.apply_symm_apply, pure_bind]
  change (match sum A B value with
    | .inl a => do
      let ka ← ((pure k : Tree Events (D K)) >>= fun k' =>
        (pure a : Tree Events (D A)) >>= fun a' => pure (pack[K, A] (k', a')))
      pure (tag[product K A, product K B] (.inl ka))
    | .inr b => do
      let kb ← ((pure k : Tree Events (D K)) >>= fun k' =>
        (pure b : Tree Events (D B)) >>= fun b' => pure (pack[K, B] (k', b')))
      pure (tag[product K A, product K B] (.inr kb))) = _
  cases sum A B value <;> simp only [pure_bind, Sum.map_inl, Sum.map_inr]

theorem run_distribRight (k : D K) (value : D (coprod A B)) :
    (Program.distribRight (Φ := Φ) A B K).run M (pack[coprod A B, K] (value, k)) =
      pure (tag[product A K, product B K]
        ((sum A B value).map (fun a => pack[A, K] (a, k)) (fun b => pack[B, K] (b, k)))) := by
  simp only [Program.distribRight, Program.run, Derivation.denote, BoundEnv.snoc_zero]
  erw [pure_bind, Equiv.apply_symm_apply, pure_bind]
  change (match sum A B value with
    | .inl a => do
      let ak ← ((pure a : Tree Events (D A)) >>= fun a' =>
        (pure k : Tree Events (D K)) >>= fun k' => pure (pack[A, K] (a', k')))
      pure (tag[product A K, product B K] (.inl ak))
    | .inr b => do
      let bk ← ((pure b : Tree Events (D B)) >>= fun b' =>
        (pure k : Tree Events (D K)) >>= fun k' => pure (pack[B, K] (b', k')))
      pure (tag[product A K, product B K] (.inr bk))) = _
  cases sum A B value <;> simp only [pure_bind, Sum.map_inl, Sum.map_inr]

theorem run_mergeLeft_inl (k : D K) (a : D A) :
    (Program.mergeLeft (Φ := Φ) K A B).run M (tag[product K A, product K B] (.inl (pack[K, A] (k, a)))) =
      pure (pack[K, coprod A B] (k, tag[A, B] (.inl a))) := by
  simp only [Program.mergeLeft, Program.run_desc, Equiv.apply_symm_apply, Sum.elim_inl,
    Program.run_whiskerLeft, Program.run_inl, pure_bind]

theorem run_mergeLeft_inr (k : D K) (b : D B) :
    (Program.mergeLeft (Φ := Φ) K A B).run M (tag[product K A, product K B] (.inr (pack[K, B] (k, b)))) =
      pure (pack[K, coprod A B] (k, tag[A, B] (.inr b))) := by
  simp only [Program.mergeLeft, Program.run_desc, Equiv.apply_symm_apply, Sum.elim_inr,
    Program.run_whiskerLeft, Program.run_inr, pure_bind]

theorem run_mergeRight_inl (a : D A) (k : D K) :
    (Program.mergeRight (Φ := Φ) A B K).run M (tag[product A K, product B K] (.inl (pack[A, K] (a, k)))) =
      pure (pack[coprod A B, K] (tag[A, B] (.inl a), k)) := by
  simp only [Program.mergeRight, Program.run_desc, Equiv.apply_symm_apply, Sum.elim_inl,
    Program.run_whiskerRight, Program.run_inl, pure_bind]

theorem run_mergeRight_inr (b : D B) (k : D K) :
    (Program.mergeRight (Φ := Φ) A B K).run M (tag[product A K, product B K] (.inr (pack[B, K] (b, k)))) =
      pure (pack[coprod A B, K] (tag[A, B] (.inr b), k)) := by
  simp only [Program.mergeRight, Program.run_desc, Equiv.apply_symm_apply, Sum.elim_inr,
    Program.run_whiskerRight, Program.run_inr, pure_bind]

private theorem run_id (a : D A) : (Program.id (Φ := Φ) A).run M a = pure a := rfl

theorem left_split_merge (K A B : τ) :
    (Program.setoid M policy (product K (coprod A B)) (product K (coprod A B))).r
      ((Program.distribLeft K A B).seq (Program.mergeLeft K A B)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨k, value⟩, rfl⟩ := pack[K, coprod A B].surjective input
  obtain ⟨selected, rfl⟩ := tag[A, B].surjective value
  cases selected <;> simp only [Program.run_seq, run_distribLeft, Equiv.apply_symm_apply, Sum.map_inl, Sum.map_inr,
    pure_bind, run_mergeLeft_inl, run_mergeLeft_inr, run_id]

theorem right_split_merge (A B K : τ) :
    (Program.setoid M policy (product (coprod A B) K) (product (coprod A B) K)).r
      ((Program.distribRight A B K).seq (Program.mergeRight A B K)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨value, k⟩, rfl⟩ := pack[coprod A B, K].surjective input
  obtain ⟨selected, rfl⟩ := tag[A, B].surjective value
  cases selected <;> simp only [Program.run_seq, run_distribRight, Equiv.apply_symm_apply, Sum.map_inl, Sum.map_inr,
    pure_bind, run_mergeRight_inl, run_mergeRight_inr, run_id]

theorem left_merge_split (K A B : τ) :
    (Program.setoid M policy (coprod (product K A) (product K B)) (coprod (product K A) (product K B))).r
      ((Program.mergeLeft K A B).seq (Program.distribLeft K A B)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨selected, rfl⟩ := tag[product K A, product K B].surjective input
  cases selected with
  | inl value =>
    obtain ⟨⟨k, a⟩, rfl⟩ := pack[K, A].surjective value
    simp only [Program.run_seq, run_mergeLeft_inl, pure_bind, run_distribLeft,
      Equiv.apply_symm_apply, Sum.map_inl, run_id]
  | inr value =>
    obtain ⟨⟨k, b⟩, rfl⟩ := pack[K, B].surjective value
    simp only [Program.run_seq, run_mergeLeft_inr, pure_bind, run_distribLeft,
      Equiv.apply_symm_apply, Sum.map_inr, run_id]

theorem right_merge_split (A B K : τ) :
    (Program.setoid M policy (coprod (product A K) (product B K)) (coprod (product A K) (product B K))).r
      ((Program.mergeRight A B K).seq (Program.distribRight A B K)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨selected, rfl⟩ := tag[product A K, product B K].surjective input
  cases selected with
  | inl value =>
    obtain ⟨⟨a, k⟩, rfl⟩ := pack[A, K].surjective value
    simp only [Program.run_seq, run_mergeRight_inl, pure_bind, run_distribRight,
      Equiv.apply_symm_apply, Sum.map_inl, run_id]
  | inr value =>
    obtain ⟨⟨b, k⟩, rfl⟩ := pack[B, K].surjective value
    simp only [Program.run_seq, run_mergeRight_inr, pure_bind, run_distribRight,
      Equiv.apply_symm_apply, Sum.map_inr, run_id]

private theorem pure_of_pointwise {X Y : τ} {p : Program Φ X Y}
    (result : ∀ x, ∃ r, p.run M x = pure r) : p.HasPureRun M := by
  choose value runs using result
  exact ⟨value, runs⟩

theorem left_pure (K A B : τ) : (Program.distribLeft (Φ := Φ) K A B).HasPureRun M := by
  apply pure_of_pointwise
  intro input
  obtain ⟨⟨k, value⟩, rfl⟩ := pack[K, coprod A B].surjective input
  exact ⟨_, run_distribLeft k value⟩

theorem right_pure (A B K : τ) : (Program.distribRight (Φ := Φ) A B K).HasPureRun M := by
  apply pure_of_pointwise
  intro input
  obtain ⟨⟨value, k⟩, rfl⟩ := pack[coprod A B, K].surjective input
  exact ⟨_, run_distribRight k value⟩

theorem left_merge_pure (K A B : τ) : (Program.mergeLeft (Φ := Φ) K A B).HasPureRun M := by
  apply pure_of_pointwise
  intro input
  obtain ⟨selected, rfl⟩ := tag[product K A, product K B].surjective input
  cases selected with
  | inl value =>
    obtain ⟨⟨k, a⟩, rfl⟩ := pack[K, A].surjective value
    exact ⟨_, run_mergeLeft_inl k a⟩
  | inr value =>
    obtain ⟨⟨k, b⟩, rfl⟩ := pack[K, B].surjective value
    exact ⟨_, run_mergeLeft_inr k b⟩

theorem right_merge_pure (A B K : τ) : (Program.mergeRight (Φ := Φ) A B K).HasPureRun M := by
  apply pure_of_pointwise
  intro input
  obtain ⟨selected, rfl⟩ := tag[product A K, product B K].surjective input
  cases selected with
  | inl value =>
    obtain ⟨⟨a, k⟩, rfl⟩ := pack[A, K].surjective value
    exact ⟨_, run_mergeRight_inl a k⟩
  | inr value =>
    obtain ⟨⟨b, k⟩, rfl⟩ := pack[B, K].surjective value
    exact ⟨_, run_mergeRight_inr b k⟩

theorem run_whiskerLeft_desc (p : Program Φ A C) (q : Program Φ B C) (input : D (product K (coprod A B))) :
    ((p.desc q).whiskerLeft K).run M input =
      ((Program.distribLeft K A B).seq ((p.whiskerLeft K).desc (q.whiskerLeft K))).run M input := by
  obtain ⟨⟨k, value⟩, rfl⟩ := pack[K, coprod A B].surjective input
  obtain ⟨selected, rfl⟩ := tag[A, B].surjective value
  cases selected <;> simp only [Program.run_seq, run_distribLeft, Program.run_whiskerLeft, Program.run_desc,
    Equiv.apply_symm_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, pure_bind]

theorem run_whiskerRight_desc (p : Program Φ A C) (q : Program Φ B C) (input : D (product (coprod A B) K)) :
    ((p.desc q).whiskerRight K).run M input =
      ((Program.distribRight A B K).seq ((p.whiskerRight K).desc (q.whiskerRight K))).run M input := by
  obtain ⟨⟨value, k⟩, rfl⟩ := pack[coprod A B, K].surjective input
  obtain ⟨selected, rfl⟩ := tag[A, B].surjective value
  cases selected <;> simp only [Program.run_seq, run_distribRight, Program.run_whiskerRight, Program.run_desc,
    Equiv.apply_symm_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, pure_bind]

end Silmaril.Isotope.LetCase.HandledTrace.DistributivityProofs
