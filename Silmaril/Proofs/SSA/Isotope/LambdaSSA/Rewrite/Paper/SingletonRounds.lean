module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Rounds.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonRounds

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Rounds
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open Paper.Extension.Singleton.ThreeCycle (triple projectStep_thenOnRepeat)
open Semantics.Categorical (roundsStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {A B : τ}

set_option backward.isDefEq.respectTransparency false

/-- A larger seed keeps every equation between projected arrows. -/
theorem projection_map_of_le {Small : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (incl : ∀ {Γ r s L}, Small Γ r s L → Seed Γ r s L)
    {X Y : Paper.TypeCategory (τ := τ) Φ} {a b : X ⟶ Y}
    (h : (projection Small).map a = (projection Small).map b) :
    (projection Seed).map a = (projection Seed).map b := by
  let G : TypeCategory Small ⥤ TypeCategory Seed :=
    CategoryTheory.Quotient.lift (homRel Small) (projection Seed) <| by
      rintro _ _ _ _ ⟨r, s, hr, hs, hf, hg, eqv⟩
      exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed incl⟩
  exact congrArg G.map h

theorem inl_typed : ValueBranches [B] (.br 0 (.inl (.var 0)) : Region Φ) [Silmaril.coprod B A] :=
  .br rfl (.inl (.var rfl))

theorem then_typed {s t : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A])
    (ht : ValueBranches [A] t [Silmaril.coprod B A]) :
    ValueBranches [A] (thenRegion s t) [Silmaril.coprod B A] :=
  seqValueBranches hs (caseValueBranches inl_typed ht)

theorem rounds_typed {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) :
    ∀ n, ValueBranches [A] (roundsRegion s n) [Silmaril.coprod B A]
  | 0 => hs
  | n + 1 => then_typed hs (rounds_typed hs n)

theorem ofRegion_then {s t : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A])
    (ht : ValueBranches [A] t [Silmaril.coprod B A]) :
    ofRegion Seed (then_typed hs ht) = thenExact Seed (ofRegion Seed hs) (ofRegion Seed ht) := by
  have inl : (sumCofan Seed B A).inl = ofRegion Seed (inl_typed (Φ := Φ) (A := A) (B := B)) :=
    congrArg (projection Seed).map (Paper.TypeCategory.sumCofan_inl (Φ := Φ) B A)
  unfold thenExact
  rw [inl, exactCopair_ofRegion]
  exact (congrArg (projection Seed).map
    (Paper.TypeCategory.ofRegion_comp hs (caseValueBranches inl_typed ht)
      (seqValueBranches hs (caseValueBranches inl_typed ht)))).symm.trans
    ((projection Seed).map_comp _ _)

theorem ofRegion_rounds {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) :
    ∀ n, ofRegion Seed (rounds_typed hs n) = rounds Seed (ofRegion Seed hs) n
  | 0 => rfl
  | n + 1 => (ofRegion_then Seed hs (rounds_typed hs n)).trans
      (congrArg (thenExact Seed (ofRegion Seed hs)) (ofRegion_rounds hs n))

variable (s t r : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A))

theorem inl_copair (f : ofType Seed B ⟶ ofType Seed (Silmaril.coprod B A)) :
    (sumCofan Seed B A).inl ≫ exactCopair Seed f t = f :=
  (sumCofanIsColimit Seed B A).fac (BinaryCofan.mk f t) ⟨WalkingPair.left⟩

theorem inr_copair (f : ofType Seed B ⟶ ofType Seed (Silmaril.coprod B A)) :
    (sumCofan Seed B A).inr ≫ exactCopair Seed f t = t :=
  (sumCofanIsColimit Seed B A).fac (BinaryCofan.mk f t) ⟨WalkingPair.right⟩

theorem then_assoc :
    thenExact Seed (thenExact Seed s t) r = thenExact Seed s (thenExact Seed t r) := by
  unfold thenExact
  rw [Category.assoc]
  congr 1
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed B A)
  · rw [← Category.assoc, inl_copair, inl_copair, inl_copair]
  · rw [← Category.assoc, inr_copair, inr_copair]

theorem rounds_add (m n : Nat) :
    thenExact Seed (rounds Seed s m) (rounds Seed s n) = rounds Seed s (m + n + 1) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    change thenExact Seed (thenExact Seed s (rounds Seed s m)) (rounds Seed s n) = _
    rw [then_assoc, ih, show m + 1 + n + 1 = (m + n + 1) + 1 by omega]
    rfl

theorem rounds_rounds (m : Nat) :
    ∀ n, rounds Seed (rounds Seed s m) n = rounds Seed s (m * n + m + n)
  | 0 => by rw [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; rfl
  | n + 1 => by
    change thenExact Seed (rounds Seed s m) (rounds Seed (rounds Seed s m) n) = _
    rw [rounds_rounds m n, rounds_add, Nat.mul_succ]
    congr 1
    omega

theorem iterateSum_chosen :
    iterateSum Seed s = iterateChosen Seed (s ≫ (sumIso Seed B A).hom) := by
  change iterateSum Seed s = iterateSum Seed ((s ≫ (sumIso Seed B A).hom) ≫ (sumIso Seed B A).inv)
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem then_chosen :
    thenExact Seed s t ≫ (sumIso Seed B A).hom =
      (s ≫ (sumIso Seed B A).hom) ≫ coprod.desc coprod.inl (t ≫ (sumIso Seed B A).hom) := by
  unfold thenExact
  rw [Category.assoc, Category.assoc]
  congr 1
  have hl := sumCofan_inl_sumIso_hom Seed B A
  have hr := sumCofan_inr_sumIso_hom Seed B A
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed B A)
  · rw [← Category.assoc, inl_copair]
    exact hl.trans ((((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ coprod.desc coprod.inl (t ≫ (sumIso Seed B A).hom)) hl)).trans
        (coprod.inl_desc _ _)).symm)
  · rw [← Category.assoc, inr_copair]
    exact (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ coprod.desc coprod.inl (t ≫ (sumIso Seed B A).hom)) hr)).trans
        (coprod.inr_desc _ _)).symm

theorem rounds_chosen : ∀ n,
    rounds Seed s n ≫ (sumIso Seed B A).hom = roundsStep (s ≫ (sumIso Seed B A).hom) n
  | 0 => rfl
  | n + 1 => (then_chosen Seed s (rounds Seed s n)).trans
      (congrArg (fun k => (s ≫ (sumIso Seed B A).hom) ≫ coprod.desc coprod.inl k) (rounds_chosen n))

theorem projectStep_roundsStep {X Y : Paper.TypeCategory (τ := τ) Φ} (h : X ⟶ Y ⨿ X) : ∀ n,
    projectStep Seed (roundsStep h n) = roundsStep (projectStep Seed h) n
  | 0 => rfl
  | n + 1 => (projectStep_thenOnRepeat Seed h (roundsStep h n)).trans
      (congrArg (fun k => projectStep Seed h ≫ coprod.desc coprod.inl k) (projectStep_roundsStep h n))

theorem iterateSum_double (d : Doubles Seed) :
    iterateSum Seed (thenExact Seed s s) = iterateSum Seed s := by
  rw [iterateSum_chosen, then_chosen, d, ← iterateSum_chosen]

theorem iterateSum_triple (d : Triples Seed) :
    iterateSum Seed (thenExact Seed s (thenExact Seed s s)) = iterateSum Seed s := by
  rw [iterateSum_chosen, then_chosen, then_chosen]
  exact (d (s ≫ (sumIso Seed B A).hom)).trans (iterateSum_chosen Seed s).symm

/-- The law at the chosen coproduct gives the law at the exact sum. -/
theorem unrolls_of_roundsLaw {n : Nat} (law : RoundsLaw Seed n) : Unrolls Seed n := by
  intro A B s
  rw [iterateSum_chosen, rounds_chosen, law, ← iterateSum_chosen]

/-- The laws for two round counts give the law for their product. -/
theorem unrolls_mul {m n : Nat} (hm : Unrolls Seed m) (hn : Unrolls Seed n) :
    Unrolls Seed (m * n + m + n) := by
  intro A B s
  rw [← rounds_rounds, hn (rounds Seed s m), hm s]

/-- Round counts that are products of twos and threes unroll. -/
theorem unrolls_of_smooth (d : Doubles Seed) (t : Triples Seed) {n : Nat} (h : Smooth n) :
    Unrolls Seed n := by
  induction h with
  | one => intro A B s; rfl
  | @double m _ ih =>
    intro A B s
    rw [show 2 * m + 1 = m + m + 1 by omega, ← rounds_add, iterateSum_double Seed _ d]
    exact ih s
  | @triple m _ ih =>
    intro A B s
    rw [show 3 * m + 2 = m + (m + m + 1) + 1 by omega, ← rounds_add, ← rounds_add,
      iterateSum_triple Seed _ t]
    exact ih s

theorem ofRegion_iterateRegion {r : Region Φ} (hr : ValueBranches [A] r [Silmaril.coprod B A]) :
    ofRegion Seed (SyntacticCategory.iterateRegion_valueBranches hr) = iterateSum Seed (ofRegion Seed hr) :=
  ((iterateSum_map Seed (Paper.TypeCategory.ofRegion hr)).trans
    (congrArg (projection Seed).map (Paper.TypeCategory.iterateSum_ofRegion hr))).symm

/-- An unrolling law of the quotient equates the two written loops. -/
theorem unrolled_eqv {n : Nat} (law : Unrolls Seed n) {s : Region Φ}
    (hs : ValueBranches [A] s [Silmaril.coprod B A]) :
    Paper.Extension.Eqv Seed [A] (SyntacticCategory.iterateRegion A (roundsRegion s n))
      (SyntacticCategory.iterateRegion A s) [B] := by
  apply (ofRegion_eq_iff Seed (SyntacticCategory.iterateRegion_valueBranches (rounds_typed hs n))
    (SyntacticCategory.iterateRegion_valueBranches hs)).1
  rw [ofRegion_iterateRegion Seed (rounds_typed hs n), ofRegion_iterateRegion Seed hs,
    ofRegion_rounds, law]

/-- Conversely the written equations at every guarded step give the law. -/
theorem unrolls_of_eqv {n : Nat}
    (h : ∀ {A B : τ} {s : Region Φ} (_ : ValueBranches [A] s [Silmaril.coprod B A]),
      Paper.Extension.Eqv Seed [A] (SyntacticCategory.iterateRegion A (roundsRegion s n))
        (SyntacticCategory.iterateRegion A s) [B]) : Unrolls Seed n := by
  intro A B s
  obtain ⟨g, rfl⟩ := (projection Seed).map_surjective s
  obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
  change iterateSum Seed (rounds Seed (ofRegion Seed hr) n) = iterateSum Seed (ofRegion Seed hr)
  rw [← ofRegion_rounds, ← ofRegion_iterateRegion Seed (rounds_typed hr n),
    ← ofRegion_iterateRegion Seed hr]
  exact (ofRegion_eq_iff Seed _ _).2 (h hr)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonRounds
