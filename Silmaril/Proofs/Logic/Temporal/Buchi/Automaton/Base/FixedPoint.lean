module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Base.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Base
open ModalMu

theorem disjoin_denote {S : Signature} {k n : Nat} (M : Model S) (ρ : Env M.World k)
    (p : Fin n → Formula S k) (w : M.World) :
    w ∈ (disjoin p).denote M ρ ↔ ∃ i, w ∈ (p i).denote M ρ := by
  induction n with
  | zero =>
    change False ↔ ∃ i : Fin 0, _
    simp
  | succ n ih =>
    change (w ∈ (p 0).denote M ρ ∨
      w ∈ (disjoin (fun i : Fin n => p i.succ)).denote M ρ) ↔ _
    rw [ih]
    exact (@Fin.exists_fin_succ n (fun i => w ∈ (p i).denote M ρ)).symm

theorem next_denote {S : Signature} {n k : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World k)
    (X : Fin n → Formula S k) (q : Fin n) (w : M.World) :
    w ∈ (next A a X q).denote M ρ ↔
      ∃ v r, A.automaton.productStep (M.step a) (modelLabel M) (w, q) (v, r) ∧
        v ∈ (X r).denote M ρ := by
  rw [next, disjoin_denote]
  change (∃ r, w ∈ (A.guard q r).toFormula.denote M ρ ∧
    ∃ v, M.step a w v ∧ v ∈ (X r).denote M ρ) ↔ _
  constructor
  · rintro ⟨r, hg, v, hv, hx⟩
    exact ⟨v, r, ⟨hv, (Guard.toFormula_denote M ρ _ w).mp hg⟩, hx⟩
  · rintro ⟨v, r, ⟨hv, hg⟩, hx⟩
    exact ⟨r, (Guard.toFormula_denote M ρ _ w).mpr hg, v, hv, hx⟩

/-- The actual inner equation syntax has exactly the independent product μ operator. -/
theorem inner_operator {S : Signature} {n : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (Z Y : Env M.World n) :
    productSets M.World n ((innerSystem A a).operator M Z Y) =
      Buchi.inner (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting (productSets M.World n Z)
        (productSets M.World n Y) := by
  ext x
  rcases x with ⟨w, q⟩
  change w ∈ ((innerSystem A a).body q).denote M (FiniteVector.joinEnv Z Y) ↔ _
  have hZ (r : Fin n) : (Formula.var (Fin.natAdd n r) : Formula S (n+n)).denote M
      (FiniteVector.joinEnv Z Y) = Z r := by
    change Fin.addCases Y Z (Fin.natAdd n r) = Z r
    exact Fin.addCases_right r
  have hY (r : Fin n) : (Formula.var (Fin.castAdd n r) : Formula S (n+n)).denote M
      (FiniteVector.joinEnv Z Y) = Y r := by
    change Fin.addCases Y Z (Fin.castAdd n r) = Y r
    simp
  unfold innerSystem
  by_cases hq : q ∈ A.accepting
  · simp only [hq, ↓reduceIte]
    change (w ∈ (next A a (fun r => .var (Fin.natAdd n r)) q).denote M
      (FiniteVector.joinEnv Z Y) ∨ w ∈ (next A a (fun r => .var (Fin.castAdd n r)) q).denote M
      (FiniteVector.joinEnv Z Y)) ↔ _
    rw [next_denote, next_denote]
    simp only [hZ, hY]
    simp [Buchi.inner, productSets, productAccepting, Symbolic.automaton, hq]
  · simp only [hq, ↓reduceIte]
    change (False ∨ w ∈ (next A a (fun r => .var (Fin.castAdd n r)) q).denote M
      (FiniteVector.joinEnv Z Y)) ↔ _
    rw [false_or, next_denote]
    simp only [hY]
    simp [Buchi.inner, productSets, productAccepting, Symbolic.automaton, hq]

theorem inner_correct {S : Signature} {n : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (Z : Env M.World n) :
    productSets M.World n ((innerSystem A a).denote false M Z) =
      (Buchi.inner (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting (productSets M.World n Z)).lfp := by
  let e := productSets M.World n
  have hg : (FiniteVector.orderMap e).comp
      (((innerSystem A a).operator M Z).comp (FiniteVector.orderMap e.symm)) =
      Buchi.inner (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting (e Z) := by
    apply DFunLike.ext
    intro P
    change e ((innerSystem A a).operator M Z (e.symm P)) = _
    rw [inner_operator, e.apply_symm_apply]
  exact (FiniteVector.fixed_conjugate e ((innerSystem A a).operator M Z) false).trans
    (by rw [hg]; rfl)

theorem outer_operator {S : Signature} {n : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (Z : Env M.World n) :
    productSets M.World n ((outerSystem A a).operator M ρ Z) =
      Buchi.outer (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting (productSets M.World n Z) := by
  have henv : FiniteVector.joinEnv ρ Z = Z := by
    funext i
    change Fin.addCases Z ρ i = Z i
    exact Fin.addCases (fun j => Fin.addCases_left j)
      (fun j : Fin 0 => Fin.elim0 j) i
  have hvec : (outerSystem A a).operator M ρ Z = (innerSystem A a).denote false M Z := by
    change (fun q => ((innerSystem A a).compile false q).denote M
      (FiniteVector.joinEnv ρ Z)) = _
    rw [henv]
    exact FiniteVector.System.compile_correct false (innerSystem A a) M Z
  rw [hvec, inner_correct]
  rfl

theorem outer_correct {S : Signature} {n : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) :
    productSets M.World n ((outerSystem A a).denote true M ρ) =
      (Buchi.outer (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting).gfp := by
  let e := productSets M.World n
  have hg : (FiniteVector.orderMap e).comp
      (((outerSystem A a).operator M ρ).comp (FiniteVector.orderMap e.symm)) =
      Buchi.outer (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting := by
    apply DFunLike.ext
    intro P
    change e ((outerSystem A a).operator M ρ (e.symm P)) = _
    rw [outer_operator, e.apply_symm_apply]
  exact (FiniteVector.fixed_conjugate e ((outerSystem A a).operator M ρ) true).trans
    (by rw [hg]; rfl)

/-- Each actual scalar coordinate is interpreted on the original model M. -/
theorem coordinate_correct {S : Signature} {n : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (q : Fin n) (w : M.World) :
    w ∈ (coordinate A a q).denote M ρ ↔
      (w, q) ∈ (Buchi.outer (A.automaton.productStep (M.step a) (modelLabel M))
        A.automaton.productAccepting).gfp := by
  have hc := congrFun (FiniteVector.System.compile_correct true (outerSystem A a) M ρ) q
  change w ∈ ((outerSystem A a).compile true q).denote M ρ ↔ _
  rw [hc, ← outer_correct A a M ρ]
  rfl

/-- Eliminate the finite automaton state component from the model itself. -/
theorem formula_correct {S : Signature} {n : Nat} (A : Symbolic S.Atom n)
    (a : S.Action) (M : Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (formula A a).denote M ρ ↔
      A.automaton.AcceptsPath (M.step a) (modelLabel M) w := by
  classical
  rw [formula, disjoin_denote, acceptsPath_iff_gfp]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hi : q ∈ A.initial
    · simp only [hi, ↓reduceIte] at hq
      exact ⟨q, hi, (coordinate_correct A a M ρ q w).mp hq⟩
    · simp only [hi, ↓reduceIte] at hq
      exact False.elim hq
  · rintro ⟨q, hi, hq⟩
    refine ⟨q, ?_⟩
    have hi' : q ∈ A.initial := hi
    simpa only [hi', ↓reduceIte] using (coordinate_correct A a M ρ q w).mpr hq

end Silmaril.Logic.Temporal.Buchi.Automaton.Base
