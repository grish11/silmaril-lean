module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Sums.Thms

/-! # Exact sums of finite families and the fold along a tag map

A family is `A : Fin (m + 1) → τ`. Its sum is nested to the right:
`A 0 + (A 1 + (… + A m))`.

A tag map `f : Fin (N + 1) → Fin (m + 1)` gives every source state `k`
the payload `A (f k)` of its class. `tagFold A f` is the class map from
the sum of the source states to the sum of the classes. The source states
may come in any order.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The exact sum of a finite family, nested to the right. -/
def famSum : (m : Nat) → (Fin (m + 1) → τ) → τ
  | 0, A => A 0
  | m + 1, A => Silmaril.coprod (A 0) (famSum m fun i => A i.succ)

/-- The injection of summand `i`. -/
noncomputable def famInj : (m : Nat) → (A : Fin (m + 1) → τ) → (i : Fin (m + 1)) →
    (ofType (Φ := Φ) (A i) ⟶ ofType (famSum m A))
  | 0, A, i => Fin.cases (motive := fun i => ofType (Φ := Φ) (A i) ⟶ ofType (A 0)) (𝟙 _) (fun j => j.elim0) i
  | m + 1, A, i => Fin.cases (motive := fun i => ofType (Φ := Φ) (A i) ⟶ ofType (famSum (m + 1) A))
      (sumInl (A 0) _) (fun j => famInj m (fun i => A i.succ) j ≫ sumInr (A 0) _) i

/-- Case analysis on the sum of a family. -/
noncomputable def famDesc {T : τ} : (m : Nat) → (A : Fin (m + 1) → τ) →
    (∀ i, ofType (Φ := Φ) (A i) ⟶ ofType T) → (ofType (Φ := Φ) (famSum m A) ⟶ ofType T)
  | 0, _, x => x 0
  | m + 1, A, x => sumDesc (x 0) (famDesc m (fun i => A i.succ) fun i => x i.succ)

/-- The sum of the family with summand `i` left out. There are at least
two summands. -/
def famRest : (m : Nat) → (A : Fin (m + 2) → τ) → Fin (m + 2) → τ
  | 0, A, i => Fin.cases (A (Fin.succ 0)) (fun _ => A 0) i
  | m + 1, A, i => Fin.cases (famSum (m + 1) fun k => A k.succ)
      (fun j => Silmaril.coprod (A 0) (famRest m (fun k => A k.succ) j)) i

/-- The other summands, into the whole sum. -/
noncomputable def famMiss : (m : Nat) → (A : Fin (m + 2) → τ) → (i : Fin (m + 2)) →
    (ofType (Φ := Φ) (famRest m A i) ⟶ ofType (famSum (m + 1) A))
  | 0, A, i => Fin.cases (motive := fun i => ofType (Φ := Φ) (famRest 0 A i) ⟶ ofType (famSum 1 A))
      (sumInr (A 0) (A (Fin.succ 0))) (fun _ => sumInl (A 0) (A (Fin.succ 0))) i
  | m + 1, A, i => Fin.cases
      (motive := fun i => ofType (Φ := Φ) (famRest (m + 1) A i) ⟶ ofType (famSum (m + 2) A))
      (sumInr (A 0) _)
      (fun j => sumDesc (sumInl (A 0) _) (famMiss m (fun k => A k.succ) j ≫ sumInr (A 0) _)) i

variable {m N : Nat}

/-- The class map of a tag map: source state `k` goes to class `f k`. -/
noncomputable def tagFold (A : Fin (m + 1) → τ) (f : Fin (N + 1) → Fin (m + 1)) :
    ofType (Φ := Φ) (famSum N fun k => A (f k)) ⟶ ofType (famSum m A) :=
  famDesc N (fun k => A (f k)) fun k => famInj m A (f k)

/-- One source state of each class: class `c` goes to state `g c`. -/
noncomputable def tagSection (A : Fin (m + 1) → τ) (f : Fin (N + 1) → Fin (m + 1))
    (g : Fin (m + 1) → Fin (N + 1)) (hg : ∀ c, f (g c) = c) :
    ofType (Φ := Φ) (famSum m A) ⟶ ofType (famSum N fun k => A (f k)) :=
  famDesc m A fun c =>
    eqToHom (congrArg (fun i => ofType (Φ := Φ) (A i)) (hg c).symm) ≫ famInj N (fun k => A (f k)) (g c)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
