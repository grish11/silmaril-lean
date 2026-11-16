module

public import Silmaril.Logic.Matching.FirstOrder.Thms
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder

variable {S : Type} {A : Algebraic.ManySorted.Signature S}

/-- Lift a variable-index map through one sorted de Bruijn binder. -/
def liftIndex {k l : Nat} (f : Fin k → Fin l) : Fin (k + 1) → Fin (l + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

theorem liftSort {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i) (bound : S) :
    ∀ i : Fin (k + 1),
      (Fin.cases bound Δ : Fin (l + 1) → S) (liftIndex f i) =
      (Fin.cases bound Γ : Fin (k + 1) → S) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact h j

/-- Sort-preserving renaming, lifted under every actual existential binder. -/
def Pattern.rename {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S} {s : S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i) : Pattern A Γ s → Pattern A Δ s
  | .var i => (h i) ▸ Pattern.var (f i)
  | .app op args => .app op (fun i => (args i).rename f h)
  | .neg p => .neg (p.rename f h)
  | .conj p q => .conj (p.rename f h) (q.rename f h)
  | .ex bound body => .ex bound (body.rename (liftIndex f) (liftSort f h bound))

/-- Free ambient coordinates; index0 under an existential is bound, not free. -/
def Pattern.free {k : Nat} {Γ : Fin k → S} {s : S} : Pattern A Γ s → Finset (Fin k)
  | .var i => {i}
  | .app _ args => Finset.univ.biUnion (fun i => (args i).free)
  | .neg p => p.free
  | .conj p q => p.free ∪ q.free
  | .ex _ body => Finset.univ.filter (fun i => i.succ ∈ body.free)

/-- Pull a target assignment back along a sort-preserving index map. -/
def Model.pullback (M : Model A) {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i)
    (a : (i : Fin l) → M.carrier (Δ i)) : (i : Fin k) → M.carrier (Γ i) :=
  fun i => cast (congrArg M.carrier (h i)) (a (f i))

/-- Redirect precisely coordinate j to the newly bound variable. -/
def closeIndex {k : Nat} (j i : Fin k) : Fin (k + 1) :=
  if i = j then 0 else i.succ

theorem closeSort {k : Nat} (Γ : Fin k → S) (j i : Fin k) :
    Fin.cases (Γ j) Γ (closeIndex j i) = Γ i := by
  by_cases same : i = j
  · subst i
    simp [closeIndex]
  · simp [closeIndex, same]

/-- Existentially bind one selected ambient coordinate, leaving the context
unchanged. Its free occurrences become index0 of a real native `.ex`. -/
def Pattern.close {k : Nat} {Γ : Fin k → S} {s : S} (j : Fin k)
    (p : Pattern A Γ s) : Pattern A Γ s :=
  .ex (Γ j) (p.rename (closeIndex j) (closeSort Γ j))

/-- Simultaneous finite abstraction implemented by actual sorted binders. -/
def Pattern.abstractList {k : Nat} {Γ : Fin k → S} {s : S}
    (xs : List (Fin k)) (p : Pattern A Γ s) : Pattern A Γ s :=
  xs.foldr Pattern.close p

noncomputable def Pattern.abstract {k : Nat} {Γ : Fin k → S} {s : S}
    (X : Finset (Fin k)) (p : Pattern A Γ s) : Pattern A Γ s :=
  p.abstractList X.toList

/-- Disjoint native contexts for independently quantified claim and rule variables. -/
def joinedContext {k n : Nat} (Γ : Fin k → S) (Δ : Fin n → S) : Fin (k + n) → S :=
  Fin.addCases Γ Δ

theorem leftSort {k n : Nat} (Γ : Fin k → S) (Δ : Fin n → S) (i : Fin k) :
    joinedContext Γ Δ (Fin.castAdd n i) = Γ i := Fin.addCases_left i

theorem rightSort {k n : Nat} (Γ : Fin k → S) (Δ : Fin n → S) (i : Fin n) :
    joinedContext Γ Δ (Fin.natAdd k i) = Δ i := Fin.addCases_right i

def Model.joinAssignment (M : Model A) {k n : Nat} {Γ : Fin k → S} {Δ : Fin n → S}
    (a : (i : Fin k) → M.carrier (Γ i)) (b : (i : Fin n) → M.carrier (Δ i)) :
    (i : Fin (k + n)) → M.carrier (joinedContext Γ Δ i) :=
  Fin.addCases
    (fun i => cast (congrArg M.carrier (leftSort Γ Δ i).symm) (a i))
    (fun i => cast (congrArg M.carrier (rightSort Γ Δ i).symm) (b i))

end Silmaril.Logic.Matching.FirstOrder
