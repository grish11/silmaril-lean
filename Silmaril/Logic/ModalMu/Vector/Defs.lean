module

public import Silmaril.Logic.ModalMu.Substitution.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.ModalMu.Vector
open CategoryTheory

/-- Uniform block kind: false=least, true=greatest. -/
def fixed {α : Type} [CompleteLattice α] (greatest : Bool) : (α →o α) →o α :=
  if greatest then OrderHom.gfp else OrderHom.lfp

def secondAt {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (f : (α × β) →o (α × β)) (x : α) : β →o β where
  toFun y := (f (x, y)).2
  monotone' := by
    intro y y' h
    have hp : (x, y) ≤ (x, y') := ⟨le_rfl, h⟩
    exact (f.mono hp).2

def secondSolutions {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (greatest : Bool) (f : (α × β) →o (α × β)) : α →o β where
  toFun x := fixed greatest (secondAt f x)
  monotone' := by
    intro x x' h
    apply (fixed greatest).mono
    intro y
    have hp : (x, y) ≤ (x', y) := ⟨h, le_rfl⟩
    exact (f.mono hp).2

def reduced {α β : Type} [CompleteLattice α] [CompleteLattice β]
    (greatest : Bool) (f : (α × β) →o (α × β)) : α →o α where
  toFun x := (f (x, secondSolutions greatest f x)).1
  monotone' := by
    intro x x' h
    have hp : (x, secondSolutions greatest f x) ≤ (x', secondSolutions greatest f x') :=
      ⟨h, (secondSolutions greatest f).mono h⟩
    exact (f.mono hp).1

/-- Two genuine simultaneous equations. Body indices0 and1 denote X and Y;
all remaining indices are captured outer set variables. -/
structure System (S : Signature) (n : Nat) where
  first : Formula S (n+2)
  second : Formula S (n+2)

def pairEnv {W : Type} {n : Nat} (ρ : Env W n) : (Set W × Set W) →o Env W (n+2) where
  toFun P := extend (extend ρ P.2) P.1
  monotone' := by
    intro P Q h i
    refine Fin.cases h.1 (fun j => ?_) i
    exact Fin.cases h.2 (fun _ => le_rfl) j

/-- Independent simultaneous powerset semantics; not defined by a compiler. -/
def System.operator {S : Signature} {n : Nat} (s : System S n) (M : Model S) (ρ : Env M.World n) :
    (Set M.World × Set M.World) →o (Set M.World × Set M.World) where
  toFun P := (s.first.denote M (pairEnv ρ P), s.second.denote M (pairEnv ρ P))
  monotone' := fun _ _ h => ⟨(s.first.denote M).mono ((pairEnv ρ).mono h),
    (s.second.denote M).mono ((pairEnv ρ).mono h)⟩

def System.denote {S : Signature} {n : Nat} (s : System S n) (greatest : Bool)
    (M : Model S) (ρ : Env M.World n) : Set M.World × Set M.World :=
  fixed greatest (s.operator M ρ)

def binder {S : Signature} {n : Nat} (greatest : Bool) (p : Formula S (n+1)) : Formula S n :=
  if greatest then .nu p else .mu p

/-- Swap only the two equation variables; captured outer indices stay fixed. -/
def swap (n : Nat) : Fin (n+2) → Fin (n+2) :=
  Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))

/-- Solve Y at a free X. The fresh inner binder has index0, and X moves to1. -/
def System.secondParam {S : Signature} {n : Nat} (s : System S n) (greatest : Bool) : Formula S (n+1) :=
  binder greatest (s.second.renameVars (swap n))

def System.firstScalar {S : Signature} {n : Nat} (s : System S n) (greatest : Bool) : Formula S n :=
  binder greatest (s.first.substitute
    (Fin.cases (.var 0) (Fin.cases (s.secondParam greatest) (fun i => .var i.succ))))

def System.secondScalar {S : Signature} {n : Nat} (s : System S n) (greatest : Bool) : Formula S n :=
  (s.secondParam greatest).substitute (Fin.cases (s.firstScalar greatest) (fun i => .var i))

def System.map {S T : Signature} {n : Nat} (f : S ⟶ T) (s : System S n) : System T n :=
  ⟨s.first.map f, s.second.map f⟩

/-- Reindex only captured variables, preserving both equation coordinates. -/
def System.renameOuter {S : Signature} {n m : Nat} (s : System S n) (g : Fin n → Fin m) : System S m :=
  ⟨s.first.renameVars (liftVars (liftVars g)), s.second.renameVars (liftVars (liftVars g))⟩

end Silmaril.Logic.ModalMu.Vector
