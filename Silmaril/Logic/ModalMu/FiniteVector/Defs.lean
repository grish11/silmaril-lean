module

public import Silmaril.Logic.ModalMu.Vector.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.ModalMu.FiniteVector
open CategoryTheory

/-- A finite uniform block. Equation variables precede the captured outer variables. -/
structure System (S : Signature) (k n : Nat) where
  body : Fin k → Formula S (k+n)

/-- Join the equation valuation and captured outer valuation. -/
def joinEnv {W : Type} {k n : Nat} (ρ : Env W n) (X : Env W k) : Env W (k+n) :=
  Fin.addCases X ρ

def System.operator {S : Signature} {k n : Nat} (s : System S k n)
    (M : Model S) (ρ : Env M.World n) : Env M.World k →o Env M.World k where
  toFun X i := (s.body i).denote M (joinEnv ρ X)
  monotone' := by
    intro X Y h i
    apply (s.body i).denote M |>.mono
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [joinEnv] using h i
    · simp [joinEnv]

/-- Independent simultaneous semantics on the complete product powerset lattice. -/
def System.denote {S : Signature} {k n : Nat} (s : System S k n) (greatest : Bool)
    (M : Model S) (ρ : Env M.World n) : Env M.World k :=
  Vector.fixed greatest (s.operator M ρ)

/-- Move the first equation variable into the first captured slot. -/
def tailIndex (k n : Nat) : Fin (k+1+n) → Fin (k+(n+1)) :=
  Fin.addCases (Fin.cases (Fin.natAdd k 0) (fun i => Fin.castAdd (n+1) i))
    (fun i => Fin.natAdd k i.succ)

def System.tail {S : Signature} {k n : Nat} (s : System S (k+1) n) : System S k (n+1) :=
  ⟨fun i => (s.body i.succ).renameVars (tailIndex k n)⟩

/-- Substitute the parametric tail solutions, keeping the head variable free. -/
def headSub {S : Signature} {k n : Nat} (tail : Fin k → Formula S (n+1)) :
    Fin (k+1+n) → Formula S (n+1) :=
  Fin.addCases (Fin.cases (.var 0) tail) (fun i => .var i.succ)

/-- Recursive Bekič elimination. Both the number of equations and captured
variables are arbitrary; output consists of actual scalar ModalMu formulas. -/
def System.compile {S : Signature} (greatest : Bool) :
    {k n : Nat} → System S k n → Fin k → Formula S n
  | 0, _, _ => Fin.elim0
  | _k+1, _, s =>
      let tail := s.tail.compile greatest
      let head := Vector.binder greatest ((s.body 0).substitute (headSub tail))
      Fin.cases head (fun i => (tail i).substitute (Fin.cases head Formula.var))

def System.map {S T : Signature} {k n : Nat} (f : S ⟶ T) (s : System S k n) : System T k n :=
  ⟨fun i => (s.body i).map f⟩

/-- Reindex captured variables while fixing every equation coordinate. -/
def System.renameOuter {S : Signature} {k n m : Nat} (s : System S k n)
    (g : Fin n → Fin m) : System S k m :=
  ⟨fun i => (s.body i).renameVars
    (Fin.addCases (Fin.castAdd m) (fun j => Fin.natAdd k (g j)))⟩

end Silmaril.Logic.ModalMu.FiniteVector
