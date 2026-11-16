module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder
open Silmaril.Logic.Institution.Examples

abbrev TargetTerm (A : Signature) {k} (Γ : Fin k → TargetSort) (s : TargetSort) :=
  EQ.Term (signature A).toSignature Γ s

abbrev heapContext {k} (Γ : Fin k → TargetSort) : Fin (k+1) → TargetSort :=
  contextCons .heap Γ

def liftHeap {A : Signature} {k} {Γ : Fin k → TargetSort} {s} (t : TargetTerm A Γ s) :
    TargetTerm A (heapContext Γ) s := liftTerm (S := (signature A).toSignature) TargetSort.heap t

def forallFormula {A : Signature} {k} {Γ : Fin k → TargetSort} (s : TargetSort)
    (p : FOL.Formula (signature A) (Fin.cases s Γ)) : FOL.Formula (signature A) Γ :=
  .all rfl p

def existsFormula {A : Signature} {k} {Γ : Fin k → TargetSort} (s : TargetSort)
    (p : FOL.Formula (signature A) (Fin.cases s Γ)) : FOL.Formula (signature A) Γ :=
  .not (forallFormula s (.not p))

def impliesFormula {A : Signature} {k} {Γ : Fin k → TargetSort}
    (p q : FOL.Formula (signature A) Γ) : FOL.Formula (signature A) Γ :=
  .not (.and p (.not q))

def joinFormula {A : Signature} {k} {Γ : Fin k → TargetSort}
    (a b c : TargetTerm A Γ .heap) : FOL.Formula (signature A) Γ :=
  .rel .join (Fin.cases a (Fin.cases b (fun _ => c)))

def ownershipFormula {A : Signature} {k n} {Γ : Fin k → TargetSort}
    (a : A.Atom n) (args : Fin n → TargetTerm A Γ .value) (h : TargetTerm A Γ .heap) :
    FOL.Formula (signature A) Γ :=
  .rel (.atom a) (Fin.cases
    (motive := fun i => TargetTerm A Γ (pointerHeapTargetSorts n i)) h args)

/-- Actual spatial assertion compilation: heap splitting and extension become
ordinary quantification over the exact resource carrier. -/
def assertion {A : Signature} {k} : {l : Nat} → {Γ : Fin l → TargetSort} →
    Assertion A k → (Fin k → TargetTerm A Γ .value) → TargetTerm A Γ .heap →
      FOL.Formula (signature A) Γ
  | _, _, .eq t u, σ, _ => .eq (term σ t) (term σ u)
  | _, _, .atom a args, σ, h => ownershipFormula a (fun i => term σ (args i)) h
  | _, _, .emp, _, h => .eq h (.app .unit (fun i => i.elim0))
  | _, _, .neg p, σ, h => .not (assertion p σ h)
  | _, _, .conj p q, σ, h => .and (assertion p σ h) (assertion q σ h)
  | _, _, .sep p q, σ, h => existsFormula .heap (existsFormula .heap
      (.and (joinFormula (.var 1) (.var 0) (liftHeap (liftHeap h)))
        (.and (assertion p (fun i => liftHeap (liftHeap (σ i))) (.var 1))
          (assertion q (fun i => liftHeap (liftHeap (σ i))) (.var 0)))))
  | _, _, .wand p q, σ, h => forallFormula .heap (forallFormula .heap
      (impliesFormula (joinFormula (liftHeap (liftHeap h)) (.var 1) (.var 0))
        (impliesFormula (assertion p (fun i => liftHeap (liftHeap (σ i))) (.var 1))
          (assertion q (fun i => liftHeap (liftHeap (σ i))) (.var 0)))))

def tupleContext {l} (n : Nat) (Γ : Fin l → TargetSort) : Fin ((n+1)+l) → TargetSort :=
  Fin.addCases (pointerHeapTargetSorts n) Γ

def tupleHeap {A : Signature} {l} (n : Nat) (Γ : Fin l → TargetSort) :
    TargetTerm A (tupleContext n Γ) .heap :=
  Eq.mp (congrArg (fun s => TargetTerm A (tupleContext n Γ) s)
    (by simp [tupleContext,pointerHeapTargetSorts])) (.var ((0 : Fin (n+1)).castAdd l))

def tupleValue {A : Signature} {l} (n : Nat) (Γ : Fin l → TargetSort) (j : Fin n) :
    TargetTerm A (tupleContext n Γ) .value :=
  Eq.mp (congrArg (fun s => TargetTerm A (tupleContext n Γ) s)
    (by simp [tupleContext,pointerHeapTargetSorts])) (.var (j.succ.castAdd l))

def tupleAmbientVar {A : Signature} {l} (n : Nat) (Γ : Fin l → TargetSort) (i : Fin l) :
    TargetTerm A (tupleContext n Γ) (Γ i) :=
  Eq.mp (congrArg (fun s => TargetTerm A (tupleContext n Γ) s)
    (by simp [tupleContext])) (.var (Fin.natAdd (n+1) i))

def bodyValues {A : Signature} {k l} {Γ : Fin l → TargetSort} (n : Nat)
    (σ : Fin k → TargetTerm A Γ .value) : Fin (n+k) → TargetTerm A (tupleContext n Γ) .value :=
  Fin.addCases (tupleValue n Γ) (fun i => substitute (tupleAmbientVar n Γ) (σ i))

def boundValues {A : Signature} {k l} {Γ : Fin l → TargetSort}
    (σ : Fin k → TargetTerm A Γ .value) : Fin (k+1) → TargetTerm A (contextCons .value Γ) .value :=
  Fin.cases (.var 0) (fun i => liftTerm (S := (signature A).toSignature) TargetSort.value (σ i))

def recursiveArgs {A : Signature} {n l} {Γ : Fin l → TargetSort}
    (h : TargetTerm A Γ .heap) (args : Fin n → TargetTerm A Γ .value) :
    ∀ i, TargetTerm A Γ (pointerHeapTargetSorts n i) :=
  Fin.cases (motive := fun i => TargetTerm A Γ (pointerHeapTargetSorts n i)) h args

/-- Positive source recursion compiles to the existing n-ary sorted FO(LFP)
syntax, with heap head, pointer tuple and retained ambient object parameters. -/
def pattern {A : Signature} : {r k : Nat} → {P : Fin r → Nat} → Pattern A P k →
    {l : Nat} → {Γ : Fin l → TargetSort} →
    (Fin k → TargetTerm A Γ .value) → TargetTerm A Γ .heap →
    Silmaril.Logic.FirstOrderLFP.Formula (signature A) (fun i => profile A (P i)) Γ
  | _, _, _, .base p, _, _, σ, h => .base (assertion p σ h)
  | _, _, _, .pred i args, _, _, σ, h => .pred i (recursiveArgs h (fun j => term σ (args j)))
  | _, _, _, .conj p q, _, _, σ, h => .conj (pattern p σ h) (pattern q σ h)
  | _, _, _, .disj p q, _, _, σ, h => .disj (pattern p σ h) (pattern q σ h)
  | _, _, _, .sep p q, _, _, σ, h => .ex (.ex
      (.conj (.base (joinFormula (.var 1) (.var 0) (liftHeap (liftHeap h))))
        (.conj (pattern p (fun i => liftHeap (liftHeap (σ i))) (.var 1))
          (pattern q (fun i => liftHeap (liftHeap (σ i))) (.var 0)))))
  | _, _, _, .wand p q, _, _, σ, h => .all (.all
      (.disj (.base (.not (.and (joinFormula (liftHeap (liftHeap h)) (.var 1) (.var 0))
          (assertion p (fun i => liftHeap (liftHeap (σ i))) (.var 1)))))
        (pattern q (fun i => liftHeap (liftHeap (σ i))) (.var 0))))
  | _, _, _, .ex p, _, _, σ, h => .ex (pattern p (boundValues σ)
      (liftTerm (S := (signature A).toSignature) TargetSort.value h))
  | _, _, _, .all p, _, _, σ, h => .all (pattern p (boundValues σ)
      (liftTerm (S := (signature A).toSignature) TargetSort.value h))
  | _, _, _, .lfp (P' := P') body args, _, Γ, σ, h =>
      .lfp (Δ := tupleContext (P' 0) Γ)
        (by funext i; simp [tupleContext]) (by funext i; simp [tupleContext])
        (pattern body (bodyValues (P' 0) σ) (tupleHeap (P' 0) Γ))
        (recursiveArgs h (fun j => term σ (args j)))

end Silmaril.Logic.Separation.Parameterized.FirstOrder
