module

public import Silmaril.Logic.Institution.Examples.FirstOrder
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace Silmaril.Logic.FirstOrder.Variables
open Silmaril.Logic.Institution.Examples

variable {Sg : FOL.Signature}

def liftIndex {k l : Nat} (f : Fin k → Fin l) : Fin (k + 1) → Fin (l + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

theorem consTail {k : Nat} (s : Sg.S) (Γ : Fin k → Sg.S) :
    (Fin.cases s Γ : Fin (k + 1) → Sg.S) ∘ Fin.succ = Γ := by
  funext i
  rfl

/-- The source binder may have any extension with the specified tail equality. -/
theorem liftSort {k l : Nat} {Γ : Fin k → Sg.S} {Δ : Fin l → Sg.S}
    {Ξ : Fin (k + 1) → Sg.S} (tail : Ξ ∘ Fin.succ = Γ)
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i) :
    ∀ i, Fin.cases (Ξ 0) Δ (liftIndex f i) = Ξ i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact (h j).trans (congrFun tail j).symm

def termRename {k l : Nat} {Γ : Fin k → Sg.S} {Δ : Fin l → Sg.S} {s : Sg.S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i) :
    EQ.Term Sg.toSignature Γ s → EQ.Term Sg.toSignature Δ s
  | .var i => (h i) ▸ EQ.Term.var (f i)
  | .app op args => .app op (fun j => termRename f h (args j))

/-- Actual FOL syntax renaming, including arbitrary sorted universal extensions. -/
def rename {k l : Nat} {Γ : Fin k → Sg.S} {Δ : Fin l → Sg.S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i) :
    FOL.Formula Sg Γ → FOL.Formula Sg Δ
  | .eq t u => .eq (termRename f h t) (termRename f h u)
  | .rel r args => .rel r (fun j => termRename f h (args j))
  | .tt => .tt
  | .not p => .not (rename f h p)
  | .and p q => .and (rename f h p) (rename f h q)
  | .all tail body => .all (Γ := Δ) (consTail _ Δ) (rename (liftIndex f) (liftSort tail f h) body)

def termFree {k : Nat} {Γ : Fin k → Sg.S} {s : Sg.S} :
    EQ.Term Sg.toSignature Γ s → Finset (Fin k)
  | .var i => {i}
  | .app _ args => Finset.univ.biUnion (fun j => termFree (args j))

def free {k : Nat} {Γ : Fin k → Sg.S} : FOL.Formula Sg Γ → Finset (Fin k)
  | .eq t u => termFree t ∪ termFree u
  | .rel _ args => Finset.univ.biUnion (fun j => termFree (args j))
  | .tt => ∅
  | .not p => free p
  | .and p q => free p ∪ free q
  | .all _ body => Finset.univ.filter (fun i => i.succ ∈ free body)

def pullback (M : FOL.Structure Sg) {k l : Nat} {Γ : Fin k → Sg.S} {Δ : Fin l → Sg.S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i)
    (a : (i : Fin l) → M.carrier (Δ i)) : (i : Fin k) → M.carrier (Γ i) :=
  fun i => cast (congrArg M.carrier (h i)) (a (f i))

/-- Extend an assignment along the actual tail equality of a universal binder. -/
def extendAssignment (M : FOL.Structure Sg) {k : Nat} {Γ : Fin k → Sg.S}
    {Ξ : Fin (k + 1) → Sg.S} (tail : Ξ ∘ Fin.succ = Γ)
    (x : M.carrier (Ξ 0)) (a : (i : Fin k) → M.carrier (Γ i)) :
    (i : Fin (k + 1)) → M.carrier (Ξ i) :=
  Fin.cases x (fun j => cast (congrArg M.carrier (congrFun tail j).symm) (a j))

def existsFormula {k : Nat} {Γ : Fin k → Sg.S} (s : Sg.S)
    (body : FOL.Formula Sg (Fin.cases s Γ)) : FOL.Formula Sg Γ :=
  .not (.all (Γ := Γ) (consTail s Γ) (.not body))

/-- Typed dependent assignment extension, with its context fixed explicitly. -/
def consAssignment (M : FOL.Structure Sg) {k : Nat} (s : Sg.S) (Γ : Fin k → Sg.S)
    (x : M.carrier s) (a : (i : Fin k) → M.carrier (Γ i)) :
    (i : Fin (k + 1)) → M.carrier (Fin.cases s Γ i) := Fin.cases x a

/-- Exchange the first two coordinates, leaving all outer captures unchanged. -/
def swapHead {k : Nat} : Fin (k + 1 + 1) → Fin (k + 1 + 1) :=
  Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))

theorem swapSort {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S) :
    ∀ i : Fin (k + 1 + 1),
      (Fin.cases bound (Fin.cases cfg Γ) : Fin (k + 1 + 1) → Sg.S) (swapHead i) =
      (Fin.cases cfg (Fin.cases bound Γ) : Fin (k + 1 + 1) → Sg.S) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl

/-- Bind one captured variable while retaining current configuration at slot0.
The syntax moves that slot under the binder, then discharges only the capture. -/
def existsCaptured {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S)
    (p : FOL.Formula Sg (Fin.cases cfg (Fin.cases bound Γ))) :
    FOL.Formula Sg (Fin.cases cfg Γ) :=
  existsFormula bound (rename swapHead (swapSort cfg bound Γ) p)

/-- Telescope sizes are defined recursively to avoid arithmetic context casts. -/
def blockSize : List Sg.S → Nat → Nat
  | [], k => k
  | _ :: xs, k => blockSize xs k + 1

def blockContext {k : Nat} (Γ : Fin k → Sg.S) :
    (xs : List Sg.S) → Fin (blockSize xs k) → Sg.S
  | [] => Γ
  | s :: xs => Fin.cases s (blockContext Γ xs)

/-- Ordinary finite sorted block quantification. Configuration stays slot0 in
both input and output patterns; no capture can bind the placeholder. -/
def existsBlock {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S) :
    (xs : List Sg.S) →
    FOL.Formula Sg (Fin.cases cfg (blockContext Γ xs)) →
    FOL.Formula Sg (Fin.cases cfg Γ)
  | [], p => p
  | s :: xs, p => existsBlock cfg Γ xs
      (existsCaptured cfg s (blockContext Γ xs) p)

theorem capturedShiftSort {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S) :
    ∀ i : Fin (k + 1),
      (Fin.cases cfg (Fin.cases bound Γ) : Fin (k + 1 + 1) → Sg.S)
          (liftIndex Fin.succ i) = (Fin.cases cfg Γ : Fin (k + 1) → Sg.S) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Add an unused capture after the current-configuration coordinate. -/
def weakenCaptured {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S)
    (p : FOL.Formula Sg (Fin.cases cfg Γ)) :
    FOL.Formula Sg (Fin.cases cfg (Fin.cases bound Γ)) :=
  rename (liftIndex Fin.succ) (capturedShiftSort cfg bound Γ) p

/-- Weaken by an actual finite sorted capture block, leaving cfg at slot0. -/
def weakenBlock {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S) :
    (xs : List Sg.S) → FOL.Formula Sg (Fin.cases cfg Γ) →
      FOL.Formula Sg (Fin.cases cfg (blockContext Γ xs))
  | [], p => p
  | s :: xs, p => weakenCaptured cfg s (blockContext Γ xs) (weakenBlock cfg Γ xs p)

/-- Outer coordinates embedded below a finite telescope. -/
def outerIndex {k : Nat} : (xs : List Sg.S) → Fin k → Fin (blockSize xs k)
  | [], i => i
  | _ :: xs, i => (outerIndex xs i).succ

theorem outerSort {k : Nat} (Γ : Fin k → Sg.S) (xs : List Sg.S) (i : Fin k) :
    blockContext Γ xs (outerIndex xs i) = Γ i := by
  induction xs with
  | nil => rfl
  | cons s xs ih => exact ih

/-- Empty outer context used by an independently valued operational rule. -/
def emptyContext : Fin 0 → Sg.S := Fin.elim0

/-- Embed the rule-only prefix of a telescope into that same prefix above any
outer captured context. No ordinary Fin-context normalization is claimed. -/
def prefixIndex {k : Nat} : (xs : List Sg.S) →
    Fin (blockSize xs 0) → Fin (blockSize xs k)
  | [], i => i.elim0
  | _ :: xs, i => Fin.cases (0 : Fin (blockSize xs k + 1))
      (fun j => (prefixIndex xs j).succ) i

theorem prefixSort {k : Nat} (Γ : Fin k → Sg.S) (xs : List Sg.S) :
    ∀ i : Fin (blockSize xs 0),
      blockContext Γ xs (prefixIndex xs i) = blockContext emptyContext xs i := by
  induction xs with
  | nil => intro i; exact i.elim0
  | cons s xs ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j

theorem capturedPrefixSort {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S) (xs : List Sg.S) :
    ∀ i : Fin (blockSize xs 0 + 1),
      (Fin.cases cfg (blockContext Γ xs) : Fin (blockSize xs k + 1) → Sg.S)
        (liftIndex (prefixIndex xs) i) =
      (Fin.cases cfg (blockContext emptyContext xs) : Fin (blockSize xs 0 + 1) → Sg.S) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact prefixSort Γ xs j

/-- Semantic assignments to a finite sorted telescope, independently of Γ. -/
def BlockAssignment (M : FOL.Structure Sg) : List Sg.S → Type
  | [] => Unit
  | s :: xs => M.carrier s × BlockAssignment M xs

def joinAssignment (M : FOL.Structure Sg) {k : Nat} {Γ : Fin k → Sg.S}
    (a : (i : Fin k) → M.carrier (Γ i)) :
    (xs : List Sg.S) → BlockAssignment M xs →
      (i : Fin (blockSize xs k)) → M.carrier (blockContext Γ xs i)
  | [], _ => a
  | _ :: xs, b => Fin.cases b.1 (joinAssignment M a xs b.2)

end Silmaril.Logic.FirstOrder.Variables
