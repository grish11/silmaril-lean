module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables

variable {Sg : FOL.Signature}
abbrev StockName (Sg : FOL.Signature) := Sg.S × Nat
abbrev StockAssignment (M : FOL.Structure Sg) := (j : StockName Sg) → M.carrier j.1

/-- Distinct finite numeric tags give distinct sorted stock names. -/
structure Embedding {k : Nat} (Γ : Fin k → Sg.S) where
  tag : Fin k → Nat
  injective : Function.Injective tag

namespace Embedding
variable {k : Nat} {Γ : Fin k → Sg.S}

def name (e : Embedding Γ) (i : Fin k) : StockName Sg := (Γ i, e.tag i)
def bound (e : Embedding Γ) : Nat := Finset.univ.sup e.tag
def fresh (e : Embedding Γ) : Nat := e.bound + 1

theorem tag_lt_fresh (e : Embedding Γ) (i : Fin k) : e.tag i < e.fresh := by
  have h : e.tag i ≤ e.bound := Finset.le_sup (Finset.mem_univ i)
  exact Nat.lt_succ_of_le h

def extend (e : Embedding Γ) (s : Sg.S) : Embedding (Fin.cases s Γ) where
  tag := Fin.cases e.fresh e.tag
  injective := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h; rfl
      · intro h
        have hj := e.tag_lt_fresh j
        change e.fresh = e.tag j at h
        omega
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        have hi := e.tag_lt_fresh i
        change e.tag i = e.fresh at h
        omega
      · intro h
        exact congrArg Fin.succ (e.injective h)

def extendBlock (e : Embedding Γ) : (xs : List Sg.S) → Embedding (blockContext Γ xs)
  | [] => e
  | s :: xs => (e.extendBlock xs).extend s

noncomputable def freshNames (e : Embedding Γ) : List Sg.S → Finset (StockName Sg)
  | [] => ∅
  | s :: xs => by
      classical
      exact insert (s, (e.extendBlock xs).fresh) (e.freshNames xs)

/-- Projection reads only captured stock; configuration is a separate argument. -/
def assignment (e : Embedding Γ) (M : FOL.Structure Sg) (a : StockAssignment M) :
    (i : Fin k) → M.carrier (Γ i) := fun i => a (e.name i)

def blockAssignment (e : Embedding Γ) (M : FOL.Structure Sg) (a : StockAssignment M) :
    (xs : List Sg.S) → BlockAssignment M xs
  | [] => ()
  | s :: xs => (a (s, (e.extendBlock xs).fresh), e.blockAssignment M a xs)

end Embedding

/-- Interpret actual source formulas at an unchanged external configuration. -/
def Pattern.holds {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
    (p : Pattern Sg cfg Γ) (M : FOL.Structure Sg) (e : Embedding Γ)
    (a : StockAssignment M) (w : M.carrier cfg) : Prop :=
  FOL.Formula.Holds M p (consAssignment M cfg Γ w (e.assignment M a))

end Silmaril.Logic.Reachability.Derivation.FirstOrder
