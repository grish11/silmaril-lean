module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Characterization.Defs
public import Mathlib.Order.FixedPoints

/-! Equation-independent algebraic generation on actual public EQ algebras.
Sort and operation families are arbitrary; only the public operation arities
are finite. Empty carriers and signatures without constants are allowed. -/

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Generation

open Silmaril.Logic.Institution.Examples
open Presented.Characterization
variable {A : EQ.Signature}

/-- An independent subset at each actual carrier sort, without encoding sorts
in a uniform carrier or identifying different coordinates. -/
abbrev Family (M : EQ.Algebra A) := (s : A.S) → Set (M.carrier s)

/-- One actual operation application, with every argument in the subset at its
own input sort. All original operation symbols and profiles participate. -/
def groundStep (M : EQ.Algebra A) : Family M →o Family M where
  toFun X s := { x | ∃ (n : Nat) (w : Fin n → A.S) (op : A.Op n w s)
    (args : ∀ i, M.carrier (w i)),
      (∀ i, args i ∈ X (w i)) ∧ M.op op args = x }
  monotone' := by
    rintro X Y h s x ⟨n, w, op, args, hargs, rfl⟩
    exact ⟨n, w, op, args, (fun i => h (w i) (hargs i)), rfl⟩

/-- Product-lattice least fixed point, defined independently of term evaluation. -/
def generated (M : EQ.Algebra A) : Family M := (groundStep M).lfp

/-- Values of existing public ground terms, independently of the fixed point. -/
def evaluationRange (M : EQ.Algebra A) : Family M :=
  fun s => Set.range (evaluate M (s := s))

end Silmaril.Logic.Algebraic.Initial.Generation
