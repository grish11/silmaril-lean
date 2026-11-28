module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic

open Diamond (Signature ValueSort)

universe u v w

/-- A class representative is a vertex having the requested key. -/
theorem classesOf_preserves_key {Key : Type w} [DecidableEq Key] {n : Nat}
    (key : Fin n → Key) (i : Fin n) : key (classesOf key i) = key i :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.classesOf_preserves_key key i

/-- Class labels agree exactly on equal keys. -/
theorem classesOf_eq_iff {Key : Type w} [DecidableEq Key] {n : Nat}
    (key : Fin n → Key) (i j : Fin n) : classesOf key i = classesOf key j ↔ key i = key j :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.classesOf_eq_iff key i j

variable {Data : Type u} {Op : Signature.{u,v} Data} {n : Nat}
variable {inputs : List (ValueSort Data)} {sorts : Fin n → ValueSort Data}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- The initial producer classes are exactly the typed profile classes.
Arguments are distinguished separately by their typed positions. -/
theorem seed_eq_iff (g : Graph Op inputs sorts) (i j : Fin n) :
    seed g i = seed g j ↔ (g.node i).profile = (g.node j).profile :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.seed_eq g i j

/-- A round splits old classes precisely by profile and the ordered classes
of all operand occurrences. In particular, it cannot merge old classes. -/
theorem refine_eq_iff (g : Graph Op inputs sorts) (p : Partition n) (i j : Fin n) :
    refine g p i = refine g p j ↔
      p i = p j ∧ (g.node i).profile = (g.node j).profile ∧
        g.operandClasses p i = g.operandClasses p j :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.refine_eq g p i j

/-- Acceptance certifies structural agreement for all pairs in a class. -/
theorem checkStable_eq_true_iff (g : Graph Op inputs sorts) (p : Partition n) :
    checkStable g p = true ↔ Stable g p :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.checkStable_correct g p

/-- Stability is a fixed point of refinement viewed as a partition,
independently of the numeric labels. -/
theorem stable_iff_refine_eq (g : Graph Op inputs sorts) (p : Partition n) :
    Stable g p ↔ ∀ i j, refine g p i = refine g p j ↔ p i = p j :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.stable_iff_no_split g p

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic
