module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.Example

/-! # The previous retained separator is identified and generated -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Example

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithComputedCallReturns.Example (Atom Op Payload)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example (explicitArrow)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (Result)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example
  (retained_ne singleBind_typed singleBindArrow)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open TableReadback (Readback outwardEntry readback_outward)

/-- The strict comparison uses the same two retained syntax arrows. -/
theorem projection_identifies_distinct : explicitArrow ≠ singleBindArrow ∧
    (fromWithComputedCalls false).map explicitArrow = (fromWithComputedCalls false).map singleBindArrow :=
  ⟨retained_ne, Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.retained_eq⟩

/-- The original single-bind producer with a nested effectful scrutinee
and the retained input is generated at its written interface. -/
theorem singleBind_generated :
    Generated (Step (τ := Ty Atom) (Φ := Op) false) (ofRegion (Step false) singleBind_typed) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.singleBind_generated

/-- The existing effectful single bind is an outward entry for a written
two-row table. The local rows have heterogeneous payloads and self loops. -/
theorem twoRowReadback :
    let labels : Fin 2 → Ty Atom := fun i => if i.val = 0 then Payload else Silmaril.unit
    let rows : Fin 2 → Region Op := fun i => .br i (.var 0)
    have rowTyping (i : Fin 2) : ValueBranches [labels i, Payload] (rows i) (List.ofFn labels ++ [Result]) :=
      .br ((List.getElem?_append_left (by simp)).trans (by simp only [List.getElem?_ofFn, dite_eq_left i.isLt, Fin.eta]))
        (.var (i := 0) rfl)
    Readback false labels (outwardEntry labels singleBind_typed) rowTyping :=
  readback_outward false _ singleBind_typed _

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Example
