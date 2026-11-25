module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Subdistribution.Defs
public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
import Silmaril.Proofs.Semantics.Calco2019.Examples.Subdistribution

/-! # Complete Elgot iteration for countable subdistributions -/

public section

open scoped ENNReal

universe u

namespace Silmaril.Calco2019.Examples.Probability.Subdist

variable {X Y : Type u}

instance : LawfulMonad Subdist.{u} := Proofs.lawful

/-- Bounded total mass enforces the paper's countable-support restriction. -/
theorem countable_support (p : Subdist X) : (Function.support p.weight).Countable :=
  Proofs.countable_support p

/-- Pointwise least solutions for all subdistribution bodies. -/
noncomputable def solve (f : X → Subdist (Y ⊕ X)) : X → Subdist Y :=
  Proofs.solve f

theorem solve_weight (f : X → Subdist (Y ⊕ X)) (x : X) (y : Y) :
    solve f x y = ⨆ n, unfoldFor f n x y :=
  Proofs.solve_weight f x y

theorem fix (f : X → Subdist (Y ⊕ X)) : unfoldLoop f (solve f) = solve f :=
  Proofs.fix f

theorem least_solution (f : X → Subdist (Y ⊕ X)) {g : X → Subdist Y}
    (hg : unfoldLoop f g ≤ g) : solve f ≤ g :=
  Proofs.least_solution f hg

noncomputable instance : Elgot.Iterate Subdist.{u} := ⟨solve⟩

instance : Elgot.LawfulElgotMonad Subdist.{u} := Proofs.lawfulElgot

/-- The subdistribution monad of Example 20(3) has total CALCO iteration. -/
noncomputable def elgot : GuardedElgotMonad typeCoproducts.{u} :=
  ofLawfulMonad Subdist

theorem isElgot : (elgot.{u}).IsElgot :=
  ofLawfulMonad_isElgot Subdist

/-- On full probability bodies the total operator gives the same unnormalized weights
as the computation used in the counterexample. -/
theorem pmf_agreement (f : X → PMF (Y ⊕ X)) (x : X) (y : Y) :
    solve (fun x => ofPMF (f x)) x y = Probability.least f x y :=
  Proofs.pmf_agreement f x y

end Silmaril.Calco2019.Examples.Probability.Subdist
