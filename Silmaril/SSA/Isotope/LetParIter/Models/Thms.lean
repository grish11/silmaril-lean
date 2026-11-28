module

public import Silmaril.SSA.Isotope.LetParIter.Models.Defs
public import Silmaril.SSA.Isotope.LetParIter.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Models

/-! # Concrete observations and soundness for the two LetParIter dialects -/

public section

namespace Silmaril.Isotope.LetParIter.Models

open Parallel (Derivation)
open LetIter.ProofRelevant.Semantics
open scoped Silmaril.Elgot.Nondet

variable {Γ : Ctx Empty Code} {n : Nat} {β : BoundCtx Code n} {A : Code}

namespace ReadOnly

/-- Every generated typed equation is sound at every environment. -/
theorem sound {a b : Tm Empty Instr n}
    {da : Derivation Instr Γ β a A} {db : Derivation Instr Γ β b A}
    (h : LetParIter.Equiv (⊥ : Effect) Γ da db) (γ : CtxDen Γ) (values : BoundDen β) :
    denote da γ values = denote db γ values :=
  LetParIter.sound pairing h γ values

/-- Each coordinate of the result depends only on its own environment slot.
The pair returns exactly when both slots supply a value. -/
theorem readPair_mem (r : Env) (a b : Nat) :
    (a, b) ∈ (denote readPair PUnit.unit PUnit.unit).run r ↔ a ∈ r.1 ∧ b ∈ r.2 :=
  Proofs.Models.ReadOnly.readPair_mem r a b

/-- For every available counter the loop reaches zero and returns the right
slot's value, if available. An absent counter yields no result. -/
theorem countAndRead_run (r : Env) :
    (denote countAndRead PUnit.unit PUnit.unit).run r = (r.1 >>= fun _ => r.2) :=
  Proofs.Models.ReadOnly.countAndRead_run r

end ReadOnly

namespace Choice

/-- Every generated typed equation preserves the entire set of may-outcomes. -/
theorem sound {a b : Tm Empty Instr n}
    {da : Derivation Instr Γ β a A} {db : Derivation Instr Γ β b A}
    (h : LetParIter.Equiv (⊥ : Bool) Γ da db) (γ : CtxDen Γ) (values : BoundDen β) :
    denote da γ values = denote db γ values :=
  LetParIter.sound Elgot.Nondet.parallelPairing h γ values

/-- Each left alternative can be combined independently with each right one. -/
theorem choosePair_mem (a b c d x y : Nat) :
    (x, y) ∈ₘ denote (choosePair a b c d) PUnit.unit PUnit.unit ↔
      (x = a ∨ x = b) ∧ (y = c ∨ y = d) :=
  Proofs.Models.Choice.choosePair_mem a b c d x y

/-- The zero state can take the back edge indefinitely. -/
theorem step_zero_backEdge : Sum.inr 0 ∈ₘ step 0 := Or.inr rfl

/-- Returning immediately can yield 20, and taking a back edge can yield 10. -/
theorem chooseLoop_outcomes :
    denote chooseLoop PUnit.unit PUnit.unit = ({10, 20} : Set Nat) :=
  Proofs.Models.Choice.chooseLoop_outcomes

end Choice

end Silmaril.Isotope.LetParIter.Models
