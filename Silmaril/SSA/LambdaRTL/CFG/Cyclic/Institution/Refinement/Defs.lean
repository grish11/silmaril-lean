module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Thms

/-! # Terminating-result refinement for named cyclic λRTL and λSSA

Use the inclusion order on `Part (K × α)`. A sentence `lhs ≤ rhs` requires
every terminating exit and payload of the left side to occur on the right
at the same initial store. An undefined result is bottom. Infinite execution
and failure to produce a result have no separate observation. The result
also omits the final store and any intermediate effects.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

open CategoryTheory Silmaril.Elgot Silmaril.Logic.Institution
open Silmaril.SSA.LambdaRTL.Institution (Sig)
open Comparison

variable {V K F α : Type} [DecidableEq V] [DecidableEq K]

/-- Every terminating mutable result on the left occurs on the right. -/
abbrev rtlSat (model : PairModel F Part α) (lhs rhs : RTLClass V K F Part α) : Prop :=
  rtlRelSat (· ≤ ·) model lhs rhs

/-- Every terminating lexical result on the left occurs on the right. -/
abbrev ssaSat (model : PairModel F Part α) (lhs rhs : SSAClass V K F Part α) : Prop :=
  ssaRelSat (· ≤ ·) model lhs rhs

/-- Uniform mutable refinement over the discrete pair-lawful Part models. -/
def rtlRefines (lhs rhs : RTLClass V K F Part α) : Prop :=
  ∀ model, rtlSat model lhs rhs

/-- Uniform lexical refinement over the discrete pair-lawful Part models. -/
def ssaRefines (lhs rhs : SSAClass V K F Part α) : Prop :=
  ∀ model, ssaSat model lhs rhs

variable (V K α)

/-- Mutable named cyclic refinement over the primitive signature category. -/
noncomputable def rtl : Inst.{1, 0, 0, 0, 0} := rtlRelation V K Part α (· ≤ ·)

/-- Lexical named cyclic refinement over the primitive signature category. -/
noncomputable def ssa : Inst.{1, 0, 0, 0, 0} := ssaRelation V K Part α (· ≤ ·)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement
