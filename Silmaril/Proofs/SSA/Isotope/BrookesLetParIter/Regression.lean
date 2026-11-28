module

public import Silmaril.SSA.Isotope.BrookesLetParIter.Thms
import Silmaril.Logic.BrookesSC.Concrete.Thms

public section

namespace Silmaril.Isotope.BrookesLetParIter.Regression

open Silmaril.Isotope.BrookesLetParIter
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Logic.BrookesSC
open Silmaril.Semantics.Brookes

abbrev Γ : Ctx Unit SCType := .nil
abbrev β : BoundCtx SCType 1 := .snoc .nil word

/-- The loop makes one atomic load and returns its result. -/
def readOnce : LetParIter.Tm Unit Instr 1 :=
  .iter rfl .unit (.inl (Parallel.Tier.iterHasCase rfl) (.op (.load true) .unit))

def readOnceDerivation : Parallel.Derivation Instr Γ β readOnce word :=
  .iter .unit (.inl (.op .unit))

/-- A write races with a load performed in a returning loop. -/
def program : LetParIter.Tm Unit Instr 1 :=
  .par (.op (.store false) (.bv 0)) readOnce

def writeDerivation :
    Parallel.Derivation Instr Γ β (.op (.store false) (.bv 0) : LetParIter.Tm Unit Instr 1) unit :=
  .op .bv

def programDerivation : Parallel.Derivation Instr Γ β program (product unit word) :=
  .par writeDerivation readOnceDerivation

set_option backward.isDefEq.respectTransparency false in
theorem denote_readOnce (input : Nat) :
    LetParIter.denote (ε := Bool) pairing readOnceDerivation PUnit.unit (PUnit.unit, input) =
      eval (.load true) () := by
  change Parallel.evalIter (A := (unit : SCType)) (B := word)
    (pure () : M Unit) (fun _ =>
      ((pure () : M Unit) >>= eval (.load true)) >>= fun y => pure (.inl y : Nat ⊕ Unit)) = _
  rw [Parallel.evalIter_unfold]
  simp only [pure_bind, bind_assoc]
  exact Behavior.bind_ret _

set_option backward.isDefEq.respectTransparency false in
theorem denote_program (input : Nat) :
    LetParIter.denote (ε := Bool) pairing programDerivation PUnit.unit (PUnit.unit, input) =
      (eval (.store false) input).parallel (eval (.load true) ()) := by
  change Parallel.evalPar (A := (unit : SCType)) (B := word) pairing
    ((pure input : M Nat) >>= eval (.store false))
    (LetParIter.denote (ε := Bool) pairing readOnceDerivation PUnit.unit (PUnit.unit, input)) = _
  rw [denote_readOnce, pure_bind]
  exact id_map _

/-- A closed observation witnesses the load seeing the old word before the write. -/
theorem program_completes :
    (LetParIter.denote (ε := Bool) pairing programDerivation PUnit.unit (PUnit.unit, (1 : Nat))).completes
      (state 0 none) (state 1 none) ((), (0 : Nat)) := by
  rw [denote_program]
  let before := state 0 none
  let after := state 1 none
  apply Behavior.parallel_completes_iff.mpr
  exact ⟨[(before, after)], [(before, before)], [(before, before), (before, after)],
    (Concrete.primitive_completes_iff (W := world) (.store false .scAtomic () (1 : Nat)) _ _ _).mpr rfl,
    (Concrete.primitive_completes_iff (W := world) (.load true .scAtomic ()) _ _ _).mpr rfl,
    .right _ (.left _ .nil), .cons (.cons (.nil _))⟩

theorem swap_program (input : Nat) :
    LetParIter.denote (ε := Bool) pairing (LetParIter.Typing.swap programDerivation)
        PUnit.unit (PUnit.unit, input) =
      LetParIter.denote (ε := Bool) pairing (.par readOnceDerivation writeDerivation)
        PUnit.unit (PUnit.unit, input) :=
  sound (.swap writeDerivation readOnceDerivation) PUnit.unit (PUnit.unit, input)

end Silmaril.Isotope.BrookesLetParIter.Regression
