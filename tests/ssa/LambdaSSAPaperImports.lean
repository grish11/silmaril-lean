module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Coproducts.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Defs

open CategoryTheory Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

example : (fromNative (Φ := Φ) (Γ := Γ)).Full :=
  inferInstance

example (X Y : Region.ContinuationContext Φ Γ)
    (f : fromNative.obj X ⟶ fromNative.obj (X.append Y)) :
    fromNative.obj X ⟶ fromNative.obj Y :=
  feedback f

#check appendIsColimit
#check singletonSumIsColimit
#check TypeCategory.sumCofanIsColimit

namespace BoundEntryEta

open Region Region.Paper Region.Paper.TypeCategory.ITree.Reflection
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Elgot.ITree

attribute [local instance] typeModel categoricalInstructions

private def entry : Region Op := .br 0 (.op .poll (.var 0))

private theorem entryTyped : HasType [payload] entry [Output] :=
  .br rfl (.op (.var rfl))

private theorem entryLocalTyped : HasType [payload] entry [Output, Output] :=
  .br rfl (.op (.var rfl))

private def table : Fin 1 → Region Op := fun _ => .br 1 (.var 0)

private theorem tableTyped (i : Fin 1) :
    HasType ((fun _ : Fin 1 => Output) i :: [payload]) (table i)
      (List.ofFn (fun _ : Fin 1 => Output) ++ [Output]) :=
  .br rfl (.var rfl)

example : WithBoundEntryEta.Eqv [payload] (.cfg entry 1 table)
    (entry.bindBranchArguments.lsubst (cfgEntryContinuations table)) [Output] :=
  WithBoundEntryEta.reentry (L := [Output]) (fun _ => Output) entryLocalTyped tableTyped

example : WithBoundEntryEta.Eqv [payload] (.cfg entry 1 table)
    (entry.lsubst (cfgEntryContinuations table)) [Output] :=
  WithBoundEntryEta.literal_reentry (L := [Output]) (fun _ => Output) entryLocalTyped tableTyped

private def discard : Nat → Region Op := fun _ => .br 0 .unit

private theorem discardTyped : LSubst.HasType [payload] [Output] [.unit] discard := by
  intro i A hi
  exact .br rfl .unit

private theorem literalDiscardTyped : HasType [payload] (entry.lsubst discard) [.unit] :=
  entryTyped.lsubst discardTyped

private theorem boundDiscardTyped :
    HasType [payload] (entry.bindBranchArguments.lsubst discard) [.unit] :=
  entryTyped.bindBranchArguments.hasType.lsubst discardTyped

local notation "J" => typeJ (m := TreeModel)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

/-- Unrestricted literal continuation substitution can erase a visible
effect at a fixed exact input and output type. -/
private theorem discard_denotation_ne : Semantics.Categorical.denoteSingletonRegion J M literalDiscardTyped ≠
    Semantics.Categorical.denoteSingletonRegion J M boundDiscardTyped := by
  intro equal
  let a : Ty.denote Atoms payload := ⟨0⟩
  have literal := singletonDenote_tree raw compatible literalDiscardTyped a (fun _ => .unit)
  have bound := singletonDenote_tree raw compatible boundDiscardTyped a (fun _ => .unit)
  rw [equal] at literal
  have observation := congrArg out (bound.symm.trans literal)
  change out (region raw (Semantics.extend (fun _ => .unit) (encodeValue Atoms payload a))
      ((Region.br 0 (.op .poll (.var 0))).bindBranchArguments.lsubst discard)) = _ at observation
  rw [lsubst_bindBranchArguments_br] at observation
  simp only [entry, discard, Region.lsubst, Region.substVars, Tm.subst, region, term,
    Semantics.extend, encodeValue, raw, a, pure_bind, vis_bind, out_vis] at observation
  change _ = out (ret (E := Call) (0, Isotope.Value.unit)) at observation
  rw [out_ret] at observation
  cases Part.some_inj.mp observation

end BoundEntryEta
