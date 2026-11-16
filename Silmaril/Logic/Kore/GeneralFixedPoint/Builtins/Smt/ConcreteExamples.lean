module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Canonical

/-! A genuine finite source/model instance: reuse Canonical's two declared
hooks, six actual operations, Int/Bool carriers and complete all-tuple laws.
Bind X to two integer values, then repeat the same raw variable in INT.eq. -/
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples

def finiteObjects (M : Model Canonical.scope Canonical.literalPrefix
    Canonical.literals Canonical.hooks) : Semantics.Values M.native :=
  [⟨"X", "SortInt", {x | M.carriers.integer x = 0 ∨ M.carriers.integer x = 1}⟩]

private theorem finiteObjects_legal (M : Model Canonical.scope Canonical.literalPrefix
    Canonical.literals Canonical.hooks) :
    (Semantics.lookupValue M.native (finiteObjects M) "X" "SortInt").isSome = true := by
  rfl

private theorem finiteObjects_member (M : Model Canonical.scope Canonical.literalPrefix
    Canonical.literals Canonical.hooks) (n : Int) (member : n = 0 ∨ n = 1) :
    M.carriers.integer.symm n ∈
      (Semantics.lookupValue M.native (finiteObjects M) "X" "SortInt").getD ∅ := by
  change M.carriers.integer (M.carriers.integer.symm n) = 0 ∨
    M.carriers.integer (M.carriers.integer.symm n) = 1
  simpa only [Equiv.apply_symm_apply] using member

/-- Closed actual original raw syntax, without an assumed checker equation. -/
def raw : RawPattern := .app "eqInt" [.evar "X" "SortInt", .evar "X" "SortInt"]

theorem checked : check Canonical.scope Canonical.hooks 2 .boolean raw =
    some (.intEq (.variable .integer "X") (.variable .integer "X")) := by
  rfl

def objects : Semantics.Values Canonical.native := finiteObjects Canonical.model

theorem objects_legal :
    (Semantics.lookupValue Canonical.native objects "X" "SortInt").isSome = true :=
  finiteObjects_legal Canonical.model

theorem actual_model_exists : Nonempty (Model Canonical.scope Canonical.literalPrefix
    Canonical.literals Canonical.hooks) := ⟨Canonical.model⟩

theorem objects_have_distinct_members :
    ∃ x y : Canonical.native.carrier "SortInt",
      x ∈ (Semantics.lookupValue Canonical.native objects "X" "SortInt").getD ∅ ∧
      y ∈ (Semantics.lookupValue Canonical.native objects "X" "SortInt").getD ∅ ∧ x ≠ y := by
  refine ⟨Canonical.carriers.integer.symm 0, Canonical.carriers.integer.symm 1,
    finiteObjects_member Canonical.model 0 (Or.inl rfl),
    finiteObjects_member Canonical.model 1 (Or.inr rfl), ?_⟩
  intro equal
  have impossible : (0 : Int) = 1 := by
    simpa only [Equiv.apply_symm_apply] using congrArg Canonical.carriers.integer equal
  exact (by decide : (0 : Int) ≠ 1) impossible

/-- Concrete source membership is false even though both arguments are X. -/
theorem false_member : Canonical.carriers.boolean.symm false ∈
    (Semantics.denote Canonical.scope [] Canonical.native Canonical.carriers 2 [] objects
      "SortBool" raw).getD ∅ := by
  exact RawExamples.repeated_variable_false Canonical.model objects 2 "eqInt" "X"
    checked objects_legal (Canonical.carriers.integer.symm 0) (Canonical.carriers.integer.symm 1)
    (finiteObjects_member Canonical.model 0 (Or.inl rfl))
    (finiteObjects_member Canonical.model 1 (Or.inr rfl))
    (by simpa only [Canonical.model, Equiv.apply_symm_apply] using
      (show (0 : Int) ≠ 1 by decide))

/-- A closed, actually inhabited source model whose native carriers are ULift. -/
def liftedModel : Model Canonical.scope Canonical.literalPrefix Canonical.literals
    Canonical.hooks := Noncanonical.model Canonical.model

def liftedObjects : Semantics.Values liftedModel.native := finiteObjects liftedModel

theorem lifted_false_member : liftedModel.carriers.boolean.symm false ∈
    (Semantics.denote Canonical.scope [] liftedModel.native liftedModel.carriers 2 [] liftedObjects
      "SortBool" raw).getD ∅ := by
  exact RawExamples.repeated_variable_false liftedModel liftedObjects 2 "eqInt" "X"
    checked (finiteObjects_legal liftedModel)
    (liftedModel.carriers.integer.symm 0) (liftedModel.carriers.integer.symm 1)
    (finiteObjects_member liftedModel 0 (Or.inl rfl))
    (finiteObjects_member liftedModel 1 (Or.inr rfl))
    (by simpa only [Equiv.apply_symm_apply] using (show (0 : Int) ≠ 1 by decide))

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.ConcreteExamples
