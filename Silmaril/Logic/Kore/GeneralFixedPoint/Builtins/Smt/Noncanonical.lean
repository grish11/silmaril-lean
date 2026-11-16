module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Source

/-! A genuinely different source carrier presentation. All native carriers,
including ordinary sorts, are lifted; every original hook/literal graph law is
transported on all tuples. This is not a canonical-carrier-only model premise. -/
set_option linter.concreteInstances false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical
variable [SortBindings]
variable {scope : Modules.Scope} {literalPrefix : String}
variable {literals : List LiteralBinding} {hooks : List HookBinding}

def native (M : Model scope literalPrefix literals hooks) :
    Matching.GeneralFixedPoint.Model scope.signature where
  carrier s := ULift (M.native.carrier s)
  nonempty s := ⟨⟨Classical.choice (M.native.nonempty s)⟩⟩
  operation op args := {result | result.down ∈ M.native.operation op (fun i => (args i).down)}

def carriers (M : Model scope literalPrefix literals hooks) : Carriers (native M) where
  integer :=
    { toFun := fun x => M.carriers.integer x.down
      invFun := fun x => ⟨M.carriers.integer.symm x⟩
      left_inv := by intro x; cases x; simp
      right_inv := by intro x; simp }
  boolean :=
    { toFun := fun x => M.carriers.boolean x.down
      invFun := fun x => ⟨M.carriers.boolean.symm x⟩
      left_inv := by intro x; cases x; simp
      right_inv := by intro x; simp }

theorem laws (M : Model scope literalPrefix literals hooks) :
    Laws (native M) literalPrefix literals hooks (carriers M) := by
  constructor
  · intro binding member l value op declared
    ext result
    change result.down ∈ M.native.operation op
      (fun i => (Fin.elim0 i : (native M).carrier (Fin.elim0 i)).down) ↔ _
    have emptyArgs :
        (fun i : Fin 0 => (Fin.elim0 i : (native M).carrier (Fin.elim0 i)).down) =
          (fun i => (Fin.elim0 i : M.native.carrier (Fin.elim0 i))) := by
      funext i
      exact Fin.elim0 i
    rw [emptyArgs, M.laws.literal binding member l value op declared]
    cases l <;> cases result <;> simp [carriers, Carriers.literal]
    all_goals exact ⟨fun h => congrArg ULift.up h, fun h => congrArg ULift.down h⟩
  · intro binding member hook op declared args
    ext result
    change result.down ∈ M.native.operation op (fun i => (args i).down) ↔
      result = (carriers M).boolean.symm
        (Operational.Conditional.intEqual
          ((carriers M).integer (args 0)) ((carriers M).integer (args 1)))
    rw [M.laws.intEq binding member hook op declared]
    cases result
    simp [carriers]
    exact ⟨fun h => congrArg ULift.up h, fun h => congrArg ULift.down h⟩
  · intro binding member hook op declared args
    ext result
    change result.down ∈ M.native.operation op (fun i => (args i).down) ↔
      result = (carriers M).boolean.symm (!((carriers M).boolean (args 0)))
    rw [M.laws.boolNot binding member hook op declared]
    cases result
    simp [carriers]
    exact ⟨fun h => congrArg ULift.up h, fun h => congrArg ULift.down h⟩

def model (M : Model scope literalPrefix literals hooks) : Model scope literalPrefix literals hooks :=
  ⟨native M, carriers M, laws M⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical
