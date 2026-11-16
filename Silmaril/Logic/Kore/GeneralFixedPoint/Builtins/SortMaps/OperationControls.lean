module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Institution
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.PopulatedControls

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls
open CategoryTheory
open PopulatedControls

/-- An actual ordinary source declaration whose two profile names are identified. -/
def cfgStep : Kore.Modules.NamedSymbol :=
  ⟨⟨"CONTROL", 2⟩, ⟨"cfgStep", ["CfgA"], "CfgB"⟩⟩

abbrev sourceWithCfg : Signature :=
  { source with scope := { source.scope with symbols := cfgStep :: source.scope.symbols } }

/-- The argument-list equality is transported directly; no default operation is used. -/
def cfgStepOperation {n : Nat} {inputs : Fin n → String} {output : String}
    (op : sourceWithCfg.scope.signature.operations n inputs output) (identity : op.val = cfgStep) :
    target.scope.signature.operations n (renameSort ∘ inputs) (renameSort output) where
  val := Canonical.negation
  property := by
    refine ⟨by simp [Canonical.scope], ?_, ?_⟩
    · have profile : ["CfgA"] = List.ofFn inputs := by
        simpa only [identity, cfgStep] using op.property.2.1
      calc
        Canonical.negation.declaration.arguments = (["CfgA"] : List String).map renameSort := rfl
        _ = (List.ofFn inputs).map renameSort := congrArg (List.map renameSort) profile
        _ = List.ofFn (renameSort ∘ inputs) := by simp [List.map_ofFn, Function.comp_def]
    · have result : "CfgB" = output := by
        simpa only [identity, cfgStep] using op.property.2.2
      exact congrArg renameSort result

def mapOperation {n : Nat} {inputs : Fin n → String} {output : String}
    (op : sourceWithCfg.scope.signature.operations n inputs output) :
    target.scope.signature.operations n (renameSort ∘ inputs) (renameSort output) :=
  if fresh : op.val = cfgStep then cfgStepOperation op fresh
  else aliasMap.native.operations
    ⟨op.val, (List.mem_cons.mp op.property.1).resolve_left fresh, op.property.2⟩

theorem no_cfg_labels : sourceWithCfg.labels cfgStep = ∅ := by
  ext tag
  cases tag <;>
    simp [Signature.labels, Canonical.literals, Canonical.hooks,
      Canonical.zero, Canonical.negative, Canonical.truth, Canonical.falsity,
      Canonical.equality, Canonical.negation, cfgStep]

def cfgMap : sourceWithCfg ⟶ target where
  native := ⟨renameSort, mapOperation⟩
  integer := by decide
  boolean := by decide
  labels := by
    intro n inputs output op tag marked
    by_cases fresh : op.val = cfgStep
    · have impossible : tag ∈ (∅ : Set Label) := by
        simpa only [fresh, no_cfg_labels] using marked
      exact False.elim impossible
    · change tag ∈ target.labels (mapOperation op).val
      have mapped : mapOperation op = aliasMap.native.operations
          ⟨op.val, (List.mem_cons.mp op.property.1).resolve_left fresh, op.property.2⟩ :=
        dite_eq_right fresh
      rw [mapped]
      exact aliasMap.labels
        ⟨op.val, (List.mem_cons.mp op.property.1).resolve_left fresh, op.property.2⟩ marked

def cfgOp : sourceWithCfg.scope.signature.operations 1 (fun _ => "CfgA") "CfgB" :=
  ⟨cfgStep, List.mem_cons_self, rfl, rfl⟩

theorem actual_target_symbol : (cfgMap.native.operations cfgOp).val = Canonical.negation := by
  change (mapOperation cfgOp).val = Canonical.negation
  have mapped : mapOperation cfgOp = cfgStepOperation cfgOp rfl := dite_eq_left rfl
  exact congrArg Subtype.val mapped

def model : @Model sourceWithCfg.bindings sourceWithCfg.scope sourceWithCfg.literalPrefix
    sourceWithCfg.literals sourceWithCfg.hooks :=
  cfgMap.reduct Canonical.model

/-- A real ordinary-sort operation computes through the retained target hook. -/
theorem all_cfg_steps (args : ∀ _i : Fin 1, model.native.carrier "CfgA") :
    model.native.operation cfgOp args =
      {model.carriers.boolean.symm (!(model.carriers.boolean (args 0)))} := by
  change Canonical.native.operation (cfgMap.native.operations cfgOp) args =
    {Canonical.carriers.boolean.symm (!(Canonical.carriers.boolean (args 0)))}
  exact Canonical.laws.boolNot ⟨Canonical.negation, .boolNot⟩
    (by simp [Canonical.hooks]) rfl (cfgMap.native.operations cfgOp) actual_target_symbol args

theorem cfg_step_true :
    model.native.operation cfgOp (fun _ => model.carriers.boolean.symm true) =
      {model.carriers.boolean.symm false} := by
  simpa only [Equiv.apply_symm_apply, Bool.not_true] using
    all_cfg_steps (fun _ => model.carriers.boolean.symm true)

theorem cfg_step_false :
    model.native.operation cfgOp (fun _ => model.carriers.boolean.symm false) =
      {model.carriers.boolean.symm true} := by
  simpa only [Equiv.apply_symm_apply, Bool.not_false] using
    all_cfg_steps (fun _ => model.carriers.boolean.symm false)

theorem cfg_profiles_identified :
    cfgMap.native.sorts "CfgA" = cfgMap.native.sorts "CfgB" := by decide

theorem cfg_outputs_distinct :
    model.carriers.boolean.symm false ≠ model.carriers.boolean.symm true := by
  intro same
  have impossible : false = true := by
    simpa only [Equiv.apply_symm_apply] using congrArg model.carriers.boolean same
  cases impossible

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls
