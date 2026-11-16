module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Forgetful
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Controls
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.PopulatedControls
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.RawControls
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceThms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceControl
public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Controls
import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Usage.Defs
import Lean

namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Audits

-- Audit actual model and sentence actions, including their concrete controls.
-- Structural/layout checks alone do not inspect these transitive dependencies.
run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in #[
      ``nativeSignatures,
      ``Hom.builtin_images_distinct,
      ``Hom.reduct,
      ``Hom.reduct_native,
      ``Hom.reduct_id,
      ``Hom.reduct_comp,
      ``Hom.reductMap,
      ``Hom.reductFunctor,
      ``Hom.reductFunctor_id,
      ``Hom.reductFunctor_comp,
      ``nativeRoom,
      ``nativeCorridor,
      ``nativeInstitution,
      ``forgetModels,
      ``forget_reduct,
      ``forgetNatural,
      ``forgetful,
      ``Silmaril.Logic.Matching.SortMaps.generalInstitution,
      ``Silmaril.Logic.Matching.SortMaps.fixedSort_generalPattern,
      ``Silmaril.Logic.Matching.SortMaps.fixedSortGeneral,
      ``Silmaril.Logic.Matching.SortMaps.Hom.generalPattern,
      ``Silmaril.Logic.Matching.SortMaps.Hom.generalPattern_id,
      ``Silmaril.Logic.Matching.SortMaps.Hom.generalPattern_comp,
      ``Silmaril.Logic.Matching.SortMaps.Hom.occurs_generalPattern,
      ``Silmaril.Logic.Matching.SortMaps.Hom.admissible_generalPattern,
      ``Silmaril.Logic.Matching.SortMaps.Hom.denote_generalPattern,
      ``Silmaril.Logic.Matching.SortMaps.Hom.generalSentence,
      ``Silmaril.Logic.Matching.SortMaps.Hom.generalSatisfaction,
      ``PopulatedControls.aliasMap,
      ``PopulatedControls.model,
      ``PopulatedControls.all_literal_laws,
      ``PopulatedControls.all_intEq_laws,
      ``PopulatedControls.all_boolNot_laws,
      ``PopulatedControls.literal_zero,
      ``PopulatedControls.equality_on_zero,
      ``PopulatedControls.negation_on_true,
      ``PopulatedControls.cannot_erase_hooks,
      ``PopulatedControls.cannot_erase_literals,
      ``renameRaw,
      ``topReceipt,
      ``mapTop,
      ``mapTop_raw,
      ``mapTop_satisfies,
      ``RawControls.source_accepts,
      ``RawControls.target_accepts,
      ``RawControls.source_admitted,
      ``RawControls.target_admitted,
      ``RawControls.sourceReceipt,
      ``RawControls.targetReceipt,
      ``RawControls.sourceTyped_eq_guard,
      ``RawControls.targetTyped_eq_guard,
      ``RawControls.general_guard,
      ``RawControls.alias_lower_native,
      ``RawControls.alias_source_square,
      ``literal_parse_forward,
      ``Surface.raw,
      ``Surface.Path.action_append,
      ``Surface.toSemantic,
      ``Surface.find_symbols_map,
      ``Surface.Step.find_symbols,
      ``SurfaceControl.step,
      ``SurfaceControl.accepts,
      ``SurfaceControl.receipt,
      ``SurfaceControl.lower_native,
      ``SurfaceControl.source_square,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.cfgBoolean,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.cfg_distinct,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.complement_denotation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.complement_contains_false,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.complement_excludes_true,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.exists_denotation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.nullary_application,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.truth_denotation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.least_admitted,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.greatest_admitted,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.body_denotation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.least_denotation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.greatest_denotation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.fixedpoints_differ,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.denotation_square,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.satisfaction_square,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.exists_source_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.exists_target_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.complement_source_not_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.complement_target_not_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.least_source_not_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.least_target_not_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.greatest_contains_true,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.greatest_excludes_false,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.greatest_source_not_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.greatest_target_not_satisfied,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.model_identity,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls.model_composition,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.cfgStepOperation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.mapOperation,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.no_cfg_labels,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.cfgMap,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.model,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.actual_target_symbol,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.all_cfg_steps,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.cfg_step_true,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.cfg_step_false,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.cfg_profiles_identified,
      ``Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.OperationControls.cfg_outputs_distinct] do
    for ax in (← Lean.collectAxioms declaration) do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {declaration}: {ax}"

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Audits
