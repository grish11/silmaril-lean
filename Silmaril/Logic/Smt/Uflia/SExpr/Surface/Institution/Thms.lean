module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Institution.Defs
public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Determinism.Thms
public import Silmaril.Logic.Smt.Uflia.Script.Thms

/-! Exact transport between independent source satisfaction and the existing
accepted-expression presentation. No existing satisfaction definition changes. -/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface.Direct

open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

/-- Direct whole-sentence satisfaction agrees pointwise with the decoded presentation. -/
theorem concrete_holds_iff (sentence : Packaged.ConcreteSentence) (M : Packaged.GlobalModel) :
    ConcreteHolds sentence M ↔ sentence.Holds M :=
  assertions_direct_iff M sentence.assertions

/-- Direct accepted-script satisfaction agrees pointwise with the existing script room. -/
theorem script_holds_iff (script : Uflia.Script.Accepted) (M : Packaged.GlobalModel) :
    ScriptHolds script M ↔ script.Holds M :=
  (concrete_holds_iff script.sentence M).trans (Uflia.Script.holds_iff script M).symm

/-- Finite-signature interpretations are reducts of coherent global interpretations. -/
noncomputable def interpretationCorridor (E : Environment) : SExpr.room E ⟶ room E where
  sen := id
  mod := Disc.functor (fun M : Packaged.GlobalModel => M.reduct (Packaged.nameMap E))
  sat M a := assertion_direct_iff M a

/-- Model expansion is exact whenever typed operation names distinguish declared operations. -/
theorem interpretationCorridor_modelExpansive (E : Environment) (hE : Packaged.NamesInjective E) :
    (interpretationCorridor E).ModelExpansive :=
  fun M => ⟨Packaged.expand E M, Packaged.expand_reduct E hE M⟩

/-- Every accepted declaration prefix supplies the required model expansion hypothesis. -/
theorem checked_interpretationCorridor_modelExpansive (checked : DeclarationPrefix) :
    (interpretationCorridor checked.environment).ModelExpansive :=
  interpretationCorridor_modelExpansive checked.environment (Packaged.checked_namesInjective checked)

/-- Identity sentence/model maps expose exact direct/decoded transport for whole problems. -/
noncomputable def concreteCorridor : concreteRoom ⟶ Packaged.concreteRoom :=
  ⟨id, Disc.functor id, fun M sentence => (concrete_holds_iff sentence M).symm⟩

/-- Exact transport also exists in the reverse direction. -/
noncomputable def concreteReverseCorridor : Packaged.concreteRoom ⟶ concreteRoom :=
  ⟨id, Disc.functor id, fun M sentence => concrete_holds_iff sentence M⟩

/-- Whole-problem transport loses no coherent global model. -/
theorem concreteCorridor_modelExpansive : concreteCorridor.ModelExpansive :=
  fun M => ⟨M, rfl⟩

/-- Accepted scripts have the same exact identity transport. -/
noncomputable def scriptCorridor : scriptRoom ⟶ Uflia.Script.room :=
  ⟨id, Disc.functor id, fun M script => (script_holds_iff script M).symm⟩

/-- Accepted-script transport also exists in the reverse direction. -/
noncomputable def scriptReverseCorridor : Uflia.Script.room ⟶ scriptRoom :=
  ⟨id, Disc.functor id, fun M script => script_holds_iff script M⟩

/-- Script transport loses no coherent global model. -/
theorem scriptCorridor_modelExpansive : scriptCorridor.ModelExpansive :=
  fun M => ⟨M, rfl⟩

/-- The direct and decoded whole-problem institutions have exact identity transport. -/
noncomputable def concreteComorphism :
    Comorphism concreteInstitution Packaged.concreteInstitution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => id) (fun _ => id)
    (fun _ M sentence => (concrete_holds_iff sentence M).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The direct script institution has exact identity transport to the decoded presentation. -/
noncomputable def scriptComorphism :
    Comorphism scriptInstitution Uflia.Script.institution :=
  Comorphism.ofPlain (𝟭 _) (fun _ => id) (fun _ => id)
    (fun _ M script => (script_holds_iff script M).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Whole accepted problems preserve SAT in both directions. -/
theorem concrete_sat_iff (sentence : Packaged.ConcreteSentence) :
    (∃ M, ConcreteHolds sentence M) ↔ sentence.Sat :=
  exists_congr (concrete_holds_iff sentence)

/-- Whole accepted problems preserve UNSAT in both directions. -/
theorem concrete_unsat_iff (sentence : Packaged.ConcreteSentence) :
    (¬ ∃ M, ConcreteHolds sentence M) ↔ sentence.Unsat :=
  not_congr (concrete_sat_iff sentence)

/-- Accepted scripts preserve SAT in both directions. -/
theorem script_sat_iff (script : Uflia.Script.Accepted) :
    (∃ M, ScriptHolds script M) ↔ script.Sat :=
  exists_congr (script_holds_iff script)

/-- Accepted scripts preserve UNSAT in both directions. -/
theorem script_unsat_iff (script : Uflia.Script.Accepted) :
    (¬ ∃ M, ScriptHolds script M) ↔ script.Unsat :=
  not_congr (script_sat_iff script)

end Silmaril.Logic.Smt.Uflia.SExpr.Surface.Direct
