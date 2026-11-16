module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Institution
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.PopulatedControls

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls
open CategoryTheory
open PopulatedControls
open Matching

/-- The actual restricted reduct of the existing populated canonical model. -/
abbrev model := PopulatedControls.model
abbrev noSets : Fin 0 → String := Fin.elim0
abbrev noObjects : Fin 0 → String := Fin.elim0
abbrev cfgSets : Fin 1 → String := fun _ => "CfgA"

/-- The ordinary source sort really has the two-element target Bool carrier. -/
def cfgBoolean : model.native.carrier "CfgA" ≃ Bool := by
  change Canonical.native.carrier "SortBool" ≃ Bool
  exact Canonical.carriers.boolean

def cfgTrue : model.native.carrier "CfgA" := cfgBoolean.symm true
def cfgFalse : model.native.carrier "CfgA" := cfgBoolean.symm false

theorem cfg_distinct : cfgTrue ≠ cfgFalse := by
  intro same
  have impossible : true = false := by
    simpa only [cfgTrue, cfgFalse, Equiv.apply_symm_apply] using congrArg cfgBoolean same
  cases impossible

def emptyObjects : Matching.GeneralFixedPoint.ObjEnv source.scope.signature model.native noObjects :=
  fun i => i.elim0
def emptySets : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native noSets :=
  fun i => i.elim0
def cfgSingleton : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native cfgSets :=
  fun _ => {cfgTrue}

/-- Complement is evaluated on an actual non-singleton, aliased carrier. -/
def complement : Matching.GeneralFixedPoint.Pattern source.scope.signature cfgSets noObjects "CfgA" :=
  .neg (.setvar 0)

theorem complement_denotation :
    complement.denote model.native emptyObjects cfgSingleton = ({cfgTrue} : Set _)ᶜ := rfl

theorem complement_contains_false :
    cfgFalse ∈ complement.denote model.native emptyObjects cfgSingleton := by
  change ¬ cfgFalse = cfgTrue
  intro same
  exact cfg_distinct same.symm

theorem complement_excludes_true :
    cfgTrue ∉ complement.denote model.native emptyObjects cfgSingleton := by
  change ¬ ¬ cfgTrue = cfgTrue
  exact fun absent => absent rfl

/-- The existential branch binds an actual ordinary-sort object. -/
def existsObject : Matching.GeneralFixedPoint.Pattern source.scope.signature noSets noObjects "CfgA" :=
  .ex "CfgA" (.base (.var 0))

theorem exists_denotation
    (v : Matching.GeneralFixedPoint.ObjEnv source.scope.signature model.native noObjects)
    (η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native noSets) :
    existsObject.denote model.native v η = Set.univ := by
  change {x : model.native.carrier "CfgA" | ∃ a, x ∈ ({a} : Set _)} = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨x, rfl⟩

def truthOp : source.scope.signature.operations 0 (fun i => i.elim0) "SortBool" :=
  ⟨Canonical.truth.symbol, by simp [Canonical.scope], rfl, rfl⟩

theorem nullary_application_any {scope : Kore.Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) {s : String}
    (op : scope.signature.operations 0 (fun i => i.elim0) s)
    (args : ∀ i : Fin 0, Set (M.carrier (Fin.elim0 i))) :
    Matching.FixedPoint.application M op args = M.operation op (fun i => i.elim0) := by
  ext result
  constructor
  · rintro ⟨values, _, member⟩
    have empty : values = fun i => i.elim0 := funext (fun i => i.elim0)
    subst values
    exact member
  · intro member
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), member⟩

theorem nullary_application {scope : Kore.Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) {s : String}
    (op : scope.signature.operations 0 (fun i => i.elim0) s) :
    Matching.FixedPoint.application M op (fun i => i.elim0) = M.operation op (fun i => i.elim0) :=
  nullary_application_any M op _

def truthPattern {r k : Nat} {P : Fin r → String} {Γ : Fin k → String} :
    Matching.GeneralFixedPoint.Pattern source.scope.signature P Γ "SortBool" :=
  .app truthOp (fun i => i.elim0)

theorem truth_denotation {r k : Nat} {P : Fin r → String} {Γ : Fin k → String}
    (v : Matching.GeneralFixedPoint.ObjEnv source.scope.signature model.native Γ)
    (η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native P) :
    (truthPattern (P := P) (Γ := Γ)).denote model.native v η =
      {model.carriers.boolean.symm true} := by
  exact (nullary_application_any model.native truthOp _).trans
    (model.laws.literal Canonical.truth (by simp [Canonical.literals])
      (.boolean true) rfl truthOp rfl)

/-- Both fixed points use the actual declared true literal. F(X)={true}∩X. -/
def fixedBody : Matching.GeneralFixedPoint.Pattern source.scope.signature
    (Fin.cases "SortBool" noSets) noObjects "SortBool" :=
  .conj truthPattern (.setvar 0)

def least : Matching.GeneralFixedPoint.Pattern source.scope.signature noSets noObjects "SortBool" :=
  .mu fixedBody
def greatest : Matching.GeneralFixedPoint.Pattern source.scope.signature noSets noObjects "SortBool" :=
  .nu fixedBody

theorem least_admitted : least.admissible = true := rfl
theorem greatest_admitted : greatest.admissible = true := rfl

theorem body_denotation
    (v : Matching.GeneralFixedPoint.ObjEnv source.scope.signature model.native noObjects)
    (η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native noSets)
    (X : Set (model.native.carrier "SortBool")) :
    fixedBody.denote model.native v ((Fin.cases X η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native
      (Fin.cases "SortBool" noSets))) =
      {model.carriers.boolean.symm true} ∩ X := by
  change (truthPattern.denote model.native v ((Fin.cases X η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native
      (Fin.cases "SortBool" noSets)))) ∩ X = _
  rw [truth_denotation]

theorem least_denotation
    (v : Matching.GeneralFixedPoint.ObjEnv source.scope.signature model.native noObjects)
    (η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native noSets) :
    least.denote model.native v η = ∅ := by
  change sInf {X | fixedBody.denote model.native v ((Fin.cases X η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native
      (Fin.cases "SortBool" noSets))) ⊆ X} = ∅
  simp only [body_denotation]
  apply le_antisymm
  · exact sInf_le (show ({model.carriers.boolean.symm true} ∩ (∅ : Set _)) ⊆ ∅ from
      fun _ member => member.2)
  · exact Set.empty_subset _

theorem greatest_denotation
    (v : Matching.GeneralFixedPoint.ObjEnv source.scope.signature model.native noObjects)
    (η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native noSets) :
    greatest.denote model.native v η = {model.carriers.boolean.symm true} := by
  change sSup {X | X ⊆ fixedBody.denote model.native v ((Fin.cases X η : Matching.GeneralFixedPoint.SetEnv source.scope.signature model.native
      (Fin.cases "SortBool" noSets)))} = _
  simp only [body_denotation]
  apply le_antisymm
  · apply sSup_le
    intro X post x member
    exact (post member).1
  · apply le_sSup
    intro x member
    exact ⟨member, member⟩

theorem fixedpoints_differ :
    least.denote model.native emptyObjects emptySets ≠
      greatest.denote model.native emptyObjects emptySets := by
  rw [least_denotation, greatest_denotation]
  intro same
  have impossible : model.carriers.boolean.symm true ∈ (∅ : Set _) :=
    same.symm ▸ (show model.carriers.boolean.symm true ∈ {model.carriers.boolean.symm true} from rfl)
  exact impossible

def complementSentence : Matching.GeneralFixedPoint.Sentence source.scope.signature :=
  ⟨1, 0, cfgSets, noObjects, "CfgA", complement, rfl⟩
def existsSentence : Matching.GeneralFixedPoint.Sentence source.scope.signature :=
  ⟨0, 0, noSets, noObjects, "CfgA", existsObject, rfl⟩
def leastSentence : Matching.GeneralFixedPoint.Sentence source.scope.signature :=
  ⟨0, 0, noSets, noObjects, "SortBool", least, least_admitted⟩
def greatestSentence : Matching.GeneralFixedPoint.Sentence source.scope.signature :=
  ⟨0, 0, noSets, noObjects, "SortBool", greatest, greatest_admitted⟩

/-- Actual denotations, including free sets, are transported to Canonical.model. -/
theorem denotation_square {r k : Nat} {P : Fin r → String} {Γ : Fin k → String} {s : String}
    (p : Matching.GeneralFixedPoint.Pattern source.scope.signature P Γ s)
    (v : Matching.GeneralFixedPoint.ObjEnv target.scope.signature Canonical.model.native (aliasMap.native.sorts ∘ Γ))
    (η : Matching.GeneralFixedPoint.SetEnv target.scope.signature Canonical.model.native (aliasMap.native.sorts ∘ P)) :
    (Matching.SortMaps.Hom.generalPattern aliasMap.native p).denote Canonical.model.native v η =
      p.denote model.native v η := by
  exact Matching.SortMaps.Hom.denote_generalPattern aliasMap.native Canonical.model.native p v η

/-- This square uses the full native institution on two actual restricted models. -/
theorem satisfaction_square (p : Matching.GeneralFixedPoint.Sentence source.scope.signature) :
    Matching.GeneralFixedPoint.Sentence.Satisfies Canonical.model.native
      (Matching.SortMaps.Hom.generalSentence aliasMap.native p) ↔
      Matching.GeneralFixedPoint.Sentence.Satisfies model.native p :=
  (nativeCorridor aliasMap).sat Canonical.model p

theorem exists_source_satisfied :
    Matching.GeneralFixedPoint.Sentence.Satisfies model.native existsSentence := by
  intro v η x
  change x ∈ existsObject.denote model.native v η
  exact (exists_denotation v η).symm ▸ Set.mem_univ x

theorem exists_target_satisfied :
    Matching.GeneralFixedPoint.Sentence.Satisfies Canonical.model.native
      (Matching.SortMaps.Hom.generalSentence aliasMap.native existsSentence) :=
  (satisfaction_square existsSentence).mpr exists_source_satisfied

theorem complement_source_not_satisfied :
    ¬ Matching.GeneralFixedPoint.Sentence.Satisfies model.native complementSentence := by
  intro valid
  exact complement_excludes_true (valid emptyObjects cfgSingleton cfgTrue)

theorem complement_target_not_satisfied :
    ¬ Matching.GeneralFixedPoint.Sentence.Satisfies Canonical.model.native
      (Matching.SortMaps.Hom.generalSentence aliasMap.native complementSentence) := by
  intro valid
  exact complement_source_not_satisfied ((satisfaction_square complementSentence).mp valid)

theorem least_source_not_satisfied :
    ¬ Matching.GeneralFixedPoint.Sentence.Satisfies model.native leastSentence := by
  intro valid
  have member := valid emptyObjects emptySets (model.carriers.boolean.symm true)
  change model.carriers.boolean.symm true ∈ least.denote model.native emptyObjects emptySets at member
  rw [least_denotation] at member
  exact member

theorem least_target_not_satisfied :
    ¬ Matching.GeneralFixedPoint.Sentence.Satisfies Canonical.model.native
      (Matching.SortMaps.Hom.generalSentence aliasMap.native leastSentence) := by
  intro valid
  exact least_source_not_satisfied ((satisfaction_square leastSentence).mp valid)

theorem greatest_contains_true :
    model.carriers.boolean.symm true ∈ greatest.denote model.native emptyObjects emptySets := by
  rw [greatest_denotation]
  rfl

theorem greatest_excludes_false :
    model.carriers.boolean.symm false ∉ greatest.denote model.native emptyObjects emptySets := by
  rw [greatest_denotation]
  intro same
  have impossible : false = true := by
    simpa only [Set.mem_singleton_iff, Equiv.apply_symm_apply] using
      congrArg model.carriers.boolean same
  cases impossible

theorem greatest_source_not_satisfied :
    ¬ Matching.GeneralFixedPoint.Sentence.Satisfies model.native greatestSentence := by
  intro valid
  exact greatest_excludes_false (valid emptyObjects emptySets (model.carriers.boolean.symm false))

theorem greatest_target_not_satisfied :
    ¬ Matching.GeneralFixedPoint.Sentence.Satisfies Canonical.model.native
      (Matching.SortMaps.Hom.generalSentence aliasMap.native greatestSentence) := by
  intro valid
  exact greatest_source_not_satisfied ((satisfaction_square greatestSentence).mp valid)

theorem model_identity : Hom.reduct (𝟙 source) model = model :=
  Hom.reduct_id source model

theorem model_composition :
    Hom.reduct (aliasMap ≫ 𝟙 target) Canonical.model =
      Hom.reduct aliasMap (Hom.reduct (𝟙 target) Canonical.model) :=
  Hom.reduct_comp aliasMap (𝟙 target) Canonical.model

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.NativeControls
