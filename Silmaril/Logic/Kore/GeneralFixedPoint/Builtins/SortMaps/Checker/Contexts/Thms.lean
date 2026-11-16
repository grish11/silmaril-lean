module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Contexts.Defs
public import Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

abbrev ContextData := (n : Nat) × (Fin n → String)

def namesData (names : Names) : ContextData := ⟨names.length, context names⟩

private theorem fin_function_heq {n m : Nat} (h : n = m)
    (f : Fin n → String) (g : Fin m → String)
    (pointwise : ∀ i, f i = g (Fin.cast h i)) : HEq f g := by
  cases h
  apply heq_of_eq
  funext i
  exact pointwise i

theorem namesData_mapNames (sortMap : String → String) (names : Names) :
    namesData (mapNames sortMap names) =
      (⟨names.length, sortMap ∘ context names⟩ : ContextData) := by
  apply Sigma.ext (mapNames_length sortMap names)
  exact (fin_function_heq (mapNames_length sortMap names).symm
    (sortMap ∘ context names) (context (mapNames sortMap names))
    (fun i => (context_mapNames sortMap names i).symm)).symm

/-- The only type equality used by reindexing is the computed equality of
context lengths and pointwise sort names. No checker equation is involved. -/
theorem mappedPatternType {A B : Package} (f : Step A B)
    (sets objects : Names) (s : String) :
    @Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
        (mapNames f.semantic.native.sorts objects) (f.semantic.native.sorts s) =
      Matching.GeneralFixedPoint.Pattern B.base.scope.signature
        (f.semantic.native.sorts ∘ context sets) (f.semantic.native.sorts ∘ context objects)
        (f.semantic.native.sorts s) :=
  congrArg₂ (fun setData objectData : ContextData =>
    Matching.GeneralFixedPoint.Pattern B.base.scope.signature setData.2 objectData.2
      (f.semantic.native.sorts s))
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects)

/-- Native pattern transport written in the actual mapped named contexts. -/
def reindexPattern {A B : Package} (f : Step A B) {sets objects : Names} {s : String}
    (p : @Pattern A.base.scope sets objects s) :
    @Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
      (mapNames f.semantic.native.sorts objects) (f.semantic.native.sorts s) :=
  Eq.mpr (mappedPatternType f sets objects s)
    (Matching.SortMaps.Hom.generalPattern f.semantic.native p)

private theorem eq_mpr_heq {α β : Type} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  cases h
  rfl

theorem reindexPattern_heq {A B : Package} (f : Step A B)
    {sets objects : Names} {s : String} (p : @Pattern A.base.scope sets objects s) :
    HEq (reindexPattern f p) (Matching.SortMaps.Hom.generalPattern f.semantic.native p) :=
  eq_mpr_heq (mappedPatternType f sets objects s) _

theorem familyType_eq {scope : Kore.Modules.Scope} {R R' P P' Γ Γ' : ContextData}
    (hR : R = R') (hP : P = P') (hΓ : Γ = Γ') :
    ((i : Fin R.1) → Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 (R.2 i)) =
      ((i : Fin R'.1) → Matching.GeneralFixedPoint.Pattern scope.signature P'.2 Γ'.2 (R'.2 i)) := by
  cases hR
  cases hP
  cases hΓ
  rfl

/-- Transport a replacement family using computed context equalities. Its
coordinates are retained through the finite index cast. -/
def recontextFamily {scope : Kore.Modules.Scope} {R R' P P' Γ Γ' : ContextData}
    (hR : R = R') (hP : P = P') (hΓ : Γ = Γ')
    (xs : (i : Fin R'.1) → Matching.GeneralFixedPoint.Pattern scope.signature P'.2 Γ'.2 (R'.2 i)) :
    (i : Fin R.1) → Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 (R.2 i) :=
  Eq.mpr (familyType_eq hR hP hΓ) xs

theorem recontextFamily_heq {scope : Kore.Modules.Scope} {R R' P P' Γ Γ' : ContextData}
    (hR : R = R') (hP : P = P') (hΓ : Γ = Γ')
    (xs : (i : Fin R'.1) → Matching.GeneralFixedPoint.Pattern scope.signature P'.2 Γ'.2 (R'.2 i)) :
    HEq (recontextFamily hR hP hΓ xs) xs := eq_mpr_heq _ xs

theorem recontextFamily_at_heq {scope : Kore.Modules.Scope} {R R' P P' Γ Γ' : ContextData}
    (hR : R = R') (hP : P = P') (hΓ : Γ = Γ')
    (xs : (i : Fin R'.1) → Matching.GeneralFixedPoint.Pattern scope.signature P'.2 Γ'.2 (R'.2 i))
    (i : Fin R'.1) :
    HEq (recontextFamily hR hP hΓ xs (Fin.cast (congrArg Sigma.fst hR).symm i)) (xs i) := by
  cases hR
  cases hP
  cases hΓ
  rfl

def reindexFamily {A B : Package} (f : Step A B) {formals sets objects : Names}
    (xs : (i : Fin formals.length) → @Pattern A.base.scope sets objects (context formals i)) :
    (i : Fin (mapNames f.semantic.native.sorts formals).length) →
      @Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
        (mapNames f.semantic.native.sorts objects)
        (context (mapNames f.semantic.native.sorts formals) i) :=
  recontextFamily (namesData_mapNames f.semantic.native.sorts formals)
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects)
    (fun i => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i))

theorem reindexFamily_heq {A B : Package} (f : Step A B) {formals sets objects : Names}
    (xs : (i : Fin formals.length) → @Pattern A.base.scope sets objects (context formals i)) :
    HEq (reindexFamily f xs) (fun i => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i)) :=
  recontextFamily_heq _ _ _ _

theorem reindexFamily_at_heq {A B : Package} (f : Step A B) {formals sets objects : Names}
    (xs : (i : Fin formals.length) → @Pattern A.base.scope sets objects (context formals i))
    (i : Fin formals.length) :
    HEq (reindexFamily f xs (mapIndex f.semantic.native.sorts formals i))
      (Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i)) :=
  recontextFamily_at_heq
    (namesData_mapNames f.semantic.native.sorts formals)
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects)
    (fun j => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs j)) i

/-- A symbol profile packages its finite arity and ordered input sorts. -/
def profileData (inputs : List String) : ContextData := ⟨inputs.length, inputs.get⟩

theorem profileData_map (sortMap : String → String) (inputs : List String) :
    profileData (inputs.map sortMap) =
      (⟨inputs.length, sortMap ∘ inputs.get⟩ : ContextData) := by
  apply Sigma.ext (List.length_map _)
  apply HEq.symm
  apply fin_function_heq (List.length_map _).symm
  intro i
  simp [profileData, List.get_eq_getElem]

/-- Reindex an operation's arguments in its actual mapped finite profile. -/
def reindexArguments {A B : Package} (f : Step A B) {inputs : List String} {sets objects : Names}
    (xs : (i : Fin inputs.length) → @Pattern A.base.scope sets objects (inputs.get i)) :
    (i : Fin (inputs.map f.semantic.native.sorts).length) →
      @Pattern B.base.scope (mapNames f.semantic.native.sorts sets)
        (mapNames f.semantic.native.sorts objects) ((inputs.map f.semantic.native.sorts).get i) :=
  recontextFamily (profileData_map f.semantic.native.sorts inputs)
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects)
    (fun i => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i))

theorem reindexArguments_heq {A B : Package} (f : Step A B) {inputs : List String} {sets objects : Names}
    (xs : (i : Fin inputs.length) → @Pattern A.base.scope sets objects (inputs.get i)) :
    HEq (reindexArguments f xs) (fun i => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i)) :=
  recontextFamily_heq _ _ _ _

def mapProfileIndex (sortMap : String → String) (inputs : List String) (i : Fin inputs.length) :
    Fin (inputs.map sortMap).length := Fin.cast (List.length_map _).symm i

theorem profileSort_map (sortMap : String → String) (inputs : List String) (i : Fin inputs.length) :
    (inputs.map sortMap).get (mapProfileIndex sortMap inputs i) = sortMap (inputs.get i) := by
  simp [mapProfileIndex, List.get_eq_getElem]

theorem reindexArguments_at_heq {A B : Package} (f : Step A B) {inputs : List String} {sets objects : Names}
    (xs : (i : Fin inputs.length) → @Pattern A.base.scope sets objects (inputs.get i)) (i : Fin inputs.length) :
    HEq (reindexArguments f xs (mapProfileIndex f.semantic.native.sorts inputs i))
      (Matching.SortMaps.Hom.generalPattern f.semantic.native (xs i)) :=
  recontextFamily_at_heq
    (profileData_map f.semantic.native.sorts inputs)
    (namesData_mapNames f.semantic.native.sorts sets)
    (namesData_mapNames f.semantic.native.sorts objects)
    (fun j => Matching.SortMaps.Hom.generalPattern f.semantic.native (xs j)) i

theorem name_mapNames (sortMap : String → String) (names : Names) (i : Fin names.length) :
    ((mapNames sortMap names).get (mapIndex sortMap names i)).1 = (names.get i).1 := by
  induction names with
  | nil => exact i.elim0
  | cons head tail ih =>
      rcases head with ⟨name, sort⟩
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change ((mapNames sortMap tail).get (mapIndex sortMap tail i)).1 = (tail.get i).1
          exact ih i

/-- The attached recursion used by the total raw action preserves the ordinary
ordered argument list; attachment only justifies termination. -/
theorem raw_arguments (sortMap nameMap : String → String) (args : List RawPattern) :
    args.attach.map (fun arg => raw sortMap nameMap arg.val) = args.map (raw sortMap nameMap) := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (raw sortMap nameMap)) (List.attach_map_subtype_val args)

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
