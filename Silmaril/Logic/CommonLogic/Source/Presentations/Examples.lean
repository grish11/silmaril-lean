module

public import Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.Thms
public import Silmaril.Logic.CommonLogic.Source.Presentations.Packaged.Thms
public import Silmaril.Logic.CommonLogic.Source.Renaming.Thms
public import Silmaril.Logic.CommonLogic.Core.Examples.Thms
public import Silmaril.Logic.CommonLogic.Source.CLIF.Examples

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.Presentations.Examples
open CategoryTheory
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

abbrev S := Core.Examples.signature

def names : Names S := ⟨[("x",false),("y",true)], [("n",())], [("...s",())]⟩
theorem names_valid : names.Valid := by simp [Names.Valid, names]

def otherNames : Names S := ⟨[("a",false),("b",true)], [("head",())], [("...args",())]⟩
theorem otherNames_valid : otherNames.Valid := by simp [Names.Valid, otherNames]

def vocabulary : Family.Signature := ⟨S, names, names_valid⟩
def otherVocabulary : Family.Signature := ⟨S, otherNames, otherNames_valid⟩

/-- Identifies the distinct discourse symbols while also admitting a fresh marker. -/
def extendedNames : Names S where
  discourse := (names.map Core.Examples.collapse).discourse
  nondiscourse := (names.map Core.Examples.collapse).nondiscourse
  marker := (names.map Core.Examples.collapse).marker ++ ([("...fresh",())] : List (String × S.marker))

theorem extendedNames_valid : extendedNames.Valid := by
  simp [Names.Valid, extendedNames, Names.map, names, Core.Examples.collapse]

def extension : vocabulary ⟶ (⟨S, extendedNames, extendedNames_valid⟩ : Family.Signature) where
  symbols := Core.Examples.collapse
  named :=
    { discourse := (Names.supports_map names Core.Examples.collapse).discourse
      nondiscourse := (Names.supports_map names Core.Examples.collapse).nondiscourse
      marker := fun x d hd => find?_append_of_some x _ _ _
        ((Names.supports_map names Core.Examples.collapse).marker x d hd) }

theorem identifies_distinct_symbols : extension.symbols.discourse false = extension.symbols.discourse true := rfl

theorem fresh_target_declaration : find? "...fresh" extendedNames.marker = some () := rfl

def equalText : CLIF.Text names :=
  (CLIF.readText? names names_valid 64 "(= x y)").get (by rfl)
def unequalText : CLIF.Text otherNames :=
  (CLIF.readText? otherNames otherNames_valid 64 "(not (= a b))").get (by rfl)

theorem extension_preserves_bytes : (Family.mapText extension equalText).source = "(= x y)" := rfl

def equalPackage : Dynamic.Text S := ⟨vocabulary, 𝟙 _, equalText⟩
def unequalPackage : Dynamic.Text S := ⟨otherVocabulary, 𝟙 _, unequalText⟩

theorem equal_package_satisfiable : ∃ M, (Dynamic.room S).Sat M equalPackage := by
  refine ⟨(Core.Model.reduct Core.Examples.collapse).obj Core.Examples.model, ?_⟩
  apply (Dynamic.translate_adequate _ equalPackage).mp
  change (0 : Nat) = 0 ∧ True
  exact ⟨rfl, trivial⟩

theorem unequal_package_satisfiable : ∃ M, (Dynamic.room S).Sat M unequalPackage := by
  refine ⟨Core.Examples.model, ?_⟩
  apply (Dynamic.translate_adequate _ unequalPackage).mp
  change (¬ (0 : Nat) = 1) ∧ True
  exact ⟨by decide, trivial⟩

/-- Independent local models would miss this contradiction. Shared global names
force the two differently spelled local formulae to contradict each other. -/
theorem shared_global_theory_unsatisfiable :
    ¬ ∃ M, ∀ p ∈ ({equalPackage, unequalPackage} : Set (Dynamic.Text S)), (Dynamic.room S).Sat M p := by
  rintro ⟨M, h⟩
  have he := (Dynamic.translate_adequate M equalPackage).mpr (h _ (by simp))
  have hn := (Dynamic.translate_adequate M unequalPackage).mpr (h _ (by simp))
  change (M.discourse false = M.discourse true) ∧ True at he
  change (¬ M.discourse false = M.discourse true) ∧ True at hn
  exact hn.1 he.1

/-- Every full-grammar accepted text from the existing examples packages directly. -/
def generalPackage : Dynamic.Text CLIF.Examples.signature :=
  ⟨⟨_, CLIF.Examples.names, CLIF.Examples.names_valid⟩, 𝟙 _, CLIF.Examples.general⟩

theorem full_grammar_bytes_retained : generalPackage.text.source = CLIF.Examples.generalSource := rfl

/-- Swapping spelling names also renames shadowed binders and occurrences. -/
def shadowed : Formula := .all "x" (.allSeq "...s" (.ex "x"
  (.pred (.reference "x") (.sequence "...s"))))

theorem mixed_shadowing_capture_safe (M : Core.Model S) (r : Equiv.Perm String)
    (ρ : String → Option M.Discourse) (σ : String → Option (List M.Discourse)) :
    (shadowed.rename r).Holds (names.rename r) M (renameEnv r ρ) (renameEnv r σ) ↔
      shadowed.Holds names M ρ σ := Formula.holds_rename names M r ρ σ shadowed

/-- A constant spelling function would capture the formerly unbound occurrence. -/
theorem noninjective_spelling_captures :
    index? "y" ["x"] = none ∧ index? "one" ["one"] = some 0 := by decide

/-- Collapsing x and y to one spelling changes raw truth: an existential
witness different from the free y becomes required to differ from itself. -/
theorem spelling_collision_changes_truth :
    (Formula.ex "x" (.neg (.equal (.individual "x") (.individual "y")))).Holds
      (⟨[],[],[]⟩ : Names S) Core.Examples.model (fun _ => some (0 : Nat)) (fun _ => none) ∧
    ¬ (Formula.ex "one" (.neg (.equal (.individual "one") (.individual "one")))).Holds
      (⟨[],[],[]⟩ : Names S) Core.Examples.model (fun _ => some (0 : Nat)) (fun _ => none) := by
  constructor
  · refine ⟨(1 : Nat), ?_⟩
    change ¬ ∃ x y : Nat, some (1 : Nat) = some x ∧ some (0 : Nat) = some y ∧ x = y
    simp
  · simp [Formula.Holds, Expr.eval, bind, find?]

/-- A spelling permutation preserves the full partition and its semantic aliases. -/
theorem renamed_vocabulary_valid (r : Equiv.Perm String) : (names.rename r).Valid :=
  names.valid_rename r names_valid

end Silmaril.Logic.CommonLogic.Source.Presentations.Examples
