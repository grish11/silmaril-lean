module

public import Silmaril.Logic.Smt.Uflia.SExpr.Thms

/-!
# QF-UFLIA problems with declarations inside sentences

One global model interprets every name at every typed operation profile, with
the standard Bool/Int carriers and a single coherent family of user carriers.
A sentence contains an environment and assertions over its finite symbol set.
This is distinct from the fixed-symbol institution. Names at different profiles
may have different interpretations. Repeated names at the same profile collapse
under packaging; expansion results therefore require the actual name map to be
injective at each profile, rather than assuming satisfiability as a premise.
`Thms` derives this injectivity from successful declaration-prefix decoding.
The fixed-problem institutions use discrete raw/checked environment signatures;
their equality transports are not a claim of concrete symbol-renaming maps.
No full SMT-LIB script parser is claimed.
Concrete whole-problem sentences retain a checked declaration prefix and the
accepted S-expression assertions. Their meaning is checked decoding in the
global model's reduct, not an independently formalized SMT-LIB standard.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.Packaged

open CategoryTheory Silmaril.Inst
open Silmaril.Logic.Institution (Room Corridor)
open SExpr

/-- The universal typed name signature. One model interprets it globally,
rather than choosing unrelated models separately for each environment. -/
def nameSignature : Signature String := ⟨fun _ _ _ => String⟩

abbrev GlobalModel := Model nameSignature

/-- Forget finite declaration indices while preserving each operation profile. -/
def nameMap (E : Environment) : E.signature ⟶ nameSignature where
  operations symbol := by
    cases symbol with
    | declared i => exact (E.declarations.get i).name

/-- Precisely the structural hypothesis needed to extend every local model. -/
def NamesInjective (E : Environment) : Prop :=
  ∀ n inputs output, Function.Injective (@(nameMap E).operations n inputs output)

structure Sentence where
  environment : Environment
  assertions : Problem environment.signature

noncomputable def Sentence.Holds (s : Sentence) (M : GlobalModel) : Prop :=
  ∀ φ ∈ s.assertions, M.Holds (Term.map (nameMap s.environment) φ)

noncomputable def Sentence.Sat (s : Sentence) : Prop := ∃ M, s.Holds M

noncomputable def Sentence.Unsat (s : Sentence) : Prop := ¬ s.Sat

/-- Whole assertion lists over fixed raw declaration environments. -/
noncomputable def rawPlain : Plain (Disc Environment) where
  Sen E := Problem E.signature
  map σ Γ := σ.down ▸ Γ
  map_id _ _ := rfl
  map_comp σ τ Γ := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Mod E := Model E.signature
  reduct σ M := σ.down.symm ▸ M
  reduct_id _ _ := rfl
  reduct_comp σ τ M := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Sat M Γ := Γ.Holds M
  sat_map σ M Γ := by
    rcases σ with ⟨h⟩
    cases h
    rfl

noncomputable abbrev rawInstitution := rawPlain.toInst

/-- The room at a fixed environment is exactly a room of `rawInstitution`. -/
noncomputable abbrev fixedRoom (E : Environment) := rawPlain.room E

/-- Restrict the fixed-environment signatures to prefixes that really decoded. -/
noncomputable def checkedPlain : Plain (Disc DeclarationPrefix) where
  Sen checked := Problem checked.environment.signature
  map σ Γ := σ.down ▸ Γ
  map_id _ _ := rfl
  map_comp σ τ Γ := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Mod checked := Model checked.environment.signature
  reduct σ M := σ.down.symm ▸ M
  reduct_id _ _ := rfl
  reduct_comp σ τ M := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Sat M Γ := Γ.Holds M
  sat_map σ M Γ := by
    rcases σ with ⟨h⟩
    cases h
    rfl

noncomputable abbrev checkedInstitution := checkedPlain.toInst

noncomputable abbrev checkedRoom (checked : DeclarationPrefix) := checkedPlain.room checked

noncomputable def wholeRoom : Room :=
  ⟨Sentence, Disc.cat GlobalModel, fun M s => s.Holds M⟩

/-- Coherent whole-problem semantics as a singleton-signature institution. -/
noncomputable def plain : Plain (Disc Unit) where
  Sen _ := Sentence
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M s := s.Holds M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev institution := plain.toInst

/-- Direct whole concrete problems retain actual declaration/term decoder
equalities. This is a structured prefix plus assertions, not a flat-script parser. -/
structure ConcreteSentence where
  checked : DeclarationPrefix
  assertions : List (Assertion checked.environment)

def ConcreteSentence.toAbstract (s : ConcreteSentence) : Sentence :=
  ⟨s.checked.environment, s.assertions.map Assertion.formula⟩

/-- Direct concrete satisfaction uses accepted expressions in the reduct of
one coherent global interpretation of typed names. -/
noncomputable def ConcreteSentence.Holds (s : ConcreteSentence) (M : GlobalModel) : Prop :=
  AssertionsHolds s.assertions (M.reduct (nameMap s.checked.environment))

noncomputable def ConcreteSentence.Sat (s : ConcreteSentence) : Prop := ∃ M, s.Holds M

noncomputable def ConcreteSentence.Unsat (s : ConcreteSentence) : Prop := ¬ s.Sat

/-- Concrete assertion lists with a checked declaration prefix as signature,
before declarations are moved into each sentence. -/
noncomputable def concreteFixedPlain : Plain (Disc DeclarationPrefix) where
  Sen checked := List (Assertion checked.environment)
  map σ Γ := σ.down ▸ Γ
  map_id _ _ := rfl
  map_comp σ τ Γ := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Mod checked := Model checked.environment.signature
  reduct σ M := σ.down.symm ▸ M
  reduct_id _ _ := rfl
  reduct_comp σ τ M := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Sat M Γ := AssertionsHolds Γ M
  sat_map σ M Γ := by
    rcases σ with ⟨h⟩
    cases h
    rfl

noncomputable abbrev concreteFixedInstitution := concreteFixedPlain.toInst

noncomputable abbrev concreteFixedRoom (checked : DeclarationPrefix) :=
  concreteFixedPlain.room checked

noncomputable def concretePlain : Plain (Disc Unit) where
  Sen _ := ConcreteSentence
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := GlobalModel
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M s := s.Holds M
  sat_map _ _ _ := Iff.rfl

noncomputable abbrev concreteInstitution := concretePlain.toInst

noncomputable abbrev concreteRoom := concretePlain.room ()

/-- The name signature is populated at every sort, including unused sorts. -/
noncomputable def defaultValue (C : Carriers String) : (s : SortCode String) → C.value s
  | .bool => false
  | .int => 0
  | .user u => Classical.choice (C.nonempty u)

/-- Extend a local model by selecting its operation at names in the image,
and a constant operation elsewhere. Injectivity is used in the inverse law,
not to manufacture a model or a semantic certificate. -/
noncomputable def expand (E : Environment) (M : Model E.signature) : GlobalModel := by
  classical
  exact
    { carriers := M.carriers
      operation := fun {n inputs output} name args =>
        if h : ∃ symbol : E.signature.operations n inputs output,
            (nameMap E).operations symbol = name then
          M.operation (Classical.choose h) args
        else defaultValue M.carriers output }

end Silmaril.Logic.Smt.Uflia.Packaged
