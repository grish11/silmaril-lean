module

public import Silmaril.Logic.Egglog.Source.Named.Syntax.Defs
public import Silmaril.Logic.Egglog.Core.Defs
public import Silmaril.Logic.Smt.SExpr.Writer.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory

structure DeclarationData where
  sorts : List String
  constructors : List TotalDeclaration
  relations : List RelationDeclaration
  functions : List TotalDeclaration
  deriving DecidableEq, Repr

/-- User identifiers exclude grammar tags as well as lexical delimiters. -/
def LegalName (name : String) : Prop :=
  Smt.SExpr.Writer.LegalAtom name ∧
    name ∉ ["sort", "constructor", "relation", "function", "rule", "query", "var", "app",
      "equal", "row"]

def DeclarationData.Valid (D : DeclarationData) : Prop :=
  D.sorts.Nodup ∧
  (D.constructors.map TotalDeclaration.name ++ D.relations.map RelationDeclaration.name ++
    D.functions.map TotalDeclaration.name).Nodup ∧
  (∀ s ∈ D.sorts, LegalName s) ∧
  (∀ d ∈ D.constructors ++ D.functions,
    LegalName d.name ∧ (∀ s ∈ d.inputs, s ∈ D.sorts) ∧ d.output ∈ D.sorts) ∧
  (∀ d ∈ D.relations, LegalName d.name ∧ ∀ s ∈ d.inputs, s ∈ D.sorts)

/-- Finite checked declaration data; no ambient sort equality is required. -/
structure Declarations where
  data : DeclarationData
  valid : data.Valid

namespace Declarations
abbrev LocalSort (D : Declarations) := { name : String // name ∈ D.data.sorts }

/-- A symbol is a finite declaration witness at its exact ordered profile.
No constructor freeness, nonempty carrier, or total table is imposed. -/
def signature (D : Declarations) : Core.Signature where
  S := D.LocalSort
  Op := fun n w s => { d : TotalDeclaration // d ∈ D.data.constructors ∧
    d.inputs = List.ofFn (fun i : Fin n => (w i).val) ∧ d.output = s.val }
  Rel := fun n w => { d : RelationDeclaration // d ∈ D.data.relations ∧
    d.inputs = List.ofFn (fun i : Fin n => (w i).val) }
  Function := fun n w s => { d : TotalDeclaration // d ∈ D.data.functions ∧
    d.inputs = List.ofFn (fun i : Fin n => (w i).val) ∧ d.output = s.val }
end Declarations

/-- A finite vocabulary may name part of an infinite ambient signature; distinct
local names may map to the same ambient sort or symbol. -/
structure NameView (S : Core.Signature) where
  declarations : Declarations
  symbols : declarations.signature ⟶ S

/-- A checked context retains every position and its declared sort. -/
structure CheckedContext (D : Declarations) where
  bindings : Context
  unique : (bindings.map Binding.name).Nodup
  declared : ∀ i : Fin bindings.length, (bindings.get i).sort ∈ D.data.sorts

def CheckedContext.profile {D : Declarations} (Γ : CheckedContext D) :
    Fin Γ.bindings.length → D.LocalSort :=
  fun i => ⟨(Γ.bindings.get i).sort, Γ.declared i⟩

end Silmaril.Logic.Egglog.Source.Named
