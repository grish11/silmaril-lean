module

public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Semantics.Naming.Observations.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type}

/-- Named partial witnesses. A root is in the language when it has a witness. -/
abbrev PartialLanguage (Name : Type) := Relation Name (Partial Name)

namespace PartialLanguage

def roots (language : PartialLanguage Name) : Set Name := {root | ∃ tree, language root tree}

def shallowRoots (language : PartialLanguage Name) : Relation Name (Shallow Name) :=
  fun root source => ∃ tree, language root tree ∧ tree.shallow = source

/-- A root binding together with all the known object and blob link targets. -/
def witness (root : Name) (tree : Partial Name) : Store Name :=
  ⟨fun name source => (name = root ∧ source = tree.shallow) ∨ tree.bindings.objects name source,
    tree.bindings.blobs⟩

def observed (language : PartialLanguage Name) : Store Name := Stores.collect language witness

/-- Satisfaction is inclusion of every observed binding, not merely the absence of a conflict. -/
def Satisfies (language : PartialLanguage Name) (store : Store Name) : Prop :=
  ∀ ⦃root tree⦄, language root tree → PartialNames store root tree

def SaturatedIn (language : PartialLanguage Name) (store : Store Name) : Prop :=
  ∀ ⦃root seed tree⦄, language root seed → Extends seed tree → PartialNames store root tree → language root tree

def Saturated (language : PartialLanguage Name) : Prop := language.SaturatedIn language.observed

def HasShallowSeeds (language : PartialLanguage Name) : Prop :=
  ∀ ⦃root tree⦄, language root tree → language root tree.shallow.embed

/-- The presentations of exactly these shallow roots justified by the supplied store.
The store can have unobserved bindings and need not be reconstructed from the result. -/
def realize (roots : Relation Name (Shallow Name)) (store : Store Name) : PartialLanguage Name :=
  fun root tree => roots root tree.shallow ∧ PartialNames store root tree

/-- Only admit refinements whose observations are in the jointly binding union.
Joint binding of the inputs does not authorize other new bindings. -/
def expand (language : PartialLanguage Name) (external : Store Name)
    (_compatible : language.observed.MergeCompatible external) : PartialLanguage Name :=
  fun root tree => ∃ seed, language root seed ∧ Extends seed tree ∧
    PartialNames (language.observed.union external) root tree

end PartialLanguage

/-- Recognition is existential over finite fully expanded, nameless values. -/
def Recognized (store : Store Name) (language : Value → Prop) : Set Name :=
  {root | ∃ value, ValueNames store root value ∧ language value}

/-- Positive evidence from some partial witness. This is not a test for rejection
of the full-value language and is not the result of a particular observation policy. -/
def PartialRecognized (store : Store Name) (language : Partial Name → Prop) : Set Name :=
  {root | ∃ tree, PartialNames store root tree ∧ language tree}

end Silmaril.Formats.Dasl
