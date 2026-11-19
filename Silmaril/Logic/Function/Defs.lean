module

public import Silmaril.Logic.Fragments.Institution.Defs
public import Silmaril.Semantics.Function.Defs

/-! # Function rooms

These are the existing atomic rooms instantiated at function judgments.
Reduct recovers raw atoms, not an exact graph after collapsing names. A
lawful reduct needs rule transport, not just a function between atom types.
-/

@[expose] public section
namespace Silmaril.Logic.Function
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Fragments
open Silmaril.Semantics.Function
universe u

@[ext] structure Renaming (A B : Signature.{u}) where
  context : A.Context → B.Context
  internal : A.Internal → B.Internal
  foreign : A.Foreign → B.Foreign
  site : A.Site → B.Site
  body : A.Body → B.Body

instance : Category Signature.{u} where
  Hom := Renaming
  id _ := ⟨id, id, id, id, id⟩
  comp f g := ⟨g.context ∘ f.context, g.internal ∘ f.internal, g.foreign ∘ f.foreign,
    g.site ∘ f.site, g.body ∘ f.body⟩

variable {A B : Signature.{u}}

def Renaming.node (f : A ⟶ B) : Node A → Node B
  | .localFn name => .localFn (f.internal name)
  | .foreign name => .foreign (f.foreign name)

def Renaming.edge (f : A ⟶ B) (edge : Edge A) : Edge B :=
  ⟨⟨f.internal edge.origin.caller, f.site edge.origin.site, edge.origin.transfer⟩,
    edge.dispatch, f.node edge.callee⟩

def Renaming.atom (f : A ⟶ B) : Atom A → Atom B
  | .node context name => .node (f.context context) (f.node name)
  | .body context name row => .body (f.context context) (f.internal name) (f.body row)
  | .call context edge => .call (f.context context) (f.edge edge)

def atomSignature (A : Signature.{u}) : AtomicSignature.{u} := ⟨Atom A⟩

def reduct (f : A ⟶ B) (model : Model B) : Model A :=
  Silmaril.Semantics.Region.Abstract.reindex f.atom model

def room (A : Signature.{u}) : Room.{u,u,u} := atomicRoom (atomSignature A)

end Silmaril.Logic.Function
