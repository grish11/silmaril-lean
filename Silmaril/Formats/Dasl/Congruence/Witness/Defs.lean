module

public import Silmaril.Formats.Dasl.Congruence.Thms
public import Silmaril.Formats.Dasl.Resolve.Refinement.Thms
public import Silmaril.Formats.Dasl.Wire.Profile.Defs
public import Silmaril.Semantics.OrderedMap.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.CongruenceWitness

open Silmaril.Semantics Naming

variable {Name : Type}

/-- Parse object bytes under the selected profile; keep blob bytes raw. The
caller supplies provenance/binding of bytes and the blob-name eligibility. -/
def decodedStore (profile : Wire.Profile Name) (blobName : Name → Bool)
    (wire : Stores Name ByteArray ByteArray) : Store Name where
  objects name source := profile.objectName name = true ∧ project wire.objects profile.parse? name source
  blobs name payload := blobName name = true ∧ wire.blobs name payload

/-- Bound the expansions that a certificate asserts. An eligible edge need not
be expanded; unknown and unfollowed edges may remain literal tagged references. -/
def Follows (allowed : Link Name → Prop) (tree : Partial Name) : Prop :=
  (∀ ⦃name source⦄, tree.bindings.objects name source → allowed (.obj name)) ∧
  (∀ ⦃name payload⦄, tree.bindings.blobs name payload → allowed (.blob name))

/-- A finite table of partial observations, and a finite list of proposed
equalities between named entries. Neither component claims constructor closure. -/
structure Certificate (Name : Type) [LinearOrder Name] where
  views : OrderedMap Name (Partial Name)
  claims : List (Name × Name)

variable [LinearOrder Name]

def Certificate.Valid (certificate : Certificate Name) (store : Store Name)
    (allowed : Link Name → Prop) : Prop :=
  (∀ ⦃name tree⦄, certificate.views.lookup? name = some tree → PartialNames store name tree ∧ Follows allowed tree) ∧
  (∀ ⦃left right⦄, (left, right) ∈ certificate.claims →
    (certificate.views.lookup? left).isSome ∧ (certificate.views.lookup? right).isSome)

/-- Self evidence for observations, plus both looked-up endpoints of each
explicit claim. Missing endpoints never contribute a pair. -/
def Certificate.edges (certificate : Certificate Name) (first second : Partial Name) : Prop :=
  (∃ name, certificate.views.lookup? name = some first ∧ first = second) ∨
  ∃ left right, (left, right) ∈ certificate.claims ∧
    certificate.views.lookup? left = some first ∧ certificate.views.lookup? right = some second

noncomputable def Certificate.seed (certificate : Certificate Name) : PER (Partial Name) :=
  PER.hull certificate.edges

/-- This uses the existing guarded DASL constructor closure; `allowed` on
store reads is separate from `enabled` on constructor shapes. -/
noncomputable def Certificate.generated (certificate : Certificate Name)
    (enabled : Tree.Shape (Link Name) Name → Prop) : PER (Partial Name) :=
  (Tree.constructors enabled).generated certificate.seed

/-- Report only named pairs with successful table lookups. This is a pullback,
not a constructor algebra or a rekeying theorem on names. -/
noncomputable def Certificate.named (certificate : Certificate Name)
    (enabled : Tree.Shape (Link Name) Name → Prop) : PER Name :=
  (certificate.generated enabled).decodePull certificate.views.lookup?

/-- The semantic checks that a model owes for the finitely generated evidence.
Store validity alone does not imply a proposed equality of distinct views. -/
def Certificate.CheckedBy (certificate : Certificate Name) (model : PER (Partial Name)) : Prop :=
  ∀ ⦃first second⦄, certificate.edges first second → model.rel first second

/-- Only extensions that retain the original bindings are considered. Missing
links may become known; the original certificate is not silently re-expanded. -/
def Compatible (base extended : Store Name) : Prop := base.Subset extended ∧ extended.Binding

end Silmaril.Formats.Dasl.CongruenceWitness
