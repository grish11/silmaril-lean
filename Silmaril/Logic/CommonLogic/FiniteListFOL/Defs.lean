module

public import Silmaril.Logic.FirstOrder.FiniteLists.Thms
public import Silmaril.Logic.CommonLogic.Core.Thms

/-! Common Logic's full semantic data presented by independent many-sorted FOL.
The target still admits ALL FOL sentences. Nil/cons alone receive freeness;
embedding, application, predicates, append and constants are ordinary symbols. -/
@[expose] public section
namespace Silmaril.Logic.CommonLogic.FiniteListFOL
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder

inductive Op (S : Core.Signature) : (n : Nat) →
    (Fin n → FiniteLists.ListSort) → FiniteLists.ListSort → Type where
  | discourse : S.discourse → Op S 0 Fin.elim0 .discourse
  | nondiscourse : S.nondiscourse → Op S 0 Fin.elim0 .reference
  | marker : S.marker → Op S 0 Fin.elim0 .sequence
  | embed : Op S 1 (fun _ => .discourse) .reference
  | apply : Op S 2 (FiniteLists.pair .reference .sequence) .discourse
  | append : Op S 2 (FiniteLists.pair .sequence .sequence) .sequence

inductive Rel (S : Core.Signature) : (n : Nat) → (Fin n → FiniteLists.ListSort) → Type where
  | holds : Rel S 2 (FiniteLists.pair .reference .sequence)

abbrev signature (S : Core.Signature) : FiniteLists.Signature := ⟨Op S, Rel S⟩

def signatureMap {S T : Core.Signature} (f : S ⟶ T) :
    signature S ⟶ signature T where
  ops o := match o with
    | .discourse n => .discourse (f.discourse n)
    | .nondiscourse n => .nondiscourse (f.nondiscourse n)
    | .marker n => .marker (f.marker n)
    | .embed => .embed
    | .apply => .apply
    | .append => .append
  rels r := match r with | .holds => .holds

abbrev Target (S : Core.Signature) := FiniteLists.Model (signature S)
abbrev D {S : Core.Signature} (M : Target S) := M.obj.carrier .discourse
abbrev R {S : Core.Signature} (M : Target S) := M.obj.carrier .reference
abbrev L {S : Core.Signature} (M : Target S) := M.obj.carrier .sequence

def discourse {S : Core.Signature} (M : Target S) (n : S.discourse) : D M :=
  M.obj.op (.extra (.discourse n)) (fun i => Fin.elim0 i)

def nondiscourse {S : Core.Signature} (M : Target S) (n : S.nondiscourse) : R M :=
  M.obj.op (.extra (.nondiscourse n)) (fun i => Fin.elim0 i)

def marker {S : Core.Signature} (M : Target S) (n : S.marker) : L M :=
  M.obj.op (.extra (.marker n)) (fun i => Fin.elim0 i)

def embed {S : Core.Signature} (M : Target S) (x : D M) : R M :=
  M.obj.op (.extra .embed) (fun _ => x)

def apply {S : Core.Signature} (M : Target S) (r : R M) (xs : L M) : D M :=
  M.obj.op (.extra .apply) (Fin.cases r (fun _ => xs))

def append {S : Core.Signature} (M : Target S) (xs ys : L M) : L M :=
  M.obj.op (.extra .append) (Fin.cases xs (fun _ => ys))

def holds {S : Core.Signature} (M : Target S) (r : R M) (xs : L M) : Prop :=
  M.obj.rel Rel.holds (Fin.cases r (fun _ => xs))

/-- Ordinary model restrictions beyond the independent list-freeness layer.
Append is constrained by its two constructor equations, not by assuming a
source satisfaction theorem. No restriction is placed on reference elements
outside the embedding and the named nondiscourse constants. -/
structure ConstraintsData {S : Core.Signature} (M : Target S) : Prop where
  inhabited : Nonempty (D M)
  injective : Function.Injective (embed M)
  outside : ∀ n x, embed M x ≠ nondiscourse M n
  append_nil : ∀ ys, append M (FiniteLists.listReduct M.obj).nil ys = ys
  append_cons : ∀ x xs ys,
    append M ((FiniteLists.listReduct M.obj).cons x xs) ys =
      (FiniteLists.listReduct M.obj).cons x (append M xs ys)

/-- The object predicate retains every homomorphism between constrained models.
The field-bearing data and the categorical ObjectProperty are explicit. -/
def Constraints {S : Core.Signature} : ObjectProperty (Target S) :=
  fun M => ConstraintsData M

abbrev Model (S : Core.Signature) := (Constraints (S := S)).FullSubcategory

/-- Target sentences include arbitrary reference quantifiers and list equality,
not just translations of Core formulas. Every underlying FOL model arrow is kept. -/
def room (S : Core.Signature) : Room.{0,0,1} :=
  ⟨FOL.Sentence (FiniteLists.publicSignature (signature S)), Cat.of (Model S),
    fun M p => p.Holds M.obj.obj⟩

/-- Decode through the actual ALL-finite-list evaluation equivalence. -/
noncomputable def decode {S : Core.Signature} (M : Model S) : Core.Model S where
  Reference := R M.obj
  Discourse := D M.obj
  nonempty := M.property.inhabited
  embed := embed M.obj
  injective := M.property.injective
  discourse := discourse M.obj
  nondiscourse := nondiscourse M.obj
  outside := M.property.outside
  sequence n := (FiniteLists.evaluationEquiv M.obj).symm (marker M.obj n)
  function r xs := apply M.obj r (FiniteLists.evaluationEquiv M.obj xs)
  relation r xs := holds M.obj r (FiniteLists.evaluationEquiv M.obj xs)

/-- Canonical expansion uses literal native List D and the original two
universes/extensions. It needs no guessed filler or source fragment restriction. -/
def native {S : Core.Signature} (M : Core.Model S) : FiniteLists.NativeModel (signature S) where
  Discourse := M.Discourse
  Reference := M.Reference
  op o args := match o with
    | .discourse n => M.discourse n
    | .nondiscourse n => M.nondiscourse n
    | .marker n => M.sequence n
    | .embed => M.embed (args 0)
    | .apply => M.function (args 0) (args 1)
    | .append => List.append (args 0) (args 1)
  rel r args := match r with | .holds => M.relation (args 0) (args 1)

theorem native_constraints {S : Core.Signature} (M : Core.Model S) :
    Constraints (native M).toModel where
  inhabited := M.nonempty
  injective := M.injective
  outside := M.outside
  append_nil := fun _ => rfl
  append_cons := fun _ _ _ => rfl

def expand {S : Core.Signature} (M : Core.Model S) : Model S :=
  ⟨(native M).toModel, native_constraints M⟩

/-- Signature reduct retains all target model arrows and list freeness. -/
theorem constraints_reduct {S T : Core.Signature} (f : S ⟶ T) (M : Model T) :
    Constraints ((FiniteLists.reduct (signatureMap f)).obj M.obj) where
  inhabited := M.property.inhabited
  injective := M.property.injective
  outside n := M.property.outside (f.nondiscourse n)
  append_nil := M.property.append_nil
  append_cons := M.property.append_cons

def reduct {S T : Core.Signature} (f : S ⟶ T) : Model T ⥤ Model S :=
  (Constraints (S := S)).lift
    ((Constraints (S := T)).ι ⋙ FiniteLists.reduct (signatureMap f))
    (constraints_reduct f)

def corridor {S T : Core.Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨FOL.Sentence.map (FiniteLists.publicMap (signatureMap f)), reduct f,
    fun M p => FOL.Sentence.holds_map (FiniteLists.publicMap (signatureMap f)) M.obj.obj p⟩

end Silmaril.Logic.CommonLogic.FiniteListFOL
