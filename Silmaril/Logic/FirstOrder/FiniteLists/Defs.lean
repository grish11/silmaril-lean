module

public import Silmaril.Logic.Institution.Examples.FirstOrder
public import Silmaril.Logic.Institution.Structured.Constraints.Applications.ListAlgebras
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Independent finite-list FOL target. Sentences are all public FOL
sentences, not an image of Common Logic. Freeness constrains only nil/cons;
additional operations and relations remain arbitrary. This foundation contains
no Common Logic translation and asserts no first-order axiomatization of
standard finite lists. -/
@[expose] public section
namespace Silmaril.Logic.FirstOrder.FiniteLists
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured.Constraints
open Silmaril.Logic.Institution.Structured.Constraints.Applications

inductive ListSort where
  | discourse | reference | sequence
  deriving DecidableEq

def pair (a b : ListSort) : Fin 2 → ListSort := Fin.cases a (fun _ => b)

/-- Arbitrary additional operation and relation profiles over all three sorts. -/
structure Signature where
  Op : (n : Nat) → (Fin n → ListSort) → ListSort → Type
  Rel : (n : Nat) → (Fin n → ListSort) → Type

/-- Only nil and cons are reserved. Application, embeddings, constants and any
other client operations remain independently supplied ordinary FOL symbols. -/
inductive Operation (S : Signature) : (n : Nat) → (Fin n → ListSort) → ListSort → Type where
  | nil : Operation S 0 Fin.elim0 .sequence
  | cons : Operation S 2 (pair .discourse .sequence) .sequence
  | extra {n w s} : S.Op n w s → Operation S n w s

abbrev publicSignature (S : Signature) : FOL.Signature :=
  ⟨⟨ListSort, Operation S⟩, S.Rel⟩

structure Signature.Hom (S T : Signature) where
  ops : ∀ {n w s}, S.Op n w s → T.Op n w s
  rels : ∀ {n w}, S.Rel n w → T.Rel n w

@[ext] theorem Signature.Hom.ext {S T : Signature} (f g : Signature.Hom S T)
    (ho : @f.ops = @g.ops) (hr : @f.rels = @g.rels) : f = g := by
  cases f; cases g; cases ho; cases hr; rfl

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨fun o => o, fun r => r⟩
  comp f g := ⟨fun o => g.ops (f.ops o), fun r => g.rels (f.rels r)⟩
  id_comp _ := Signature.Hom.ext _ _ rfl rfl
  comp_id _ := Signature.Hom.ext _ _ rfl rfl
  assoc _ _ _ := Signature.Hom.ext _ _ rfl rfl

def Operation.map {S T : Signature} (f : S ⟶ T) :
    {n : Nat} → {w : Fin n → ListSort} → {s : ListSort} → Operation S n w s → Operation T n w s
  | _, _, _, .nil => .nil
  | _, _, _, .cons => .cons
  | _, _, _, .extra o => .extra (f.ops o)

def publicMap {S T : Signature} (f : S ⟶ T) :
    publicSignature S ⟶ publicSignature T where
  sorts := id
  ops := Operation.map f
  rels := f.rels

/-- Forget every other operation and relation BEFORE applying freeness. -/
def listReduct {S : Signature} (M : FOL.Structure (publicSignature S)) : Lists.Algebra where
  Elt := M.carrier .discourse
  Carrier := M.carrier .sequence
  nil := M.op Operation.nil (fun i => Fin.elim0 i)
  cons x xs := M.op Operation.cons (Fin.cases x (fun _ => xs))

/-- This semantic condition excludes junk and nonstandard lists. It is not
claimed to be axiomatizable by an ordinary first-order theory. -/
def IsFree {S : Signature} : ObjectProperty (FOL.Structure (publicSignature S)) :=
  fun M => FreeAt Lists.forget (listReduct M)

abbrev Model (S : Signature) := (IsFree (S := S)).FullSubcategory

/-- The target retains arbitrary FOL sentences, including reference quantifiers
and list equality; no source-image predicate restricts this sentence type. -/
def room (S : Signature) : Room.{0,0,1} :=
  ⟨FOL.Sentence (publicSignature S), Cat.of (Model S), fun M p => p.Holds M.obj⟩

/-- Every public FOL homomorphism gives a constructor-preserving list map. -/
def listHom {S : Signature} {M N : FOL.Structure (publicSignature S)} (h : M ⟶ N) :
    listReduct M ⟶ listReduct N where
  elt := h.map .discourse
  carrier := h.map .sequence
  map_nil := by
    change h.map .sequence (M.op Operation.nil (fun i => Fin.elim0 i)) = N.op Operation.nil (fun i => Fin.elim0 i)
    rw [h.map_op]
    congr 1
    funext i
    exact Fin.elim0 i
  map_cons x xs := by
    change h.map .sequence (M.op Operation.cons (Fin.cases x (fun _ => xs))) =
      N.op Operation.cons (Fin.cases (h.map .discourse x) (fun _ => h.map .sequence xs))
    rw [h.map_op]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The actual list-evaluation counit is invertible, by the existing universal
freeness theorem. Its domain is ALL actual finite lists of the element carrier. -/
noncomputable def evaluationIso {S : Signature} (M : Model S) :
    Lists.freeObject (M.obj.carrier .discourse) ≅ listReduct M.obj := by
  let evaluation : Lists.freeObject (M.obj.carrier .discourse) ⟶ listReduct M.obj :=
    Lists.adjunction.counit.app (listReduct M.obj)
  letI : IsIso evaluation :=
    (Lists.freeAt_iff_evaluation_isIso _).mp M.property
  exact asIso evaluation

/-- An equivalence with every actual finite list, rather than a Henkin list
subset, a bounded list universe or a merely injective constructor image. -/
noncomputable def evaluationEquiv {S : Signature} (M : Model S) :
    List (M.obj.carrier .discourse) ≃ M.obj.carrier .sequence where
  toFun := (evaluationIso M).hom.carrier
  invFun := (evaluationIso M).inv.carrier
  left_inv xs := congrArg
    (fun h : Lists.freeObject (M.obj.carrier .discourse) ⟶
      Lists.freeObject (M.obj.carrier .discourse) => h.carrier xs)
    (evaluationIso M).hom_inv_id
  right_inv xs := congrArg
    (fun h : listReduct M.obj ⟶ listReduct M.obj => h.carrier xs)
    (evaluationIso M).inv_hom_id

/-- The equivalence's forward map is the original constructor fold. -/
theorem evaluationEquiv_apply {S : Signature} (M : Model S)
    (xs : List (M.obj.carrier .discourse)) :
    evaluationEquiv M xs =
      List.foldr (listReduct M.obj).cons (listReduct M.obj).nil xs := rfl

/-- Canonical carrier interpretation for arbitrary native finite-list models. -/
def NativeCarrier (D R : Type) : ListSort → Type
  | .discourse => D
  | .reference => R
  | .sequence => List D

/-- Independent interpretations of every additional symbol; no source syntax
or source model occurs in this definition. Empty element carriers are allowed. -/
structure NativeModel (S : Signature) where
  Discourse : Type
  Reference : Type
  op : ∀ {n w s}, S.Op n w s →
    ((i : Fin n) → NativeCarrier Discourse Reference (w i)) →
    NativeCarrier Discourse Reference s
  rel : ∀ {n w}, S.Rel n w →
    ((i : Fin n) → NativeCarrier Discourse Reference (w i)) → Prop

def NativeModel.toStructure {S : Signature} (M : NativeModel S) :
    FOL.Structure (publicSignature S) where
  carrier := NativeCarrier M.Discourse M.Reference
  op o args := match o with
    | .nil => []
    | .cons => args 0 :: args 1
    | .extra o => M.op o args
  rel := M.rel

/-- Native finite-list models satisfy the existing freeness constraint. -/
theorem NativeModel.isFree {S : Signature} (M : NativeModel S) : IsFree M.toStructure := by
  change FreeAt Lists.forget (Lists.freeObject M.Discourse)
  exact Lists.freeAt_free M.Discourse

def NativeModel.toModel {S : Signature} (M : NativeModel S) : Model S :=
  ⟨M.toStructure, M.isFree⟩

/-- Client symbol reducts fix both list constructors and the list algebra. -/
def reduct {S T : Signature} (f : S ⟶ T) : Model T ⥤ Model S :=
  (IsFree (S := S)).lift ((IsFree (S := T)).ι ⋙ FOL.Structure.reduct (publicMap f))
    (fun M => M.property)

def corridor {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨FOL.Sentence.map (publicMap f), reduct f,
    fun M p => FOL.Sentence.holds_map (publicMap f) M.obj p⟩

end Silmaril.Logic.FirstOrder.FiniteLists
