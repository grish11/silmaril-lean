module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms

/-! # Native rows with finite typed reply profiles -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)

abbrev Atom := Visible.Atom
abbrev Atoms := Visible.Atoms
abbrev UnitTy := Visible.UnitTy

/-- Exact finite reply types assembled from empty, Unit, and binary sums. -/
inductive ReplyShape where
  | empty
  | unit
  | sum (left right : ReplyShape)
  deriving DecidableEq

def ReplyShape.ty : ReplyShape → Ty Atom
  | .empty => .empty
  | .unit => .unit
  | .sum l r => .coprod l.ty r.ty

abbrev ReplyShape.Value (s : ReplyShape) := Ty.denote Atoms s.ty

def ReplyShape.Code : ReplyShape → Type
  | .empty => Empty
  | .unit => Unit
  | .sum l r => l.Code ⊕ r.Code

/-- Every typed reply has a code in the event interface's universe. -/
def ReplyShape.replyEquiv : (s : ReplyShape) → s.Code ≃ s.Value
  | .empty =>
      ⟨Empty.elim, PEmpty.elim, (fun x => nomatch x), (fun x => nomatch x)⟩
  | .unit => ⟨fun _ => PUnit.unit, fun _ => (), fun _ => rfl, fun _ => rfl⟩
  | .sum l r => Equiv.sumCongr l.replyEquiv r.replyEquiv

/-- Each opcode has Unit input and its own finite reply type. Every opcode is visible. -/
class Profile (Φ : Type) where
  reply : Φ → ReplyShape

universe u v

variable {Φ : Type} [Profile Φ]

instance : HasTy Φ (Ty Atom) where
  src _ := UnitTy
  trg p := (Profile.reply p).ty

instance : HasEff Φ Bool where
  eff _ := true

abbrev Seed (Φ : Type) [Profile Φ] := WithPairReturns.JoinedStep (τ := Ty Atom) (Φ := Φ) false
abbrev Native (Φ : Type) [Profile Φ] := Paper.TypeCategory (τ := Ty Atom) Φ
abbrev Quotient (Φ : Type) [Profile Φ] := Extension.Singleton.TypeCategory (Seed Φ)
abbrev nativeUnit (Φ : Type) [Profile Φ] : Native Φ := Paper.TypeCategory.ofType UnitTy
abbrev nativeBit (Φ : Type) [Profile Φ] : Native Φ :=
  Paper.TypeCategory.ofType (Silmaril.coprod UnitTy UnitTy)
abbrev unitObj (Φ : Type) [Profile Φ] : Quotient Φ := Extension.Singleton.ofType (Seed Φ) UnitTy

/-- A node keeps the opcode and one continuation for each exactly typed reply. -/
inductive Row (Φ : Type) (α : Type u) [Profile Φ] where
  | leaf (outcome : α)
  | call (op : Φ) (next : (Profile.reply op).Value → Row Φ α)

def Row.map {α : Type u} {β : Type v} (f : α → β) : Row Φ α → Row Φ β
  | .leaf a => .leaf (f a)
  | .call p k => .call p (fun x => (k x).map f)

/-- Dispatch on the exact reply type by native coproducts. -/
noncomputable def dispatch {Y : Native Φ} (s : ReplyShape) :
    (s.Value → (nativeUnit Φ ⟶ Y)) → (Paper.TypeCategory.ofType s.ty ⟶ Y) :=
  match s with
  | .empty => fun _ => Paper.TypeCategory.emptyIsInitial.to Y
  | .unit => fun k => k PUnit.unit
  | .sum l r => fun k => (Paper.TypeCategory.sumIso l.ty r.ty).hom ≫
    coprod.desc (dispatch l (fun x => k (.inl x))) (dispatch r (fun x => k (.inr x)))

/-- Render a row entirely in standard Paper before projecting to the join. -/
noncomputable def Row.render {α : Type u} {Y : Native Φ} (leaf : α → (nativeUnit Φ ⟶ Y)) :
    Row Φ α → (nativeUnit Φ ⟶ Y)
  | .leaf a => leaf a
  | .call p k => Paper.TypeCategory.primitiveReturn p ≫
    dispatch (Profile.reply p) (fun x => (k x).render leaf)

noncomputable def nativeRoute : Route → (nativeUnit Φ ⟶ nativeUnit Φ ⨿ nativeBit Φ)
  | .exit => Paper.TypeCategory.discardArrow UnitTy ≫ coprod.inl
  | .first => (Paper.TypeCategory.sumCofan UnitTy UnitTy).inl ≫ coprod.inr
  | .second => (Paper.TypeCategory.sumCofan UnitTy UnitTy).inr ≫ coprod.inr

noncomputable def nativeTarget : Bool → (nativeUnit Φ ⟶ nativeUnit Φ ⨿ nativeUnit Φ)
  | false => Paper.TypeCategory.discardArrow UnitTy ≫ coprod.inl
  | true => Paper.TypeCategory.discardArrow UnitTy ≫ coprod.inr

open Extension.Singleton (projection projectStep sumIso)

noncomputable def projectRow (a : nativeUnit Φ ⟶ nativeUnit Φ ⨿ nativeBit Φ) :
    unitObj Φ ⟶ unitObj Φ ⨿ (unitObj Φ ⨿ unitObj Φ) :=
  (projection (Seed Φ)).map a ≫
    (PreservesColimitPair.iso (projection (Seed Φ)) (nativeUnit Φ) (nativeBit Φ)).inv ≫
    coprod.map (𝟙 (unitObj Φ)) (sumIso (Seed Φ) UnitTy UnitTy).hom

noncomputable abbrev fold : unitObj Φ ⨿ unitObj Φ ⟶ unitObj Φ :=
  coprod.desc (𝟙 (unitObj Φ)) (𝟙 (unitObj Φ))

noncomputable def sourceStep (l r : Row Φ Route) : unitObj Φ ⨿ unitObj Φ ⟶
    unitObj Φ ⨿ (unitObj Φ ⨿ unitObj Φ) :=
  coprod.desc (projectRow (l.render nativeRoute)) (projectRow (r.render nativeRoute))

noncomputable def targetStep (r : Row Φ Bool) : unitObj Φ ⟶ unitObj Φ ⨿ unitObj Φ :=
  projectStep (Seed Φ) (r.render nativeTarget)

/-- The visible request identifies the opcode even when two reply types coincide. -/
inductive Event (Φ : Type) [Profile Φ] : Type → Type where
  | call (op : Φ) : Event Φ (Profile.reply op).Code

abbrev Tree (Φ : Type) [Profile Φ] := ModelTree (Event Φ)

attribute [local instance] typeModel categoricalInstructions

instance : InstructionModel Φ (Ty Atom) Bool (Tree Φ) where
  denote p _ := vis (.call p) (fun x => pure ((Profile.reply p).replyEquiv x))
  denotePure _ h := by cases h
  denote_pure _ h := by cases h

def raw : Primitive (Event Φ) Φ (Sigma Atoms) :=
  fun p _ => vis (.call p) (fun x =>
    pure (encodeValue Atoms (Profile.reply p).ty ((Profile.reply p).replyEquiv x)))

theorem compatible :
    Compatible (κ' := Atom) ⟨fun (p : Φ) x => InstructionModel.denote
      (τ := Ty Atom) (ε := Bool) (m := Tree Φ) p x⟩ raw := by
  intro p x
  change raw p .unit = ((vis (.call p) (fun x => pure ((Profile.reply p).replyEquiv x)) :
    Tree Φ (Profile.reply p).Value) >>=
    fun y => pure (encodeValue Atoms (Profile.reply p).ty y))
  rw [raw, vis_bind]
  exact congrArg (vis (.call p)) (funext fun y =>
    (pure_bind (m := Tree Φ) ((Profile.reply p).replyEquiv y)
      (fun z => pure (encodeValue Atoms (Profile.reply p).ty z))).symm)

noncomputable def interpretation : Quotient Φ ⥤ Kleisli (ofTypeMonad (Tree Φ)) :=
  letI := regionTypingCoherent (raw (Φ := Φ)) compatible
  let J := typeJ (m := Tree Φ)
  let M := Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
  Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (joined_seedDenotes (Φ := Φ) J M (fun _ _ => ⟨rfl, rfl⟩) false)

namespace Example

inductive Op where
  | select
  | tick
  | halt

instance : Profile Op where
  reply
    | .select => .sum .unit (.sum .unit .unit)
    | .tick => .unit
    | .halt => .empty

/-- The ternary request can stay, switch, or inspect another ternary reply.
The nested request can exit or expose a final event with no reply. -/
def row (destination : Route) : Row Op Route :=
  .call .select (fun
    | .inl _ => .leaf .first
    | .inr (.inl _) => .call .tick (fun _ => .leaf .second)
    | .inr (.inr _) => .call .select (fun
      | .inl _ => .leaf destination
      | .inr (.inl _) => .leaf .exit
      | .inr (.inr _) => .call .halt PEmpty.elim))

abbrev left := row .second
abbrev right := row .first
abbrev target := left.map Route.recurrent

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies
