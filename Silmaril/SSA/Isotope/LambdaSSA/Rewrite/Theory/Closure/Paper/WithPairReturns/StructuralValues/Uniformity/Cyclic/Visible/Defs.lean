module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms

/-! # A visible two-cycle whose Unit modes fold to one loop -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)

abbrev Atom := PEmpty.{2}

instance : AtomValues Atom where
  carrier := PEmpty.elim

inductive Op where
  | poll
  | choose

inductive Event : Type → Type where
  | poll : Event Bool

instance : HasTy Op (Ty Atom) where
  src _ := .unit
  trg
    | .poll => .unit
    | .choose => .coprod .unit .unit

instance : HasEff Op Bool where
  eff _ := true

abbrev Tree := ModelTree Event
abbrev Atoms := AtomValues.carrier (κ := Atom)
abbrev UnitTy : Ty Atom := Silmaril.unit
abbrev ReplyTy : Ty Atom := Silmaril.coprod UnitTy UnitTy

/-- False keeps the current copy, and true switches it. -/
def replyValue : Bool → Ty.denote Atoms ReplyTy
  | false => .inl PUnit.unit
  | true => .inr PUnit.unit

attribute [local instance] typeModel categoricalInstructions

instance : InstructionModel Op (Ty Atom) Bool Tree where
  denote
    | .poll, _ => vis .poll (fun _ => pure PUnit.unit)
    | .choose, _ => vis .poll (fun b => pure (replyValue b))
  denotePure _ h := by cases h
  denote_pure _ h := by cases h

def raw : Primitive Event Op (Sigma Atoms)
  | .poll, _ => vis .poll (fun _ => pure .unit)
  | .choose, _ => vis .poll (fun b => pure (encodeValue Atoms ReplyTy (replyValue b)))

theorem compatible :
    Compatible (κ' := Atom) ⟨fun f x => InstructionModel.denote
      (τ := Ty Atom) (ε := Bool) (m := Tree) f x⟩ raw := by
  intro f x
  cases f
  · change raw Op.poll .unit = ((vis .poll (fun _ => pure PUnit.unit) : Tree (Ty.denote Atoms .unit)) >>=
      fun y => pure (encodeValue Atoms .unit y))
    rw [raw, vis_bind]
    exact congrArg (vis .poll) (funext fun _ => (pure_bind (m := Tree) PUnit.unit
      (fun y : PUnit.{2} => pure (encodeValue Atoms .unit y))).symm)
  · change raw Op.choose .unit = ((vis .poll (fun b => pure (replyValue b)) : Tree (Ty.denote Atoms ReplyTy)) >>=
      fun y => pure (encodeValue Atoms ReplyTy y))
    rw [raw, vis_bind]
    exact congrArg (vis .poll) (funext fun b => (pure_bind (m := Tree) (replyValue b)
      (fun y => pure (encodeValue Atoms ReplyTy y))).symm)

abbrev Seed := WithPairReturns.JoinedStep (τ := Ty Atom) (Φ := Op) false
abbrev Obj := ofType Seed
abbrev One := Obj UnitTy
abbrev Two := Obj (coprod UnitTy UnitTy)
abbrev Three := Obj (coprod UnitTy (coprod UnitTy UnitTy))

/-- The actual guarded primitive arrow, used for each edge in the cycle. -/
abbrev poll : One ⟶ One := Extension.Singleton.Generation.primitive Seed Op.poll

/-- Retained state exits. Each of the other two states polls and moves to the opposite state. -/
noncomputable def sourceRows : One ⨿ (One ⨿ One) ⟶ (One ⨿ One) ⨿ (One ⨿ One) :=
  coprod.desc (coprod.inl ≫ coprod.inl)
    (coprod.desc (poll ≫ coprod.inr ≫ coprod.inr) (poll ≫ coprod.inl ≫ coprod.inr))

/-- The folded modes form one polling self-loop. -/
noncomputable def targetRows : One ⨿ One ⟶ (One ⨿ One) ⨿ One :=
  coprod.desc (coprod.inl ≫ coprod.inl) (poll ≫ coprod.inr)

noncomputable abbrev sourceStep : Three ⟶ One ⨿ Three :=
  realize Seed (sourceIso Seed UnitTy) sourceRows

noncomputable abbrev targetStep : Two ⟶ One ⨿ Two :=
  realize Seed (targetIso Seed UnitTy) targetRows

noncomputable abbrev firstMode : One ⟶ Three :=
  coprod.inl ≫ coprod.inr ≫ (sourceIso Seed UnitTy).inv

noncomputable abbrev secondMode : One ⟶ Three :=
  coprod.inr ≫ coprod.inr ≫ (sourceIso Seed UnitTy).inv

noncomputable abbrev foldedMode : One ⟶ Two :=
  coprod.inr ≫ (targetIso Seed UnitTy).inv

local notation "J" => typeJ (m := Tree)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

/-- The ordered-pair quotient interpretation for the visible polling profile. -/
noncomputable def interpretation : Extension.Singleton.TypeCategory Seed ⥤ Kleisli (ofTypeMonad Tree) :=
  letI := regionTypingCoherent raw compatible
  Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
    (joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)

/-- Observe actual guarded iteration from a selected Unit mode. -/
noncomputable def runFrom (enter : One ⟶ Three) : Tree PUnit.{2} :=
  (interpretation.map (enter ≫ Extension.Singleton.iterateChosen Seed sourceStep)).of PUnit.unit

/-- The guarded primitive returns a typed two-way reply. -/
abbrev choose : One ⟶ Two := Extension.Singleton.Generation.primitive Seed Op.choose

noncomputable abbrev replyIso : Two ≅ One ⨿ One := Extension.Singleton.sumIso Seed UnitTy UnitTy

/-- False stays in the first mode, while true switches to the second. -/
noncomputable abbrev decision : One ⟶ (One ⨿ One) ⨿ (One ⨿ One) :=
  choose ≫ replyIso.hom ≫ coprod.inr

noncomputable def mixedSourceRows : One ⨿ (One ⨿ One) ⟶ (One ⨿ One) ⨿ (One ⨿ One) :=
  coprod.desc (coprod.inl ≫ coprod.inl)
    (coprod.desc decision (decision ≫ coprod.map (𝟙 (One ⨿ One)) (coprod.desc coprod.inr coprod.inl)))

noncomputable def mixedTargetRows : One ⨿ One ⟶ (One ⨿ One) ⨿ One :=
  coprod.desc (coprod.inl ≫ coprod.inl)
    (decision ≫ coprod.map (𝟙 (One ⨿ One)) (coprod.desc (𝟙 One) (𝟙 One)))

noncomputable abbrev mixedSourceStep : Three ⟶ One ⨿ Three :=
  realize Seed (sourceIso Seed UnitTy) mixedSourceRows

noncomputable abbrev mixedTargetStep : Two ⟶ One ⨿ Two :=
  realize Seed (targetIso Seed UnitTy) mixedTargetRows

/-- Observe actual feedback under the reply-dependent step. -/
noncomputable def runMixed (enter : One ⟶ Three) : Tree PUnit.{2} :=
  (interpretation.map (enter ≫ Extension.Singleton.iterateChosen Seed mixedSourceStep)).of PUnit.unit

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible
