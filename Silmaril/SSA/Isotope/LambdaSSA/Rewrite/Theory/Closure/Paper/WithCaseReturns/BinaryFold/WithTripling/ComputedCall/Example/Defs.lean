module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Example.ITree.Defs

/-! # Two requests whose result retains the original input -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Paper.WithComputedCallReturns.Example (Atom Op Payload nested sequenced nested_typed sequenced_typed)
open Paper.WithComputedCallReturns.Example.ITree (TreeModel Atoms raw compatible PayloadValue)
open Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.Extension.Singleton (ofType ofRegion)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)

abbrev Result : Ty Atom := .product Payload Payload
abbrev Seed := Step (τ := Ty Atom) (Φ := Op) false

def keepInput : Nat → Region Op := fun _ => .br 0 (.pair (.var 1) (.var 0))

theorem keepInput_typed : LSubst.ValueFamily [Payload] [Payload] [Result] keepInput := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))
  | succ i => simp [At] at hi

def source : Region Op := (returnRegion nested).lsubst keepInput

def explicitSequence : Region Op := (returnRegion sequenced).lsubst keepInput

theorem source_typed : ValueBranches [Payload] source [Result] :=
  (returnRegion_typed nested_typed).lsubst keepInput_typed

theorem explicitSequence_typed : ValueBranches [Payload] explicitSequence [Result] :=
  (returnRegion_typed sequenced_typed).lsubst keepInput_typed

def sourceArrow : ofType Seed Payload ⟶ ofType Seed Result := ofRegion Seed source_typed

def explicitArrow : ofType Seed Payload ⟶ ofType Seed Result := ofRegion Seed explicitSequence_typed

attribute [local instance] typeModel categoricalInstructions

noncomputable def treeInterpretation :
    TypeCategory (τ := Ty Atom) (Φ := Op) false ⥤ Kleisli (ofTypeMonad TreeModel) :=
  letI := regionTypingCoherent raw compatible
  denoteFunctor false (typeJ (m := TreeModel))
    (Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)) (fun _ _ => ⟨rfl, rfl⟩)

open Paper.WithComputedCallReturns.Example.ITree (Request reply)
open Silmaril.Elgot.ITree

/-- The consumer takes the first answer, and the final pair keeps the
original input separately from the second answer. -/
def expected (x : PayloadValue) : TreeModel (Ty.denote Atoms Result) :=
  vis (Request.call Op.produce x.down) (fun produced =>
    vis (Request.call Op.consume produced) (fun consumed => pure (x, reply consumed)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
