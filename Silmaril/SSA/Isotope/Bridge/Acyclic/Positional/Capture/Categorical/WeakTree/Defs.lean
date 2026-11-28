module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Defs

/-! # Checked tables in the weak-tree Kleisli model

The weak-tree model of a signature is the Kleisli category of the tree
monad over the structural interpretation of types. It has sorts in
`Type (u + 1)` for events in `Type u → Type u`, since a tree over those
events is one universe above its replies. An arrow into ordered exits
is observed as a weak tree of an exit position and its encoded payload. -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree

open CategoryTheory
open LambdaSSA.Semantics.Categorical (ctxObj labelObj denoteRegion)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Positional.Capture.Reverse (CheckedTable)

universe u v

variable {κ : Type (u + 1)} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  {Events : Type u → Type u}

attribute [local instance] typeModel categoricalInstructions

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "K" => typeJ (m := ModelTree Events)
local notation "T" => LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

/-- The weak tree of an arrow into ordered exits at an input: each exit
is its position and its encoded payload. -/
noncomputable def exitTree (L : LCtx (Ty κ)) {X : Type (u + 1)}
    (f : (K).obj X ⟶ (K).obj (labelObj T L)) (x : X) :
    ModelTree Events (Transfer (Sigma Atoms)) :=
  (show ModelTree Events (labelObj T L) from f.of x) >>= fun out =>
    pure (encodeLabel L ((LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L).symm out))

/-- The arrow of a checked table in the weak-tree model: the native
denotation of its region, from the captured context to the ordered
exits. The ranked institution's denotation of the entry of a checked
table unfolds to this region denotation, in its own fixed universes. -/
noncomputable def arrow {d : Nat} {β : BoundCtx (Ty κ) d} {L : LCtx (Ty κ)}
    (M : Model (κ := κ) Events Φ) (c : CheckedTable Φ β L) :
    (K).obj (ctxObj T β.toList) ⟶ (K).obj (labelObj T L) :=
  let _ := M.instructions
  denoteRegion K T c.toSSA_hasType

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree
