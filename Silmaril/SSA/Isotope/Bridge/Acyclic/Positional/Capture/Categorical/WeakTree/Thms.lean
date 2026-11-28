module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree

/-! # The arrow of a checked table as a weak tree

The native law of a checked table, `Table.toLetCase_denote`, holds in
any strong Elgot Freyd category with a central unit and coherent region
typing. This file reads it in the weak-tree Kleisli model and compares
the arrow of the table with the weak tree of its erased readback.

## The model

The model is the existing one, with no new semantic definitions.

* The category is the Kleisli category of `ModelTree Events` over
  `Type (u + 1)`, for events in `Type u → Type u`.
* The signature is any `Φ : Type v` with source, target and Boolean
  effect over the sorts `Ty κ`, for `κ : Type (u + 1)` with carriers.
* The primitive data is an `Ordered.Model`: typed primitives, erased
  primitives, and their compatibility. Compatibility gives coherent
  region typing by `regionTypingCoherent`; the unit is central in any
  Kleisli category of a strong monad.

So the law of the table is instantiated as it is stated.

## What had to be added

The law equates the arrow of the table with the categorical denotation
of its readback, between a context map and the unpacking of the exits.
The categorical denotation of a LetCase term was related to the direct
monadic one only at a different presentation of the structural type
model. The two presentations are equal: they differ in the witness that
the empty type is initial, which is unique. With that, the categorical
denotation of a LetCase term in this model returns the weak tree of the
erased term.

## The common observable

The arrow of the table ends in the ordered exits, and its tree returns
the position and the encoded payload of the exit taken. The readback
returns one value of the packed sum of the exits. The law joins them by
unpacking: the injection at the single label, then the decoding of the
packed sum. On encoded values, unpacking then packing the exit at
label `0` is the identity. So the two sides are compared in two ways.

* Packed: the tree of the arrow with each exit packed at label `0` is
  the tree of the readback at label `0`.
* Ordered: packing is injective on exits, so when the readback returns
  the packing of an ordered tree, the tree of the arrow is that tree.

## What is not claimed

An arrow of another model is not a weak tree. The ranked institution
fixes sorts and signatures in `Type` and categories with objects in
`Type 1` and morphisms in `Type`. The weak-tree Kleisli category has
objects in `Type (u + 2)` and morphisms in `Type (u + 1)`, and its
sorts are in `Type (u + 1)`, at every `u`. So this model is not one of
the models of that institution, and `arrow` is stated as the region
denotation that the institution's denotation unfolds to.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree

open CategoryTheory
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject unpackLabelExit)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.Semantics.Monadic (LabelValue)
open Silmaril.Isotope.Semantics (encodeValue)
open LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open LetIter.Semantics.Categorical (envObj boundLookup)
open LetCase.LocallyNameless (Derivation)
open Morphism.CaseSSA (erase)
open Positional.Capture.Reverse (CheckedTable)
open Region (packedExitType packedExitValue)

universe u v

variable {κ : Type (u + 1)} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  {Events : Type u → Type u}

attribute [local instance] typeModel categoricalInstructions

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty κ))
local notation "K" => typeJ (m := ModelTree Events)
local notation "T" => LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
/-- The type model of the weak-tree Kleisli model is the structural
type model of the Kleisli soundness theorems. -/
theorem types_eq : T = LetIter.Semantics.Categorical.ofTypeModel (Ty.denote Atoms) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.types_eq_proof

/-- The categorical denotation of a LetCase term in the weak-tree model
returns the weak tree of the erased term, at an environment that encodes
the bound part of the input. -/
theorem letCase_tree {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty κ} (M : Model (κ := κ) Events Φ)
    (d : Derivation Φ Γ₀ β t A) (x : envObj T Γ₀ β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = encodeValue Atoms (β.get i) (boundLookup T i x.2)) :
    let _ := M.instructions
    ((show ModelTree Events (Ty.denote Atoms A) from
        (LetCase.Semantics.Categorical.denote K T d).of x) >>= fun a =>
          pure (encodeValue Atoms A a)) =
      LambdaSSA.Semantics.Interaction.term M.raw env (erase t) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.letCase_tree_proof
    M d x env agree

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
/-- Unpacking a value of the packed sum into the ordered exits and
packing the exit at label `0` returns the encoded value. -/
theorem unpack_packed (L : LCtx (Ty κ)) (v : Ty.denote Atoms (packedExitType L)) :
    FiniteCFG.packedTreeOutput (encodeLabel L ((LabelValue.categoricalEquiv L).symm
        ((labelInject T (L := [packedExitType L]) 0 rfl ≫ unpackLabelExit T L) v))) =
      (0, encodeValue Atoms (packedExitType L) v) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.unpack_packed_proof
    L v

omit [AtomValues κ] [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
/-- Packing an exit at label `0` keeps its position and its payload. -/
theorem packedTreeOutput_injective {α : Type (u + 1)} :
    Function.Injective (FiniteCFG.packedTreeOutput (α := α)) :=
  open Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree in
  packedTreeOutput_injective_proof

omit [AtomValues κ] [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
/-- Trees of ordered exits with the same packing at label `0` are equal. -/
theorem packed_injective {α : Type (u + 1)} (a b : ModelTree Events (Transfer α))
    (eq : (a >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (b >>= fun out => pure (FiniteCFG.packedTreeOutput out))) : a = b :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.packed_injective_proof
    a b eq

variable {d : Nat} {β : BoundCtx (Ty κ) d} {L : LCtx (Ty κ)}

/-- The arrow of a checked table, with each exit packed at label `0`,
is the weak tree of the erased readback at label `0`. The environment
encodes the bound part of the context map of the input. -/
theorem arrow_packed (M : Model (κ := κ) Events Φ) (c : CheckedTable Φ β L)
    (y : ctxObj T β.toList) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val =
      encodeValue Atoms (β.get i) (boundLookup T i (contextMap T β y).2)) :
    (exitTree L (arrow M c) y >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (LambdaSSA.Semantics.Interaction.term M.raw env (erase c.toLetCase.1) >>= fun value =>
        pure (0, value)) :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.arrow_packed_proof
    M c y env agree

/-- When the readback returns the packing of an ordered tree, the arrow
of the table has that tree at its ordered exits. -/
theorem arrow_ordered (M : Model (κ := κ) Events Φ) (c : CheckedTable Φ β L)
    (y : ctxObj T β.toList) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val =
      encodeValue Atoms (β.get i) (boundLookup T i (contextMap T β y).2))
    (ordered : ModelTree Events (Transfer (Sigma Atoms)))
    (readback : LambdaSSA.Semantics.Interaction.term M.raw env (erase c.toLetCase.1) =
      ordered >>= fun out => pure (packedExitValue out.1 out.2)) :
    exitTree L (arrow M c) y = ordered :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.arrow_ordered_proof
    M c y env agree ordered readback

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree
