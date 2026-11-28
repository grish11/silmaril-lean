module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms

/-! # The guarded packed CFG in the weak ITree Kleisli model

The value category is `Type` on the structural type interpretation. Primitive
arrows carry a typed ITree profile and have the same effect and reply trees
on encoded inputs as the erased interpreter. The standard Type–Kleisli
tensor comparison is reflexivity, and its unit is central. Under these
choices the Paper soundness theorem identifies the denotations of all
guarded representatives of a singleton arrow.
-/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Region Region.Paper.TypeCategory
open scoped MonoidalCategory

variable {κ : Type (v + 1)} [AtomValues κ] {F : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel

variable [InstructionModel Φ (Ty κ) Bool (ModelTree F)]
  (raw : Primitive F Φ (Sigma (AtomValues.carrier (κ := κ))))

local notation "V" => AtomValues.carrier (κ := κ)
local notation "TM" => ModelTree F
local notation "K" => typeJ (m := TM)
local notation "T" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

attribute [local instance] categoricalInstructions

private theorem shared (F : Type v → Type v) (X Y : Type (v + 1)) :
    ∃ h : (typeJ (m := ModelTree F)).obj X ⊗ (typeJ (m := ModelTree F)).obj Y =
        (typeJ (m := ModelTree F)).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := typeJ (m := ModelTree F)) X Y = eqToIso h :=
  ⟨rfl, rfl⟩

variable {blocks exits : Nat} {R : Fin blocks → Ty κ} {D : Fin exits → Ty κ}
  {g : FiniteCFG Φ blocks exits 0}

local notation "S" => packedExitType (List.ofFn R)
local notation "Y" => packedExitType (List.ofFn D)

set_option backward.isDefEq.respectTransparency false in
/-- The actual guarded dispatcher, read in the exact sum coordinates supplied
by `sumIso`, computes the literal one-step dispatcher tree. -/
theorem packedDispatcher_kleisli_tree_proof
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree F) f x⟩ raw)
    (hg : HasType .nil R D g)
    (s : Ty.denote V S) (env : Env (Sigma V)) :
    ((show TM _ from (denoteArrow K T (packedDispatcher hg ≫ (sumIso Y S).inv)).of s) >>=
      fun t => pure (0, encodeValue V (Silmaril.coprod Y S) t)) =
      region raw (extend env (encodeValue V S s)) (packedDispatcherRegion hg) := by
  let := regionTypingCoherent raw compat
  rw [packedDispatcher_ofRegion, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    denoteArrow_ofRegion K T (shared F)]
  exact singletonDenote_tree raw compat
    (packedDispatcher_valueBranches hg).hasType s env

/-- The same dispatcher equation in the model's chosen binary coproduct.
The Type coproduct comparison exposes the ordinary return-or-repeat sum. -/
theorem packedDispatcher_kleisli_sum_tree_proof
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree F) f x⟩ raw)
    (hg : HasType .nil R D g) (s : Ty.denote V S) (env : Env (Sigma V)) :
    ((show TM _ from (denoteSumArrow K T (packedDispatcher hg)).of s) >>= fun t =>
      pure (0, encodeValue V (Silmaril.coprod Y S)
        ((Types.binaryCoproductIso ((T).obj Y) ((T).obj S)).hom t))) =
      region raw (extend env (encodeValue V S s)) (packedDispatcherRegion hg) := by
  let c : TM (Ty.denote V (Silmaril.coprod Y S)) :=
    (denoteArrow K T (packedDispatcher hg ≫ (sumIso Y S).inv)).of s
  let tag : Ty.denote V (Silmaril.coprod Y S) → TM (((T).obj Y) ⨿ ((T).obj S)) :=
    fun t => pure (((T).coprodIso Y S).hom t)
  let output : (((T).obj Y) ⨿ ((T).obj S)) → TM (Transfer (Sigma V)) :=
    fun t => pure (0, encodeValue V (Silmaril.coprod Y S)
      ((Types.binaryCoproductIso ((T).obj Y) ((T).obj S)).hom t))
  unfold denoteSumArrow
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  change ((c >>= tag) >>= output) = _
  have tagged (t : Ty.denote V (Silmaril.coprod Y S)) :
      (tag t >>= output) = (pure (0, encodeValue V (Silmaril.coprod Y S) t) : TM _) := by
    unfold tag output
    rw [pure_bind (m := ModelTree F), Semantics.Agreement.coprod_hom_agrees]
    rfl
  exact ((bind_assoc c tag output).trans (bind_congr tagged)).trans
    (packedDispatcher_kleisli_tree_proof raw compat hg s env)

/-- Evaluating the actual guarded arrow for the entry followed by feedback
produces the written source graph's tree with its outward transfer packed. -/
theorem packedExecution_kleisli_tree_proof
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree F) f x⟩ raw)
    (hg : HasType .nil R D g) (env : Env (Sigma V)) :
    ((show TM _ from (denoteArrow K T (packedExecution hg)).of PUnit.unit) >>=
      fun b => pure (0, encodeValue V Y b)) =
      (region raw env g.erase >>= fun p => pure (packedTreeOutput p)) := by
  let := regionTypingCoherent raw compat
  rw [packedExecution_ofRegion, denoteArrow_ofRegion K T (shared F)]
  exact (singletonDenote_tree raw compat
    (packedExecution_valueBranches hg).hasType PUnit.unit env).trans
      (packedExecution_representative_tree raw hg env .unit)

end Silmaril.Isotope.LambdaSSA.FiniteCFG
