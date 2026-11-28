module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical

/-! # Captured sentences in the categorical model class

The existing validity class has objects in `Type 1` and homs in `Type`.

The free request tree monad sends `Type 1` to `Type 1`. Its Kleisli
category satisfies every condition of the class with objects in `Type 2`
and homs in `Type 1`. `ValidAt` states the class at chosen universes, the
native equations are sound in it at every universe, and the Kleisli
category of any lawful Elgot monad is a member one universe above the
monad. This puts the free request model in the class at its own universes.

The ordered trace monad is an endofunctor on `Type`, so its Kleisli
category is a member of the existing class, and it is a model of the
existing ranked room. Its outcomes are the complete histories of the free
trees. On the structural captured fragment both give the same answer:
validity is native equality, and so is satisfaction in a handled-trace
model that replays every history.

What is not provided: a model of the existing rooms built from the tree
monad itself. Those rooms fix objects in `Type 1` and homs in `Type`, and
there is no universe-lowering of the tree Kleisli category here.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation)
open Region (packedExitType)
open Reverse (CheckedTable)
open Isotope.Semantics (BoundEnv)
open LambdaSSA.Semantics.Categorical (denoteRegion)
open LetIter.Semantics.Categorical (denoteOfType)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open LetSeq.StraightLine.Structural (Log)
open Free
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe u₁ u₂ v₁ v₂ w

/-! ## The class at chosen universes -/

section Class

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] {pe : ε}
  {n : Nat} {β : BoundCtx τ n} {a b : LetIter.LocallyNameless.Tm Empty Φ n} {A : τ}

/-- At objects in `Type 1` and homs in `Type` this is the existing validity. -/
theorem validAt_small_iff (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    ValidAt.{1, 1, 0, 0} pe da db ↔
      LetIter.Semantics.Categorical.Syntactic.RepairedLocallySmallValidity pe da db :=
  Iff.rfl

/-- Native equations hold in the class at every universe. -/
theorem validAt_of_equiv (h : LetIter.LocallyNameless.Equiv pe (Ctx.nil : Ctx Empty τ) β a b A)
    (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) β b A) :
    ValidAt.{u₁, u₂, v₁, v₂} pe da db :=
  validAt_of_equiv_proof h da db

end Class

/-! ## Kleisli categories as members, at any universe -/

section Kleisli

variable {α : Type} [DecidableEq α] (F : α → Type w)
  {m : Type w → Type w} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ ε : Type} [HasTy Φ (Ty α)] [HasEff Φ ε] [Bot ε]
  (M : Isotope.Semantics.InstructionModel (Ty.denote F) Φ m)
  {n : Nat} {β : BoundCtx (Ty α) n} {a b : LetIter.LocallyNameless.Tm Empty Φ n} {A : Ty α}

/-- The Kleisli category of a lawful Elgot monad on `Type w` is in the
class with objects in `Type (w + 1)` and homs in `Type w`. Validity at
those universes gives equal Kleisli arrows. -/
theorem arrow_eq_of_validAt (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β b A)
    (valid : ValidAt.{w + 1, w + 1, w, w} (⊥ : ε) da db) :
    denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db :=
  arrow_eq_of_validAt_proof F M pureM da db valid

omit [DecidableEq α] in
/-- Equal Kleisli arrows are equal monadic denotations at every bound
environment. -/
theorem denote_eq_of_arrow_eq
    (da : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β a A)
    (db : LetIter.LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β b A)
    (same : denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db)
    (ρ : BoundEnv (Ty.denote F) β) :
    da.denote (Ty.denote F) M (fun x => x.elim) ρ = db.denote (Ty.denote F) M (fun x => x.elim) ρ :=
  denote_eq_of_arrow_eq_proof F M da db same ρ

end Kleisli

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]

/-! ## The free request model, one universe up -/

/-- Natively equal operands are valid at every universe. -/
theorem caseValidAt_of_equiv {n : Nat} {γ : Context n} {B : Ty Empty} {a b : Operand Φ γ B}
    (h : Equiv false Γ₀ γ a.1 b.1 B) : CaseValidAt.{u₁, u₂, v₁, v₂} a b :=
  caseValidAt_of_equiv_proof h

/-- Validity at the universes of the tree Kleisli category gives equal
free trees in every environment. -/
theorem tree_eq_of_caseValidAt {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B)
    (valid : CaseValidAt.{2, 2, 1, 1} a b) (ρ : BoundEnv Val γ) :
    a.2.denote Val (model Φ) (fun x => x.elim) ρ = b.2.denote Val (model Φ) (fun x => x.elim) ρ :=
  tree_eq_of_caseValidAt_proof a b valid ρ

variable {d : Nat} {β : Context d} {A B : Ty Empty} {I J : LCtx (Ty Empty)}

/-- All-model equality one universe up: captured operands over a
structural older context are equal in every model of the class with
objects in `Type 2` and homs in `Type 1` exactly when they are natively
equal. The separating model is the free request tree model. -/
theorem caseValidAt_tree_iff_equiv (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    CaseValidAt.{2, 2, 1, 1} a b ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  caseValidAt_tree_iff_equiv_proof input a b

/-- Satisfaction in a handled-trace model that replays every history is
validity in the class one universe up. -/
theorem satLe_iff_caseValidAt_tree (input : StructuralContext β) {M : HandledModel Φ} (exposing : Exposing M)
    (a b : Operand Φ (β.snoc A) B) : SatLe M (captured a b) ↔ CaseValidAt.{2, 2, 1, 1} a b :=
  (satLe_iff_equiv input exposing a b).trans (caseValidAt_tree_iff_equiv input a b).symm

/-! ## The existing class and the ordered trace model -/

/-- At the universes of the existing class, operand validity is the
existing validity of the LetCase derivations. -/
theorem caseValidAt_small_iff {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B) :
    CaseValidAt.{1, 1, 0, 0} a b ↔ LetCase.Structural.Reply.Valid a.2 b.2 :=
  Iff.rfl

/-- All-model equality in the existing class: captured operands over a
structural older context are equal in every model of the existing class
exactly when they are natively equal. The separating model is the ordered
trace model. -/
theorem categorical_valid_iff_equiv (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    LetCase.Structural.Reply.Valid a.2 b.2 ↔ Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  valid_iff_equiv_proof input a b

/-- Satisfaction in a handled-trace model that replays every history is
validity in the existing class. -/
theorem satLe_iff_valid (input : StructuralContext β) {M : HandledModel Φ} (exposing : Exposing M)
    (a b : Operand Φ (β.snoc A) B) :
    SatLe M (captured a b) ↔ LetCase.Structural.Reply.Valid a.2 b.2 :=
  (satLe_iff_equiv input exposing a b).trans (categorical_valid_iff_equiv input a b).symm

/-- The two universes of the class agree on this fragment. -/
theorem caseValidAt_small_iff_tree (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    CaseValidAt.{1, 1, 0, 0} a b ↔ CaseValidAt.{2, 2, 1, 1} a b :=
  (categorical_valid_iff_equiv input a b).trans (caseValidAt_tree_iff_equiv input a b).symm

/-- The ordered trace model belongs to the existing ranked room. -/
noncomputable def traceRankedModel (Φ : Type) [LetCase.Structural.Finite.Signature Φ] :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Φ)) (sig Φ)).Mod :=
  ShrinkHoms.toShrinkHoms (Discrete.mk (traceRegionModel Φ))

/-- At the ordered trace model, the original ordered-exit arrows of two
written graphs agree exactly when their emitted operands are natively equal. -/
theorem ranked_trace_iff_equiv (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    (let := traceInstructions (α := Empty) (Φ := Φ)
     denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (p.table.toSSA_hasType 0 p.entry) =
       denoteRegion (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) (q.table.toSSA_hasType 0 q.entry)) ↔
      Equiv false Γ₀ (β.snoc (packedExitType I)) p.toLetCase.1 q.toLetCase.1 (packedExitType J) :=
  ranked_trace_iff_equiv_proof input p q

/-- Satisfaction of the existing ranked sentence in the existing ranked
room, at the ordered trace model, is native equality of the emitted operands. -/
theorem sat_rankedOf_trace_iff_equiv (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Φ)) (sig Φ)).Sat
        (traceRankedModel Φ) (rankedOf p q) ↔
      Equiv false Γ₀ (β.snoc (packedExitType I)) p.toLetCase.1 q.toLetCase.1 (packedExitType J) :=
  ranked_trace_iff_equiv input p q

/-- The satisfaction comparison on written endpoints: the categorical ranked
room at the ordered trace model and the handled-trace ranked room at a
model that replays every history satisfy the same ranked sentences. -/
theorem sat_rankedOf_trace_iff_handled (input : StructuralContext β) {M : HandledModel Φ} (exposing : Exposing M)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Φ)) (sig Φ)).Sat
        (traceRankedModel Φ) (rankedOf p q) ↔ (rankedRoom Φ).Sat ⟨M⟩ (rankedOf p q) :=
  (sat_rankedOf_trace_iff_equiv input p q).trans
    ((satLe_iff_equiv input exposing p.toLetCase q.toLetCase).symm.trans
      (Iff.of_eq (congrArg (SatLe M) (grammarCase_read_rankedOf p q).symm)))

/-- Validity in all handled-trace models is validity in the existing
categorical class, on captured operands over a structural older context. -/
theorem handled_valid_iff_categorical_valid (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B) :
    (∀ M : HandledModel Φ, SatLe M (captured a b)) ↔ LetCase.Structural.Reply.Valid a.2 b.2 :=
  (valid_iff_equiv input a b).trans (categorical_valid_iff_equiv input a b).symm

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
