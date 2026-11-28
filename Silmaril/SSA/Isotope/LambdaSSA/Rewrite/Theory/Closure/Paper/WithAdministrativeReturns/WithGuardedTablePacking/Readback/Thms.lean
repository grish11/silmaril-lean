module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Readback

/-! # Readback of every nonempty guarded table, and its exit retraction

The readback holds at one capture and one outward exit. The retraction
extends it to any ordered exit list by the native literal tagging and
decoding of exits. Neither statement covers an empty table or a table
whose rows are not guarded.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- At any arity, the comparison is exactly the contextual equation
between the written table and its packed representative. The assembled
side uses inherited equations only. -/
theorem readback_iff_eqv {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R he hb ↔ Eqv pe [X] (.cfg e n blocks) (packedReadbackRep R he hb).val [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.readback_iff_eqv pe R he hb

/-- Every nonempty guarded table equals its captured dispatcher readback.
The entry and rows are arbitrary guarded regions and may reach each other. -/
theorem readback {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R he hb :=
  (readback_iff_eqv pe R he hb).2 (pack pe R he hb)

/-- A readback of the unary-return quotient remains one here, at any arity. -/
theorem readback_of_unaryReturns {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (h : WithUnaryReturns.TableReadback.Readback pe R he hb) : Readback pe R he hb :=
  (readback_iff_eqv pe R he hb).2 (ofAdministrativeReturns pe
    (WithAdministrativeReturns.ofUnaryReturns pe
      ((WithUnaryReturns.TableReadback.readback_iff_eqv pe R he hb).1 h)))

variable {n : Nat} (R : Fin n → τ) {X : τ} {L : LCtx τ} {e : Region Φ} {blocks : Fin n → Region Φ}

/-- A row label keeps its place. -/
theorem tagExits_local {i : Nat} (h : i < n) : (tagExits n i : Region Φ) = .br i (.var 0) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.tagExits_local n i h

/-- The exit written at position `j` goes to the single packed exit with
tag `j`. Two exits of one payload type keep different tags. -/
theorem tagExits_outward (n j : Nat) :
    (tagExits n (n + j) : Region Φ) = .br n (packedExitArg j (.var 0)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.tagExits_outward n j

/-- Tagging the exits of a table tags its entry and each row, under the
table's own labels. This is native `packExits` on the written table. -/
theorem packExits_cfg (e : Region Φ) (n : Nat) (blocks : Fin n → Region Φ) :
    (Region.cfg e n blocks).packExits =
      .cfg (e.lsubst (tagExits n)) n (fun i => (blocks i).lsubst (liftLSubstVars (tagExits n))) :=
  rfl

theorem tagExits_entry (he : ValueBranches [X] e (List.ofFn R ++ L)) :
    ValueBranches [X] (e.lsubst (tagExits n)) (List.ofFn R ++ [packedExitType L]) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.tagExits_entry R he

theorem tagExits_row (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L)) (i : Fin n) :
    ValueBranches [R i, X] ((blocks i).lsubst (liftLSubstVars (tagExits n)))
      (List.ofFn R ++ [packedExitType L]) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.tagExits_row R hb i

/-- A nonempty guarded table with any ordered exit list `L` equals the
packed readback of its exit-tagged form followed by the literal decoder
`unpackExits L`. The left endpoint is the written table at its written
exits. `L` may be empty and may repeat a payload type. -/
theorem retraction {n : Nat} (R : Fin (n + 1) → τ) {X : τ} {L : LCtx τ} {e : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ L))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L)) :
    Eqv pe [X] (.cfg e (n + 1) blocks)
      ((packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).val.lsubst
        (fun _ => unpackExits L)) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.retraction pe R he hb

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include pe shared in
/-- The written table and its decoded packed readback have one arrow in
every supported coherent model, at the written exits. -/
theorem denote_retraction {n : Nat} (R : Fin (n + 1) → τ) {X : τ} {L : LCtx τ} {e : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ L))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L)) :
    denoteRegion J M (ValueBranches.cfg R he hb).hasType =
      denoteRegion J M ((packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property.lsubst
        (unpackExits_valueFamily [X] L)).hasType :=
  (retraction pe R he hb).sound pe J M shared _ _

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
