module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Destructure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison

/-! # Strict inclusion of the two opt-in corrections

Every contextual derivation from typed entry-let is a once-bound η
derivation. At arities zero and one, standard Paper already proves the
once-bound equation with constructor-valued branches. At arbitrary arity,
unary lets and cases on constructor values admit re-entry. Moving a
computed product destructuring past the local table is a separate equation
and fails in the entry-let closure at arity two.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Comparison

open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Replay every entry-let seed via its η derivation and retain the same
typed contextual proof constructors. -/
theorem includes {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : WithEntryLet.Eqv Γ r s L) : WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.includes h

/-- A single constructor branch admits re-entry at any arity. The table
needs only exact typing for this β calculation. -/
theorem reentry_branch {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (hi : At (List.ofFn R ++ L) i A) (ha : Tm.BranchValue Γ a A)
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    Paper.Eqv Γ (.cfg (.br i a) n blocks)
      ((Region.br i a).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.reentry_branch R hi ha hb

/-- Unary let sequencing and the native case-value conversion admit re-entry
for this grammar over arbitrary guarded local rows. -/
theorem reentry_sequenced {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (hr : SequencedEntry Γ r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithEntryLet.Eqv Γ (.cfg r n blocks) (r.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.reentry_sequenced R hr hb

/-- Any guarded entry admits once-bound re-entry with zero or one local label. -/
theorem reentry_guarded_le_one {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {blocks : Fin n → Region Φ} (hn : n ≤ 1) (R : Fin n → τ)
    (hr : ValueBranches Γ r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    Paper.Eqv Γ (.cfg r n blocks) (r.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.reentry_guarded_le_one hn R hr hb

/-- Once-bound η derives product entry sequencing at arbitrary arity with
exact typing for the body and rows. -/
theorem entryLet₂ {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A B : τ}
    {r : Region Φ} {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.product A B))
    (hr : HasType (B :: A :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.let₂ a r) n blocks)
      (.let₂ a (.cfg r n (fun j => ((blocks j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.entryLet₂ R ha hr hb

/-- Once the body admits re-entry, the outstanding equation for a product
binder is exactly moving it past the CFG and weakening the old table by
both new captures. -/
theorem reentry_let₂_iff_move {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A B : τ}
    {r : Region Φ} {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.product A B))
    (hr : SequencedEntry (B :: A :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithEntryLet.Eqv Γ (.cfg (.let₂ a r) n blocks)
      ((Region.let₂ a r).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L ↔
    WithEntryLet.Eqv Γ (.cfg (.let₂ a r) n blocks)
      (.let₂ a (.cfg r n (fun j => ((blocks j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.reentry_let₂_iff_move R ha hr hb

namespace DestructureFixture

open Paper.EntryLetObstruction.Destructure

theorem rows_typed {Γ : VCtx (Ty Empty)} (j : Fin 2) :
    ValueBranches (labels j :: Γ) (rows j) (List.ofFn labels ++ [U]) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.DestructureFixture.rows_typed j

theorem entry_typed : ValueBranches [] entry (List.ofFn labels ++ [U]) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.DestructureFixture.entry_typed

theorem guards : ValueBranches [] original [U] ∧ ValueBranches [] reentered [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.DestructureFixture.guards

/-- The same exactly typed endpoints separate the contextual relations,
with only constructor-valued branch arguments in the entry and table. -/
theorem strict : WithBoundEntryEta.Eqv [] original reentered [U] ∧
    ¬ WithEntryLet.Eqv [] original reentered [U] :=
  ⟨Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.DestructureFixture.reentry_eq,
    reentry_ne⟩

/-- Moving the product binder across the two local labels is underivable. -/
theorem move_ne :
    ¬ WithEntryLet.Eqv [] original
      (.let₂ initializer (.cfg (.br 0 (.var 1)) 2
        (fun j => ((rows j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)))) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.DestructureFixture.move_ne

/-- A pure sum selects a Unit or Unit × Unit label. The Unit arm makes a
call in a unary initializer, and entry-let derives the re-entry equation. -/
theorem selected_reentry_eq :
    WithEntryLet.Eqv [Silmaril.coprod U P] (.cfg sumEntry 2 rows)
      (sumEntry.bindBranchArguments.lsubst (cfgEntryContinuations rows)) [U] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison.DestructureFixture.selected_reentry_eq

end DestructureFixture

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Comparison
