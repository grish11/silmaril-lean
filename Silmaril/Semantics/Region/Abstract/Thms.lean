module

public import Silmaril.Semantics.Region.Abstract.Defs
import Silmaril.Proofs.Semantics.Region.Lattice

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract
universe u v
variable {Atom : Type u} {rules : Rules Atom}

/-- Raw fixed-signature models are the powerset/product complete lattice. -/
example (S : Signature.{u, v}) : CompleteLattice S.Model := inferInstance

theorem closed_top : Closed rules (⊤ : RawModel Atom) := fun _ _ _ => trivial

theorem closed_sInf (models : Set (RawModel Atom)) (h : ∀ M ∈ models, Closed rules M) :
    Closed rules (sInf models) := Proofs.closed_sInf models h

theorem subset_closure (M : RawModel Atom) : M ⊆ closure rules M :=
  fun _ ha _ _ subset => subset ha

theorem closure_closed (M : RawModel Atom) : Closed rules (closure rules M) := Proofs.closure_closed M

theorem closure_le {M N : RawModel Atom} (closed : Closed rules N) (subset : M ⊆ N) :
    closure rules M ⊆ N := Proofs.closure_le closed subset

theorem closure_mono {M N : RawModel Atom} (subset : M ⊆ N) : closure rules M ⊆ closure rules N :=
  closure_le (closure_closed N) (subset.trans (subset_closure N))

theorem closure_idempotent (M : RawModel Atom) : closure rules (closure rules M) = closure rules M :=
  Proofs.closure_idempotent M

/-- The closed predicate is definitionally the positive-rule property. -/
def closureOperator (rules : Rules Atom) : ClosureOperator (RawModel Atom) where
  toFun := closure rules
  monotone' := fun _ _ h => closure_mono h
  le_closure' := subset_closure
  idempotent' := closure_idempotent
  IsClosed := Closed rules
  isClosed_iff := ⟨fun h => Set.Subset.antisymm (closure_le h Set.Subset.rfl) (subset_closure _),
    fun h => h ▸ closure_closed _⟩

/-- Meets are intersections; joins are closure of unions. No assumptions on
rule arity, finite enumerability, or the atom carrier. -/
instance : CompleteLattice (ClosedModel rules) := (closureOperator rules).gi.liftCompleteLattice

theorem closedModel_le_iff (M N : ClosedModel rules) : M ≤ N ↔ M.val ⊆ N.val := Iff.rfl

theorem val_sInf (models : Set (ClosedModel rules)) :
    (sInf models).val = sInf (Subtype.val '' models) := rfl

theorem val_sSup (models : Set (ClosedModel rules)) :
    (sSup models).val = closure rules (sSup (Subtype.val '' models)) := rfl

theorem val_inf (M N : ClosedModel rules) : (M ⊓ N).val = M.val ∩ N.val := rfl

theorem val_sup (M N : ClosedModel rules) : (M ⊔ N).val = closure rules (M.val ∪ N.val) := rfl

theorem val_bot : (⊥ : ClosedModel rules).val = closure rules ∅ := rfl

theorem val_top : (⊤ : ClosedModel rules).val = Set.univ := rfl

/-- All submodels below a fixed lawful ceiling also form a complete lattice.
This interval's empty meet is the ceiling, rather than the full atom set. -/
instance (ceiling : ClosedModel rules) : CompleteLattice (Below ceiling) := Set.Iic.instCompleteLattice

theorem below_top (ceiling : ClosedModel rules) : (⊤ : Below ceiling).val = ceiling := rfl

/-- Joins stay below the ceiling, including the empty join. -/
theorem below_sSup (ceiling : ClosedModel rules) (models : Set (Below ceiling)) :
    (sSup models).val = sSup (Subtype.val '' models) := rfl

/-- The ceiling is intersected in, so this includes the empty meet. -/
theorem below_sInf (ceiling : ClosedModel rules) (models : Set (Below ceiling)) :
    (sInf models).val = ceiling ⊓ sInf (Subtype.val '' models) := rfl

theorem below_bot (ceiling : ClosedModel rules) :
    (⊥ : Below ceiling).val.val = closure rules ∅ := rfl

theorem closure_below {M : RawModel Atom} (ceiling : ClosedModel rules) (h : M ⊆ ceiling.val) :
    closure rules M ⊆ ceiling.val := closure_le ceiling.property h

theorem reindex_closed {Other : Type v} {f : Atom → Other} {target : Rules Other}
    (transport : RuleMap f rules target) {M : RawModel Other} (closed : Closed target M) :
    Closed rules (reindex f M) := Proofs.reindex_closed transport closed

/-- Lawful reduct commutes with intersections; no corresponding lawful-join
claim follows from rule transport alone. -/
theorem reindex_sInf_closed {Other : Type v} {f : Atom → Other} {target : Rules Other}
    (transport : RuleMap f rules target) (models : Set (RawModel Other))
    (h : ∀ M ∈ models, Closed target M) : Closed rules (reindex f (sInf models)) :=
  reindex_closed transport (closed_sInf models h)

/-- Closing a reduct can only add judgments allowed by the reduct of target
closure. Equality needs stronger hypotheses. -/
theorem closure_reindex_le {Other : Type v} {f : Atom → Other} {target : Rules Other}
    (transport : RuleMap f rules target) (M : RawModel Other) :
    closure rules (reindex f M) ⊆ reindex f (closure target M) :=
  closure_le (reindex_closed transport (closure_closed M)) (fun _ h => subset_closure M h)

theorem forget_sSup {Other : Type v} (f : Atom → Other) (models : Set (RawModel Atom)) :
    forget f (sSup models) = sSup (forget f '' models) := Proofs.forget_sSup f models

theorem reindex_sInf {Other : Type v} (f : Atom → Other) (models : Set (RawModel Other)) :
    reindex f (sInf models) = sInf (reindex f '' models) := Proofs.reindex_sInf f models

theorem reindex_sSup {Other : Type v} (f : Atom → Other) (models : Set (RawModel Other)) :
    reindex f (sSup models) = sSup (reindex f '' models) := Proofs.reindex_sSup f models

end Silmaril.Semantics.Region.Abstract
