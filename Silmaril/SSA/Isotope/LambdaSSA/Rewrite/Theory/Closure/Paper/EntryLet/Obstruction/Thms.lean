module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.FlatPaper

/-! # Preservation and separation for the flat entry-let diagnostic -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction

open SequencingObstruction (Instruction)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

/-- Record one terminating outcome. A multi-label binder marks any effectful
segment followed by at least two local transfers within that binder.
The observed effect and mark bits propagate through all enclosing regions. -/
def observes (env : Semantics.Env Empty) (r : Region Instruction) (out : Observation) : Prop :=
  Sequencing.observesFlat env r out

/-- Every standard Paper equation preserves the full terminating observation
on exactly typed environments for the Unit-to-Unit instruction signature. -/
theorem observes_iff_of_eqv {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : Paper.Eqv Γ r s L) (env : Semantics.Env Empty)
    (he : Resumption.Typing.EnvTyped (fun (_ _ : Empty) => False) Γ env) (out : Observation) :
    observes env r out ↔ observes env s out :=
  Sequencing.observesFlat_eq_of_paper h env he out

/-- The diagnostic still distinguishes the two requests when both
discard a tagged input and return the same recurrent packet. -/
theorem discardedRecurringRequest_ne :
    let B := Silmaril.coprod U U
    let θ : Nat → Tm Instruction := Tm.singleSubst .unit ∘ Silmaril.DeBruijn.lift Nat.succ
    ¬ Paper.Eqv [B] (movedRecurringRequest.substVars θ) (flatRecurringRequest.substVars θ) [B] :=
  Sequencing.discardedRecurringRequest_ne

/-- The diagnostic still sees a mark when either request remains inside
its two-transfer table. -/
theorem unfinishedRequests_ne_bothMoved {r : Region Instruction}
    (hr : r = twoFlatRequests ∨ r = firstRequestMoved ∨ r = secondRequestMoved) :
    let B := Silmaril.coprod U U
    let θ : Nat → Tm Instruction := Tm.singleSubst .unit ∘ Silmaril.DeBruijn.lift Nat.succ
    ¬ Paper.Eqv [B] (r.substVars θ) (bothRequestsMoved.substVars θ) [B] :=
  Sequencing.unfinishedRequests_ne_bothMoved hr

/-- The asymmetric case observes different diagnostic marks on the two
tags. Every substituted region has the same observation on both inputs. -/
theorem oneMovedRequest_no_image (q : Region Instruction) :
    let B := Silmaril.coprod U U
    ¬ Paper.Eqv [B] (q.substVars discardInput) oneMovedRequest [B] :=
  Sequencing.oneMovedRequest_no_image q

theorem flatRequest_typed : ValueBranches [U] flatRequest [U] :=
  Sequencing.flatRequest_typed

theorem movedRequest_typed : ValueBranches [U] movedRequest [U] :=
  Sequencing.movedRequest_typed

theorem flatRequest_marked : observes unitEnv flatRequest (finish true) :=
  Sequencing.flatRequest_marked

theorem movedRequest_unmarked : observes unitEnv movedRequest (finish false) :=
  Sequencing.movedRequest_unmarked

theorem flatRequest_ne_moved : ¬ Paper.Eqv [U] flatRequest movedRequest [U] :=
  Sequencing.flatRequest_ne_moved

theorem flatRequest_arrow_ne_moved :
    Paper.TypeCategory.ofRegion flatRequest_typed ≠ Paper.TypeCategory.ofRegion movedRequest_typed :=
  fun h => flatRequest_ne_moved ((Paper.TypeCategory.ofRegion_eq_iff _ _).1 h)

/-- The arity-wide law already fails in a ranked two-label Unit table. -/
theorem entryLet_two_fails :
    ¬ CfgEta.EntryLet (Paper.Eqv (τ := Ty Empty) (Φ := Instruction)) 2 :=
  Sequencing.entryLet_two_fails

/-- Literal CFG η at arity two would imply the separated entry-let instance. -/
theorem entryEta_two_fails : ¬ Paper.EntryEta (Ty Empty) Instruction 2 :=
  fun h => entryLet_two_fails (Paper.entryLet_of_entryEta h)

/-- A unary entry-let move remains valid when its result reaches a multi-label table. -/
theorem unary_under_flat : Paper.Eqv [U] nestedRequest nestedMoved [U] :=
  Sequencing.unary_under_flat

/-- Both enclosing runs retain the effect before their two local transfers. -/
theorem unary_under_flat_marked :
    observes unitEnv nestedRequest (finish true) ∧ observes unitEnv nestedMoved (finish true) :=
  Sequencing.unary_under_flat_marked

end Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction
