module

public import Silmaril.SSA.SeaOfNodes.GVN.Pass.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Pass

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open RVSDG (Locals Origin Tuple)
open Elimination (Rewrite Routing operandScope)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {flow : Dataflow Op args past sigs}

/-- The table-order enumeration contains every typed producer reference. -/
theorem mem_candidates {out : ValueSort Data} (ref : Producer flow out) :
    ⟨out, ref⟩ ∈ candidates flow :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.mem_candidates ref

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- One candidate uses the discovered earlier producer and its typed prefix wire. -/
theorem eliminateCandidate?_checked {out : ValueSort Data} (candidate : Producer flow out) {result : Rewrite Op args past sigs}
    (accepted : eliminateCandidate? candidate = some result) :
    ∃ (representative : Producer flow out) (wire : Origin args (operandScope candidate) (.value out)),
      Discovery.findRepresentative? candidate = some representative ∧
        replacement? candidate representative = some wire ∧
        Elimination.eliminate? candidate representative wire = some result :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.eliminateCandidate_checked candidate accepted

/-- Any discovered representative has a usable prefix wire. -/
theorem eliminateCandidate?_eq_none_iff {out : ValueSort Data} (candidate : Producer flow out) :
    eliminateCandidate? candidate = none ↔ Discovery.findRepresentative? candidate = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.eliminateCandidate_none_iff candidate

/-- A scan stops exactly when the current table has no checker-accepted pair. -/
theorem step?_eq_none_iff (flow : Dataflow Op args past sigs) :
    step? flow = none ↔ NoDuplicate flow :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.step_none_iff flow

/-- A successful step removes one binding. -/
theorem step_size {result : Rewrite Op args past sigs} (accepted : step? flow = some result) :
    result.sigs'.length + 1 = sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.step_size accepted

/-- A single deletion preserves the value of each original routed wire. -/
theorem step_sound {result : Rewrite Op args past sigs} (accepted : step? flow = some result)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.step_sound m entry locals accepted

/-- Every original wire keeps its value under the composed routing, for any
assignment to arguments and the initial scope in a pure total model. -/
theorem run_sound (fuel : Nat) (flow : Dataflow Op args past sigs)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    let result := run fuel flow
    Routing.Agrees result.rewrite.route m entry (flow.eval m entry locals)
      (result.rewrite.flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.run_sound m entry locals fuel flow

/-- The deletion count is exact and bounded by fuel. -/
theorem run_progress (fuel : Nat) (flow : Dataflow Op args past sigs) :
    let result := run fuel flow
    result.rewrite.sigs'.length + result.deletions = sigs.length ∧ result.deletions ≤ fuel :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.run_progress fuel flow

/-- If fuel remains, recomputing keys in the resulting table finds no duplicate. -/
theorem run_normal_of_remaining (fuel : Nat) (flow : Dataflow Op args past sigs)
    (remaining : (run fuel flow).deletions < fuel) :
    NoDuplicate (run fuel flow).rewrite.flow :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.run_normal_of_remaining fuel flow remaining

/-- The default fuel suffices to reach the exact-key normal form. -/
theorem normalize_normal (flow : Dataflow Op args past sigs) :
    NoDuplicate (normalize flow).rewrite.flow :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.normalize_normal flow

end Silmaril.SSA.SeaOfNodes.GVN.Pass
