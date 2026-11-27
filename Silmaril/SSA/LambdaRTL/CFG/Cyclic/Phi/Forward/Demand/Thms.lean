module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Demand.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.ForwardDemand

/-! # The inferred forwarding table is a valid table

The inferred table passes the check of the normalization when the labels
of the blocks are distinct, which the normalization check of φ graphs
includes. The demand of a block leaves out the registers the block
defines, so no block receives a register that it defines. It also leaves
out the declared inputs, so a declared input is never forwarded.

So the normalized graph of the inferred table has the run of the original
graph, by the theorem of the normalization.

This validates the table. It does not say that the table is enough for
the lowered graph to keep the entry. That is a separate statement:
`closed` is the existing check on the normalized graph with every block
arriving with the declared inputs only, `entryKept` says that the lowered
and versioned entry reads no register at its initial version except the
declared inputs, and `Task.closedKeepsEntry` is the open statement that
the first gives the second. Both are decidable and are evaluated on the
graph at hand.
-/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL (Model)

universe v w

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

/-- The inferred table passes the check of the normalization when the
labels of the blocks are distinct. -/
theorem check_infer (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (distinct : (graph.blocks.map Prod.fst).Nodup) :
    check graph (infer graph exits inputs) = true :=
  check_infer_proof graph exits inputs distinct

/-- The inferred table passes the check of the normalization for a
normalized φ graph. -/
theorem check_infer_of_check (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (normalized : graph.check = true) : check graph (infer graph exits inputs) = true := by
  simp only [Graph.check, Bool.and_eq_true, decide_eq_true_eq] at normalized
  exact check_infer graph exits inputs normalized.1.1

/-- The inferred table never forwards a declared input. -/
theorem infer_input (graph : Graph V K F) (exits : List (Option K)) (inputs : List V) {key : K}
    {register : V} (received : register ∈ (infer graph exits inputs).received key) :
    register ∉ inputs :=
  infer_input_proof graph exits inputs received

/-- With the inferred table, the normalized graph runs like the original
graph on the original part of its input. -/
theorem run_infer [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M] (model : Model F M α)
    (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (distinct : (graph.blocks.map Prod.fst).Nodup) (input : Name V K → α) :
    OrderedExits.run model (forward graph (infer graph exits inputs)) input =
      OrderedExits.run model graph (input ∘ Sum.inl) :=
  run_forward model graph (infer graph exits inputs) (check_infer graph exits inputs distinct) input

/-- The entry is kept by a table under which every block is closed over
the declared inputs, given the open statement. -/
theorem entryKept_of (open_ : Task.closedKeepsEntry V K F) (graph : Graph V K F)
    (table : Table V K) (exits : List (Option K)) (inputs : List V)
    (isClosed : closed graph table exits inputs = true) : entryKept graph table inputs = true :=
  open_ graph table exits inputs isClosed

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
