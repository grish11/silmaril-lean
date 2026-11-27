module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Demand.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.ForwardDemand
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.ForwardDemandEntry

/-! # The inferred forwarding table is a valid table

The inferred table passes the check of the normalization when the labels
of the blocks are distinct, which the normalization check of φ graphs
includes. The demand of a block leaves out the registers the block
defines, so no block receives a register that it defines. It also leaves
out the declared inputs, so a declared input is never forwarded.

So the normalized graph of the inferred table has the run of the original
graph, by the theorem of the normalization.

This validates the table. Whether a table keeps the entry is a separate
statement, about any table. `closed` is the existing check on the
normalized graph with every block arriving with the declared inputs
only, and `entryKept` says that the lowered and versioned entry reads no
register at its initial version except the declared inputs. A closed
table keeps the entry.

The reason is in the record of the versioning. The versioning carries on
every edge the registers that some body of the lowered graph reads
freely. When the routes of a block pass the scan from the declared
inputs, every read of the block is of an input, of a φ destination of
the block or of an earlier definition of the block. The lowered block
binds its φ destinations from the packet, so its free reads are the
packet and inputs. The entry is in scope over the inputs in the same
way. So the record holds declared inputs only, and the versioned entry,
which reads its own operands and the record, reads declared inputs at
their initial version. The statement is proved for any φ graph that the
existing check accepts with every block arriving with the given
registers only; the normalized graph is one such.

This is about the initial reads of the entry. It is not a statement
that the lowered graph elaborates or is typed at given captures, and it
does not say that the inferred table is closed.
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

/-- A φ graph that the existing check accepts when every block arrives
with the given registers only: the versioning of its lowering carries
records of those registers only, and its lowered and versioned entry
reads those registers only, at their initial version. -/
theorem lowered_entry {W : Type w} [DecidableEq W] (graph : Graph W K F)
    (exits : List (Option K)) (inputs : List W)
    (ok : OrderedExits.check graph exits inputs
      (graph.blocks.map fun (key, _) => (key, inputs)) = true) :
    (∀ label ys, Versioning.destinations (OrderedExits.lower graph) label = some ys →
        ∀ z ∈ ys, z ∈ inputs.map some) ∧
      ∀ name ∈ (Versioning.compile (OrderedExits.lower graph)).entry.toRegion.fvList,
        ∃ z ∈ inputs, name = (some z, 0) :=
  lowered_entry_proof graph exits inputs ok

/-- Under a closed table, every record that the versioning of the lowered
normalized graph carries holds declared inputs only. -/
theorem records_of_closed (graph : Graph V K F) (table : Table V K) (exits : List (Option K))
    (inputs : List V) (isClosed : closed graph table exits inputs = true) (label : Option K)
    (ys : List (Option (Name V K)))
    (found : Versioning.destinations (OrderedExits.lower (forward graph table)) label = some ys) :
    ∀ z ∈ ys, z ∈ inputs.map fun register => some (Sum.inl register) :=
  closed_records_proof graph table exits inputs isClosed label ys found

/-- A closed table keeps the entry: the lowered and versioned entry of
the normalized graph reads no register at its initial version except the
declared inputs. -/
theorem entryKept_of_closed (graph : Graph V K F) (table : Table V K) (exits : List (Option K))
    (inputs : List V) (isClosed : closed graph table exits inputs = true) :
    entryKept graph table inputs = true :=
  closed_keeps_entry_proof graph table exits inputs isClosed

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
