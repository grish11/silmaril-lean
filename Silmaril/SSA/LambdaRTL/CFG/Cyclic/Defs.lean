module

public import Silmaril.SSA.LambdaRTL.CFG.Defs
public import Silmaril.Semantics.Elgot.Defs

/-! # Cyclic lookup for named register-transfer CFGs

The block list is read as a table with first-match lookup. Every jump searches
the full table. A missing label exits, while a hit writes the block parameter
in the incoming store and executes the block's body. A transfer to the same
or an earlier block can therefore execute that block again.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic

open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- A jump in flight, or the result of exiting at an absent label. -/
abbrev Transfer (V K α : Type w) := K × α × (V → α)

variable [DecidableEq K]

/-- Each target of a block in the suffix has the same lookup in the full table
and in the remaining list after that block. -/
def ForwardTargets (table : List (K × Block V K F)) : List (K × Block V K F) → Prop
  | [] => True
  | (_, block) :: rest =>
      (∀ label ∈ block.body.targets, table.lookup label = rest.lookup label) ∧
        ForwardTargets table rest

/-- Suffix lookup is sound on all syntactic outgoing targets of named blocks.
The entry searches the full list in both execution modes. -/
def IsForward (graph : CFG V K F) : Prop :=
  ForwardTargets graph.blocks graph.blocks

variable [Monad M] [DecidableEq V]

/-- Resolve one transfer. A miss returns the result, and a hit executes one
body before emitting the next transfer. -/
def step (model : Model F M α) (table : List (K × Block V K F))
    (transfer : Transfer V K α) : M (Transfer V K α ⊕ Transfer V K α) :=
  match table.lookup transfer.1 with
  | none => pure (.inl transfer)
  | some block =>
      block.body.exec model (fun label value store => pure (.inr (label, value, store)))
        (upd transfer.2.2 block.param transfer.2.1)

/-- Execute the entry once, then iterate using the entire table at each jump. -/
def run [Iterate M] (model : Model F M α) (graph : CFG V K F) (store : V → α) :
    M (Transfer V K α) :=
  graph.entry.exec model (fun label value next => iter (step model graph.blocks) (label, value, next))
    store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic
