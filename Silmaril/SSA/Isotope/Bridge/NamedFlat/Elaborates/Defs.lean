module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs

/-! # Source checks for the named elaboration

The named elaboration can fail in three ways: an operand is outside its
fragment, a label is neither a block nor a declared exit, or a register
is read that the names in scope do not have. Three checks on the source
say that none of these happens.

`plain` says that every operand is a value or a primitive applied to a
value. Explicit injections and abort are outside the fragment of the
elaboration.

`resolves` says that every jump goes to a block or to a declared exit.

`entryNamed` says that every register that the versioned entry reads at
its initial version is one of the captures. It is a check on the output
of the versioning of the entry only. There is no such check for blocks.
-/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body)

universe v w

variable {V K : Type w} {F : Type v} {n : Nat}

/-- An operand of the fragment: a value, or a primitive applied to a
value. -/
def plainOp : Op V F → Bool
  | .val _ | .app _ _ => true
  | .inl _ | .inr _ | .abort _ => false

/-- A region whose operands are all in the fragment. -/
def plainRegion {L : Type w} : Region V L F → Bool
  | .br _ _ => true
  | .let1 _ operand rest => plainOp operand && plainRegion rest
  | .let2 _ _ operand rest => plainOp operand && plainRegion rest
  | .case operand _ left _ right => plainOp operand && plainRegion left && plainRegion right
  | .join body _ _ handler => plainRegion body && plainRegion handler

/-- A body whose operands are all in the fragment. -/
def plainBody (source : Body V K F) : Bool :=
  plainRegion source.toRegion

/-- Every operand of the graph is in the fragment. -/
def plain (graph : CFG V K F) : Bool :=
  plainBody graph.entry && graph.blocks.all fun item => plainBody item.2.body

variable [DecidableEq K]

/-- Every jump of the graph goes to a block or to a declared exit. -/
def resolves (graph : CFG V K F) (exits : List K) : Bool :=
  (graph.entry.targets ++ graph.blocks.flatMap fun item => item.2.body.targets).all fun label =>
    graph.blocks.any (fun item => label == item.1) || exits.contains label

variable [DecidableEq V]

/-- Every register that the versioned entry reads at its initial version
is one of the captures. -/
def entryNamed (graph : CFG V K F) (captures : Fin n → V) : Bool :=
  (CFG.Cyclic.Versioning.compile graph).entry.toRegion.fvList.all fun name =>
    (List.finRange n).any fun i => decide ((captures i, 0) = name)

namespace Phi

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)

omit [DecidableEq K] [DecidableEq V] in
/-- Every operand of the bodies of a φ graph is in the fragment. -/
def plain (graph : Graph V K F) : Bool :=
  plainBody graph.entry && graph.blocks.all fun item => plainBody item.2.body

end Phi

end Silmaril.Isotope.Bridge.NamedFlat
