module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Demand.Defs

/-! # Conditions under which the inferred table is closed

Three checks on a φ graph, beside the existing scope check with its
arrival claims.

`claimed` is about the arrival claims. Every block has a claim, and no
claim of a block lists a register that the block itself defines, in a φ
row or anywhere in its body. The existing check does not ask for either:
a block that nothing jumps to may have no claim, or a claim that nothing
supplies.

`saturated` is about the rounds of demand. One more round changes the
demand of no block.

`ranked` is about a rank on labels. The rank of a block is below the
number of blocks, and a jump from a block to a block lowers the rank.
A ranked graph has no cycle through its blocks.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

universe v w

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- Every block has an arrival claim, and the claim lists no register
that the block defines. -/
def claimed (graph : Graph V K F) (certificate : GlobalSSA.Certificate V K) : Bool :=
  graph.blocks.all fun (key, source) =>
    (certificate.lookup key).any fun required =>
      required.all fun register =>
        !(source.rows.map Row.dst ++ GlobalSSA.bodyDefinitions source.body).contains register

/-- One more round of demand changes the demand of no block. -/
def saturated (graph : Graph V K F) (exits : List (Option K)) (inputs : List V) : Bool :=
  graph.blocks.all fun (key, _) =>
    decide (demand graph (OrderedExits.forScope graph exits) inputs (graph.blocks.length + 1) key =
      demand graph (OrderedExits.forScope graph exits) inputs graph.blocks.length key)

/-- The rank of a block is below the number of blocks, and a jump from a
block to a block lowers the rank. -/
def ranked (graph : Graph V K F) (rank : K → Nat) : Bool :=
  graph.blocks.all fun (key, source) =>
    decide (rank key < graph.blocks.length) && source.body.targets.all fun target =>
      target.elim true fun next =>
        (graph.blocks.lookup next).isNone || decide (rank next < rank key)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
