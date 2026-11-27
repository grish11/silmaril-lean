module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Closure.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward.Demand.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.ForwardClosure

/-! # When the inferred table is closed

The existing scope check with arrival claims, together with a rank, is
not enough for the inferred table to be closed. The demand of a block
leaves out every register the block defines, wherever the definition is.
A block may read a register before it defines it, or on one path and
define it on another, when its arrival claim lists the register. The
existing check accepts that for a block that nothing jumps to, since no
edge has to supply the claim. The demand then misses the register, and
the normalized block reads a register it does not have.

Three conditions avoid this, and under them the inferred table is closed.

* The existing check accepts the graph with some arrival claims.
* `claimed`: every block has a claim, and it lists no register that the
  block defines. Then a register that a block needs from its arrival is
  never one that the demand leaves out.
* `saturated`: one more round changes no demand. Then what the table
  gives a block covers what the targets of the block are given.

A rank gives the third: `ranked` implies `saturated`, since the demand of
a block stops changing after as many rounds as its rank.

The proof is edge by edge. On a route of a block that passes the existing
check, what the route needs is within the arrival claim of the block,
counting what its target is given; by `claimed` it is not defined in the
block, so it is an input, a φ destination of the block or in its demand.
In the normalized graph the block has a copy of everything in its demand,
and the φ operands on each of its edges are the original operands and
what the target is given, as the block reads them. So every route of the
normalized graph passes the check from the inputs, the φ destinations and
the copies. The normalized graph is also a normalized φ graph with single
definitions.

With the theorem for closed tables, the lowered and versioned entry of
the normalized graph then reads the declared inputs only.

These are statements about scope. They are separate from the check of
the normalization and the preservation of the run, which hold for every
graph with distinct labels, and they do not say that the lowered graph
elaborates or is typed at given captures.
-/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

universe v w

variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- Collapsing the exits commutes with the normalization, when no declared
exit is a block. -/
theorem forScope_forward (graph : Graph V K F) (table : Table V K) (exits : List (Option K))
    (partition : OrderedExits.checkExits graph exits = true) :
    OrderedExits.forScope (forward graph table) exits =
      forward (OrderedExits.forScope graph exits) table :=
  forScope_forward_proof graph table exits partition

/-- The normalized graph passes the scope check with every block arriving
with the inputs only, when the graph passes the scope check with some
claims, no block receives a register twice, the entry needs inputs only,
and each block needs only inputs, its φ destinations and what it
receives. What a route needs counts what its target receives. This holds
for any table. -/
theorem check_forward_of_needs (graph : Graph V K F) (table : Table V K) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K)
    (ok : GlobalSSA.check graph inputs certificate = true)
    (distinct : ∀ key, (table.received key).Nodup)
    (entryNeeds : ∀ route ∈ GlobalSSA.bodyRoutes (GlobalSSA.edgeReads graph none) graph.entry,
      ∀ z ∈ needs (route.accesses ++ [.read (route.target.elim [] table.received)]), z ∈ inputs)
    (blockNeeds : ∀ item ∈ graph.blocks,
      ∀ route ∈ GlobalSSA.bodyRoutes (GlobalSSA.edgeReads graph (some item.1)) item.2.body,
      ∀ z ∈ needs (route.accesses ++ [.read (route.target.elim [] table.received)]),
        z ∈ inputs ∨ z ∈ item.2.rows.map Row.dst ∨ z ∈ table.received item.1) :
    GlobalSSA.check (forward graph table) (inputs.map Sum.inl)
      (graph.blocks.map fun item => (item.1, inputs.map Sum.inl)) = true :=
  check_closed_proof graph table inputs certificate ok distinct entryNeeds blockNeeds

/-- Every demand is within the arrival claim of its block. -/
theorem demand_claimed (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K)
    (scopeOk : GlobalSSA.check (OrderedExits.forScope graph exits) inputs certificate = true)
    (claims : claimed graph certificate = true) (rounds : Nat) (key : K) :
    ∀ z ∈ demand graph (OrderedExits.forScope graph exits) inputs rounds key,
      z ∈ (certificate.lookup key).getD [] :=
  demand_claimed_proof graph exits inputs certificate scopeOk claims rounds key

/-- A ranked graph is saturated. -/
theorem saturated_of_ranked (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (rank : K → Nat) (ok : ranked graph rank = true) : saturated graph exits inputs = true :=
  saturated_of_ranked_proof graph exits inputs rank ok

/-- The inferred table is closed, when the existing check accepts the
graph with some arrival claims, every block has a claim that lists no
register the block defines, and the demand is saturated. -/
theorem closed_infer (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K)
    (ok : OrderedExits.check graph exits inputs certificate = true)
    (claims : claimed graph certificate = true)
    (stable : saturated graph exits inputs = true) :
    closed graph (infer graph exits inputs) exits inputs = true :=
  closed_infer_proof graph exits inputs certificate ok claims stable

/-- The inferred table is closed for a ranked graph that the existing
check accepts with claims that list no register their block defines. -/
theorem closed_infer_of_ranked (graph : Graph V K F) (exits : List (Option K)) (inputs : List V)
    (certificate : GlobalSSA.Certificate V K) (rank : K → Nat)
    (ok : OrderedExits.check graph exits inputs certificate = true)
    (claims : claimed graph certificate = true) (acyclic : ranked graph rank = true) :
    closed graph (infer graph exits inputs) exits inputs = true :=
  closed_infer graph exits inputs certificate ok claims
    (saturated_of_ranked graph exits inputs rank acyclic)

/-- Under the same conditions the inferred table keeps the entry: the
lowered and versioned entry of the normalized graph reads no register at
its initial version except the declared inputs. -/
theorem entryKept_infer_of_ranked (graph : Graph V K F) (exits : List (Option K))
    (inputs : List V) (certificate : GlobalSSA.Certificate V K) (rank : K → Nat)
    (ok : OrderedExits.check graph exits inputs certificate = true)
    (claims : claimed graph certificate = true) (acyclic : ranked graph rank = true) :
    entryKept graph (infer graph exits inputs) inputs = true :=
  entryKept_of_closed graph (infer graph exits inputs) exits inputs
    (closed_infer_of_ranked graph exits inputs certificate rank ok claims acyclic)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
