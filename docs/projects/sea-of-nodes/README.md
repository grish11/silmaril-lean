# Sea of Nodes

Start with the [executable loop walkthrough](../sea-of-nodes-portable-loop.md#run-the-example)
to run one typed graph natively and after lowering to numbered θ and MLIR CF.
The [source-to-Lean coverage ledger](coverage.md) tracks Click’s work,
the Simple implementation, and the scope of the current Lean results.

## Pure producers

- [Pure-value Sea of Nodes](sea-of-nodes-pure.md)
- [Sea of Nodes pure producers to scalar MLIR](sea-of-nodes-mlir.md)

## Control flow and quads

- [Sea of Nodes diamond with arm-local producers](control-flow/sea-of-nodes-diamond-arms-lambdassa.md)
- [The Sea of Nodes diamond institution](control-flow/sea-of-nodes-diamond-institution.md)
- [Scheduled Sea of Nodes diamond to λSSA](control-flow/sea-of-nodes-diamond-lambdassa.md)
- [Signature change for scoped Sea of Nodes lowering](control-flow/sea-of-nodes-diamond-mlir-naturality.md)
- [Restricted scoped models for Sea of Nodes diamonds](control-flow/sea-of-nodes-diamond-mlir-restricted.md)
- [The pure Sea of Nodes diamond in scoped MLIR](control-flow/sea-of-nodes-diamond-mlir.md)
- [Trivial φ elimination for the pure Sea of Nodes diamond](control-flow/sea-of-nodes-diamond-phi-elim.md)
- [A Sea of Nodes word diamond in machine RTL](control-flow/sea-of-nodes-diamond-rtl.md)
- [The Sea of Nodes single-loop institution](control-flow/sea-of-nodes-loop-institution.md)
- [Generate λSSA for the pure single-loop profile](control-flow/sea-of-nodes-loop-lambdassa-generic.md)
- [Sea of Nodes counted swap in λSSA](control-flow/sea-of-nodes-loop-lambdassa.md)
- [Finite quad joins and acyclic composition](control-flow/sea-of-nodes-quad-finite-join.md)
- [A closed quad branch and join](control-flow/sea-of-nodes-quad-join.md)
- [A cyclic quad loop with typed header arguments](control-flow/sea-of-nodes-quad-loop.md)
- [Straight-line quads and use-def edges](control-flow/sea-of-nodes-quads.md)
- [Sea of Nodes diamond equations in the RVSDG room](../sea-of-nodes-diamond-rvsdg-institution.md)

## Memory

- [Checked Load forwarding in Sea of Nodes memory](memory/sea-of-nodes-load-forwarding.md)
- [Ordered RVSDG lowering of a Sea of Nodes memory diamond](memory/sea-of-nodes-memory-diamond-rvsdg.md)
- [Sea of Nodes memory diamond](memory/sea-of-nodes-memory-diamond.md)
- [Sea of Nodes tail-tested memory loop](memory/sea-of-nodes-memory-loop.md)
- [Ordered RVSDG lowering for Sea of Nodes memory](memory/sea-of-nodes-memory-rvsdg.md)
- [Sea of Nodes straight-line memory](memory/sea-of-nodes-memory.md)

## Placement and value numbering

- [Discovering a legal cut for one floating value](optimization/sea-of-nodes-gcm-discovery.md)
- [Checked placement for one Sea of Nodes floating node](optimization/sea-of-nodes-gcm-legality.md)
- [Exhaustive discovery of one Sea of Nodes representative](optimization/sea-of-nodes-gvn-discovery.md)
- [Removing one checked redundant Sea of Nodes producer](optimization/sea-of-nodes-gvn-elimination.md)
- [Bounded exact-key GVN for pure Sea of Nodes](optimization/sea-of-nodes-gvn-pass.md)
- [Checked structural representatives for pure Sea of Nodes](optimization/sea-of-nodes-gvn.md)

See also the [SSA guide](../ssa.md) and [RVSDG guides](../rvsdg/README.md).
