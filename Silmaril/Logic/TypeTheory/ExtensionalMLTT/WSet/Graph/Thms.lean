module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Graph.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.WSet.Graph

/-! # Membership and iota for graph-valued W construction and elimination

`node_mem` and `wrec_mem` prove the introduction and dependent elimination
membership obligations. `wrec_node` is the raw graph-model constructor equation.
These are the W-operation lemmas for extending the full object interpretation;
they do not themselves assert a soundness theorem for every object inference.
-/
