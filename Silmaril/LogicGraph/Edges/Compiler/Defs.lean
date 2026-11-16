module

public import Silmaril.Compiler.Category.Cerberus.Defs
public import Silmaril.Compiler.Native.Correctness.Institution.Defs
public import Silmaril.LogicGraph.Nodes.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Compiler`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism compiler.category.cerberus.realization := Silmaril.Compiler.Category.Cerberus.realization
silmaril comorphism compiler.native.correctness.institution.native := Silmaril.Compiler.Native.Correctness.Institution.native
silmaril comorphism compiler.native.correctness.institution.projection := Silmaril.Compiler.Native.Correctness.Institution.projection
