module

public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.X86.BinInstitution.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.X86`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism x86.bin_institution.embed_co_hom := Silmaril.X86.BinInstitution.embedCoHom
