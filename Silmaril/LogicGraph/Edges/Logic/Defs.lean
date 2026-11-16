module

public import Silmaril.Logic.Institution.Examples.Comorphisms
public import Silmaril.Logic.Institution.Hets.Examples
public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.Wasm.InstObs.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Logic`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism inst.comorphism.of_obs := Silmaril.Inst.Comorphism.ofObs (facts := [Silmaril.Inst.Comorphism.ofObs_modelExpansive])
silmaril comorphism logic.institution.examples.eq_to_fol := Silmaril.Logic.Institution.Examples.eqToFol (facts := [Silmaril.Logic.Institution.Examples.eqToFol_modelExpansive])
silmaril comorphism logic.institution.examples.pl_to_fol := Silmaril.Logic.Institution.Examples.plToFol (hets := "Prop2CASL") (hets_relation := related) (facts := [Silmaril.Logic.Institution.Examples.plToFol_modelExpansive])
silmaril morphism inst.morphism.of_obs := Silmaril.Inst.Morphism.ofObs (facts := [Silmaril.Inst.Morphism.ofObs_sound])
silmaril morphism logic.institution.examples.fol_to_eq := Silmaril.Logic.Institution.Examples.folToEq (facts := [Silmaril.Logic.Institution.Examples.folToEq_sound])
