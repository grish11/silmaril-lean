module

public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Silmaril.Logic.CTL.Thms
public import Silmaril.Logic.Institution.Examples.Equational
public import Silmaril.Logic.Institution.Examples.FirstOrder
public import Silmaril.Logic.Institution.Examples.Propositional
public import Silmaril.Logic.Institution.Examples.Unsorted
public import Silmaril.Logic.Institution.Grothendieck.Examples.Het
public import Silmaril.Logic.Institution.Metatheory.Consilience
public import Silmaril.Logic.Institution.Metatheory.HOL
public import Silmaril.Logic.Institution.Metatheory.Metamath
public import Silmaril.Logic.Matching.FirstOrder.Defs
public import Silmaril.Logic.Matching.FirstOrder.Pointed.Defs
public import Silmaril.Logic.Matching.FixedPoint.Thms
public import Silmaril.Logic.Modal.Thms
public import Silmaril.Logic.ModalMu.Thms
public import Silmaril.Logic.PDL.Thms
public import Silmaril.Logic.Reachability.Thms
public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Wasm.InstObs.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Logic`

Registrations of the institution and room declarations of the `Logic` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution inst.institution.of_obs := Silmaril.Inst.Institution.ofObs
silmaril institution logic.algebraic.many_sorted.inst := Silmaril.Logic.Algebraic.ManySorted.inst
silmaril institution logic.ctl.inst := Silmaril.Logic.CTL.inst
silmaril institution logic.institution.examples.eq.inst := Silmaril.Logic.Institution.Examples.EQ.inst (hets := "CASL") (hets_relation := fragment)
silmaril institution logic.institution.examples.fol.inst := Silmaril.Logic.Institution.Examples.FOL.inst (hets := "CASL") (hets_relation := fragment)
silmaril institution logic.institution.examples.pl.inst := Silmaril.Logic.Institution.Examples.PL.inst (hets := "Propositional") (hets_relation := corresponds)
silmaril institution logic.institution.examples.ufol.inst := Silmaril.Logic.Institution.Examples.UFOL.inst (hets := "CASL") (hets_relation := related)
silmaril institution logic.institution.het_inst := Silmaril.Logic.Institution.hetInst
silmaril institution logic.matching.first_order.pointed.inst := Silmaril.Logic.Matching.FirstOrder.Pointed.inst
silmaril institution logic.matching.first_order.inst := Silmaril.Logic.Matching.FirstOrder.inst
silmaril institution logic.matching.fixed_point.inst := Silmaril.Logic.Matching.FixedPoint.inst
silmaril institution logic.matching.fixed_point.pointed_inst := Silmaril.Logic.Matching.FixedPoint.pointedInst
silmaril institution logic.modal.inst := Silmaril.Logic.Modal.inst (hets := "Modal") (hets_relation := related)
silmaril institution logic.modal_mu.inst := Silmaril.Logic.ModalMu.inst
silmaril institution logic.pdl.inst := Silmaril.Logic.PDL.inst
silmaril institution logic.reachability.inst := Silmaril.Logic.Reachability.inst
silmaril room logic.institution.examples.eq.room := Silmaril.Logic.Institution.Examples.EQ.room
silmaril room logic.institution.examples.fol.room := Silmaril.Logic.Institution.Examples.FOL.room
silmaril room logic.institution.examples.pl.room := Silmaril.Logic.Institution.Examples.PL.room
silmaril room logic.institution.examples.ufol.room := Silmaril.Logic.Institution.Examples.UFOL.room
silmaril room logic.institution.metatheory.hol.room := Silmaril.Logic.Institution.Metatheory.HOL.room
silmaril room logic.institution.metatheory.hol_consilience.room := Silmaril.Logic.Institution.Metatheory.HOLConsilience.room
silmaril room logic.institution.metatheory.metamath.room := Silmaril.Logic.Institution.Metatheory.Metamath.room
