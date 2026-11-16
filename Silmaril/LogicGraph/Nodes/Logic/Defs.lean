module

public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Silmaril.Logic.CTL.Thms
public import Silmaril.Logic.CommonLogic.Core.Defs
public import Silmaril.Logic.CommonLogic.FiniteListFOL.Defs
public import Silmaril.Logic.CommonLogic.FiniteListFOL.Thms
public import Silmaril.Logic.CommonLogic.FirstOrder.Defs
public import Silmaril.Logic.CommonLogic.ManySorted.Expansion.Thms
public import Silmaril.Logic.CommonLogic.ManySorted.Institution.Defs
public import Silmaril.Logic.CommonLogic.ManySorted.Institution.Thms
public import Silmaril.Logic.CommonLogic.Source.CLIF.Thms
public import Silmaril.Logic.CommonLogic.Source.Defs
public import Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.Defs
public import Silmaril.Logic.CommonLogic.Source.Presentations.Family.Defs
public import Silmaril.Logic.CommonLogic.Source.Presentations.Packaged.Defs
public import Silmaril.Logic.Egg.Core.Defs
public import Silmaril.Logic.Egg.Source.Named.Family.Defs
public import Silmaril.Logic.Egg.Source.Named.Supplied.Institution.Defs
public import Silmaril.Logic.Egglog.Core.Defs
public import Silmaril.Logic.Egglog.Core.FirstOrder
public import Silmaril.Logic.Egglog.Core.Graph.Defs
public import Silmaril.Logic.Egglog.Source.Named.Family.Defs
public import Silmaril.Logic.FirstOrder.FiniteLists.Defs
public import Silmaril.Logic.FirstOrder.FiniteLists.Thms
public import Silmaril.Logic.FirstOrderLFP.Boolean.Thms
public import Silmaril.Logic.FirstOrderLFP.Thms
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
public import Silmaril.Logic.Prolog.Definite.Defs
public import Silmaril.Logic.Reachability.Thms
public import Silmaril.Logic.Temporal.CTLStar.Thms
public import Silmaril.Logic.Temporal.LTL.Defs
public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Wasm.InstObs.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Logic`

Registrations of the institution and room declarations of the `Logic` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution inst.institution.of_obs := Silmaril.Inst.Institution.ofObs
silmaril institution logic.algebraic.many_sorted.inst := Silmaril.Logic.Algebraic.ManySorted.inst
silmaril institution logic.ctl.inst := Silmaril.Logic.CTL.inst
silmaril institution logic.common_logic.core.inst := Silmaril.Logic.CommonLogic.Core.inst (hets := "CommonLogic") (hets_relation := related)
silmaril institution logic.common_logic.finite_list_fol.inst := Silmaril.Logic.CommonLogic.FiniteListFOL.inst
silmaril institution logic.common_logic.first_order.inst := Silmaril.Logic.CommonLogic.FirstOrder.inst
silmaril institution logic.common_logic.first_order.nonempty_inst := Silmaril.Logic.CommonLogic.FirstOrder.nonemptyInst
silmaril institution logic.common_logic.many_sorted.institution.inst := Silmaril.Logic.CommonLogic.ManySorted.Institution.inst
silmaril institution logic.common_logic.source.presentations.dynamic.core_inst := Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.coreInst
silmaril institution logic.common_logic.source.presentations.dynamic.fol_inst := Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.folInst
silmaril institution logic.common_logic.source.presentations.dynamic.inst := Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.inst
silmaril institution logic.common_logic.source.presentations.family.inst := Silmaril.Logic.CommonLogic.Source.Presentations.Family.inst
silmaril institution logic.common_logic.source.presentations.packaged.inst := Silmaril.Logic.CommonLogic.Source.Presentations.Packaged.inst
silmaril institution logic.egg.core.inst := Silmaril.Logic.Egg.Core.inst
silmaril institution logic.egg.source.named.families.inst := Silmaril.Logic.Egg.Source.Named.Families.inst
silmaril institution logic.egg.source.named.supplied.direct.inst := Silmaril.Logic.Egg.Source.Named.Supplied.Direct.inst
silmaril institution logic.egglog.core.graph.inst := Silmaril.Logic.Egglog.Core.Graph.inst
silmaril institution logic.egglog.core.inst := Silmaril.Logic.Egglog.Core.inst
silmaril institution logic.egglog.source.named.families.inst := Silmaril.Logic.Egglog.Source.Named.Families.inst
silmaril institution logic.first_order.finite_lists.inst := Silmaril.Logic.FirstOrder.FiniteLists.inst
silmaril institution logic.first_order_lfp.boolean.inst := Silmaril.Logic.FirstOrderLFP.Boolean.inst
silmaril institution logic.first_order_lfp.inst := Silmaril.Logic.FirstOrderLFP.inst
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
silmaril institution logic.prolog.definite.inst := Silmaril.Logic.Prolog.Definite.inst
silmaril institution logic.reachability.inst := Silmaril.Logic.Reachability.inst
silmaril institution logic.temporal.ctl_star.inst := Silmaril.Logic.Temporal.CTLStar.inst
silmaril institution logic.temporal.ctl_star.rich_inst := Silmaril.Logic.Temporal.CTLStar.richInst
silmaril institution logic.temporal.ltl.inst := Silmaril.Logic.Temporal.LTL.inst
silmaril room logic.common_logic.core.room := Silmaril.Logic.CommonLogic.Core.room
silmaril room logic.common_logic.finite_list_fol.room := Silmaril.Logic.CommonLogic.FiniteListFOL.room
silmaril room logic.common_logic.first_order.nonempty_room := Silmaril.Logic.CommonLogic.FirstOrder.nonemptyRoom
silmaril room logic.common_logic.many_sorted.expansion.typed_room := Silmaril.Logic.CommonLogic.ManySorted.Expansion.typedRoom
silmaril room logic.common_logic.many_sorted.institution.room := Silmaril.Logic.CommonLogic.ManySorted.Institution.room
silmaril room logic.common_logic.source.clif.room := Silmaril.Logic.CommonLogic.Source.CLIF.room
silmaril room logic.common_logic.source.presentations.dynamic.room := Silmaril.Logic.CommonLogic.Source.Presentations.Dynamic.room
silmaril room logic.common_logic.source.presentations.packaged.room := Silmaril.Logic.CommonLogic.Source.Presentations.Packaged.room
silmaril room logic.common_logic.source.room := Silmaril.Logic.CommonLogic.Source.room
silmaril room logic.egg.core.room := Silmaril.Logic.Egg.Core.room
silmaril room logic.egg.source.named.families.room := Silmaril.Logic.Egg.Source.Named.Families.room
silmaril room logic.egg.source.named.supplied.direct.room := Silmaril.Logic.Egg.Source.Named.Supplied.Direct.room
silmaril room logic.egglog.core.graph.room := Silmaril.Logic.Egglog.Core.Graph.room
silmaril room logic.egglog.core.room := Silmaril.Logic.Egglog.Core.room
silmaril room logic.egglog.source.named.families.room := Silmaril.Logic.Egglog.Source.Named.Families.room
silmaril room logic.first_order.finite_lists.room := Silmaril.Logic.FirstOrder.FiniteLists.room
silmaril room logic.institution.examples.eq.room := Silmaril.Logic.Institution.Examples.EQ.room
silmaril room logic.institution.examples.fol.room := Silmaril.Logic.Institution.Examples.FOL.room
silmaril room logic.institution.examples.pl.room := Silmaril.Logic.Institution.Examples.PL.room
silmaril room logic.institution.examples.ufol.room := Silmaril.Logic.Institution.Examples.UFOL.room
silmaril room logic.institution.metatheory.hol.room := Silmaril.Logic.Institution.Metatheory.HOL.room
silmaril room logic.institution.metatheory.hol_consilience.room := Silmaril.Logic.Institution.Metatheory.HOLConsilience.room
silmaril room logic.institution.metatheory.metamath.room := Silmaril.Logic.Institution.Metatheory.Metamath.room
silmaril room logic.prolog.definite.room := Silmaril.Logic.Prolog.Definite.room
silmaril room logic.temporal.ltl.room := Silmaril.Logic.Temporal.LTL.room
