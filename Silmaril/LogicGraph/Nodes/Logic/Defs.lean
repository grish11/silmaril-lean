module

public import Silmaril.Logic.Algebraic.DependentFamily.Defs
public import Silmaril.Logic.Algebraic.Initial.Defs
public import Silmaril.Logic.Algebraic.Initial.Matching.FiniteSorted.Institution.Defs
public import Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.Defs
public import Silmaril.Logic.Algebraic.Initial.Thms
public import Silmaril.Logic.Algebraic.Lambda.Institution
public import Silmaril.Logic.Algebraic.ManySorted.Horn
public import Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Institution
public import Silmaril.Logic.Algebraic.ManySorted.Varying.Defs
public import Silmaril.Logic.Algebraic.OrderSorted
public import Silmaril.Logic.Algebraic.OrderSorted.Defs
public import Silmaril.Logic.Algebraic.OrderSorted.Examples
public import Silmaril.Logic.Algebraic.OrderSorted.Free
public import Silmaril.Logic.Algebraic.OrderSorted.Free.Defs
public import Silmaril.Logic.Algebraic.OrderSorted.Free.Thms
public import Silmaril.Logic.Algebraic.OrderSorted.Initial
public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Audits
public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Defs
public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples
public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Thms
public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Audits
public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Defs
public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Examples
public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Models
public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Thms
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Audits
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Defs
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Examples
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Audits
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Defs
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Examples
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Institution.Thms
public import Silmaril.Logic.Algebraic.OrderSorted.Representation.Thms
public import Silmaril.Logic.Algebraic.OrderSorted.Thms
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
public import Silmaril.Logic.Matching.GeneralFixedPoint.Institution
public import Silmaril.Logic.Matching.GuardedFOL.FixedPoint.Defs
public import Silmaril.Logic.Matching.GuardedFOL.Thms
public import Silmaril.Logic.Matching.GuardedLFP.Institution
public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Institution
public import Silmaril.Logic.Matching.SortMaps.Thms
public import Silmaril.Logic.Modal.Thms
public import Silmaril.Logic.ModalMu.Thms
public import Silmaril.Logic.PDL.Thms
public import Silmaril.Logic.Prolog.Definite.Defs
public import Silmaril.Logic.Reachability.Thms
public import Silmaril.Logic.STLCEquations.Institution
public import Silmaril.Logic.STLCMatching.Institution
public import Silmaril.Logic.Temporal.CTLStar.Thms
public import Silmaril.Logic.Temporal.LTL.Defs
public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Wasm.InstObs.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Logic`

Registrations of the institution and room declarations of the `Logic` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution inst.institution.of_obs := Silmaril.Inst.Institution.ofObs
silmaril institution logic.algebraic.initial.equational_inst := Silmaril.Logic.Algebraic.Initial.equationalInst
silmaril institution logic.algebraic.initial.inst := Silmaril.Logic.Algebraic.Initial.inst
silmaril institution logic.algebraic.lambda.equational_inst := Silmaril.Logic.Algebraic.Lambda.equationalInst
silmaril institution logic.algebraic.lambda.lambda_inst := Silmaril.Logic.Algebraic.Lambda.lambdaInst
silmaril institution logic.algebraic.many_sorted.public_eq.many_sorted_inst := Silmaril.Logic.Algebraic.ManySorted.PublicEQ.manySortedInst
silmaril institution logic.algebraic.many_sorted.public_eq.public_inst := Silmaril.Logic.Algebraic.ManySorted.PublicEQ.publicInst
silmaril institution logic.algebraic.many_sorted.varying.inst := Silmaril.Logic.Algebraic.ManySorted.Varying.inst
silmaril institution logic.algebraic.many_sorted.horn_inst := Silmaril.Logic.Algebraic.ManySorted.hornInst
silmaril institution logic.algebraic.order_sorted.initial.inst := Silmaril.Logic.Algebraic.OrderSorted.Initial.inst
silmaril institution logic.algebraic.order_sorted.initial.ordered_inst := Silmaril.Logic.Algebraic.OrderSorted.Initial.orderedInst
silmaril institution logic.algebraic.order_sorted.representation.literal_inst := Silmaril.Logic.Algebraic.OrderSorted.Representation.literalInst
silmaril institution logic.algebraic.order_sorted.inst := Silmaril.Logic.Algebraic.OrderSorted.inst
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
silmaril institution logic.institution.examples.eq.inst := Silmaril.Logic.Institution.Examples.EQ.inst (hets := "CASL") (hets_relation := fragment)
silmaril institution logic.institution.examples.fol.inst := Silmaril.Logic.Institution.Examples.FOL.inst (hets := "CASL") (hets_relation := fragment)
silmaril institution logic.institution.examples.pl.inst := Silmaril.Logic.Institution.Examples.PL.inst (hets := "Propositional") (hets_relation := corresponds)
silmaril institution logic.institution.examples.ufol.inst := Silmaril.Logic.Institution.Examples.UFOL.inst (hets := "CASL") (hets_relation := related)
silmaril institution logic.institution.het_inst := Silmaril.Logic.Institution.hetInst
silmaril institution logic.matching.guarded_fol.fixed_inst := Silmaril.Logic.Matching.GuardedFOL.fixedInst
silmaril institution logic.matching.guarded_fol.inst := Silmaril.Logic.Matching.GuardedFOL.inst
silmaril institution logic.matching.guarded_lfp.inst := Silmaril.Logic.Matching.GuardedLFP.inst
silmaril institution logic.matching.sort_maps.fixed_inst := Silmaril.Logic.Matching.SortMaps.fixedInst
silmaril institution logic.prolog.definite.inst := Silmaril.Logic.Prolog.Definite.inst
silmaril institution logic.stlc_equations.inst := Silmaril.Logic.STLCEquations.inst
silmaril institution logic.stlc_matching.source_inst := Silmaril.Logic.STLCMatching.sourceInst
silmaril institution logic.stlc_matching.target_inst := Silmaril.Logic.STLCMatching.targetInst
silmaril institution logic.temporal.ltl.inst := Silmaril.Logic.Temporal.LTL.inst
silmaril institution logic.algebraic.dependent_family.inst := Silmaril.Logic.Algebraic.DependentFamily.inst
silmaril institution logic.ctl.inst := Silmaril.Logic.CTL.inst
silmaril institution logic.first_order_lfp.boolean.inst := Silmaril.Logic.FirstOrderLFP.Boolean.inst
silmaril institution logic.first_order_lfp.inst := Silmaril.Logic.FirstOrderLFP.inst
silmaril institution logic.matching.first_order.pointed.inst := Silmaril.Logic.Matching.FirstOrder.Pointed.inst
silmaril institution logic.matching.first_order.inst := Silmaril.Logic.Matching.FirstOrder.inst
silmaril institution logic.matching.fixed_point.inst := Silmaril.Logic.Matching.FixedPoint.inst
silmaril institution logic.matching.fixed_point.pointed_inst := Silmaril.Logic.Matching.FixedPoint.pointedInst
silmaril institution logic.matching.general_fixed_point.inst := Silmaril.Logic.Matching.GeneralFixedPoint.inst
silmaril institution logic.matching.sort_maps.general_inst := Silmaril.Logic.Matching.SortMaps.generalInst
silmaril institution logic.matching.sort_maps.inst := Silmaril.Logic.Matching.SortMaps.inst
silmaril institution logic.modal.inst := Silmaril.Logic.Modal.inst (hets := "Modal") (hets_relation := related)
silmaril institution logic.modal_mu.inst := Silmaril.Logic.ModalMu.inst
silmaril institution logic.pdl.inst := Silmaril.Logic.PDL.inst
silmaril institution logic.reachability.inst := Silmaril.Logic.Reachability.inst
silmaril institution logic.temporal.ctl_star.inst := Silmaril.Logic.Temporal.CTLStar.inst
silmaril institution logic.temporal.ctl_star.rich_inst := Silmaril.Logic.Temporal.CTLStar.richInst
silmaril room logic.algebraic.initial.matching.finite_sorted_compiler.institution.source_room := Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.sourceRoom
silmaril room logic.algebraic.initial.matching.finite_sorted_compiler.institution.theory_room := Silmaril.Logic.Algebraic.Initial.Matching.FiniteSortedCompiler.Institution.theoryRoom
silmaril room logic.algebraic.initial.matching.global_presented.native_room := Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.nativeRoom
silmaril room logic.algebraic.initial.matching.global_presented.source_room := Silmaril.Logic.Algebraic.Initial.Matching.GlobalPresented.sourceRoom
silmaril room logic.algebraic.initial.equational_room := Silmaril.Logic.Algebraic.Initial.equationalRoom
silmaril room logic.algebraic.lambda.lambda_room := Silmaril.Logic.Algebraic.Lambda.lambdaRoom
silmaril room logic.algebraic.many_sorted.varying.room := Silmaril.Logic.Algebraic.ManySorted.Varying.room
silmaril room logic.algebraic.order_sorted.initial.ordered_room := Silmaril.Logic.Algebraic.OrderSorted.Initial.orderedRoom
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
silmaril room logic.stlc_equations.room := Silmaril.Logic.STLCEquations.room
silmaril room logic.stlc_matching.source_room := Silmaril.Logic.STLCMatching.sourceRoom
silmaril room logic.stlc_matching.target_room := Silmaril.Logic.STLCMatching.targetRoom
silmaril room logic.temporal.ltl.room := Silmaril.Logic.Temporal.LTL.room
