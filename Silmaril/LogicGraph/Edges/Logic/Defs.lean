module

public import Silmaril.Logic.CTL
public import Silmaril.Logic.CTL.Defs
public import Silmaril.Logic.CTL.Derived.Thms
public import Silmaril.Logic.CTL.Examples
public import Silmaril.Logic.CTL.Mu.Defs
public import Silmaril.Logic.CTL.Mu.Thms
public import Silmaril.Logic.CTL.Thms
public import Silmaril.Logic.Institution.Examples.Comorphisms
public import Silmaril.Logic.Institution.Hets.Examples
public import Silmaril.Logic.Matching.FirstOrder.Defs
public import Silmaril.Logic.Matching.FirstOrder.Pointed
public import Silmaril.Logic.Matching.FirstOrder.Pointed.Defs
public import Silmaril.Logic.Matching.FirstOrder.Pointed.Examples
public import Silmaril.Logic.Matching.FirstOrder.Pointed.Hets
public import Silmaril.Logic.Matching.FirstOrder.Pointed.Propositional
public import Silmaril.Logic.Matching.FirstOrder.Thms
public import Silmaril.Logic.Matching.FixedPoint
public import Silmaril.Logic.Matching.FixedPoint.Defs
public import Silmaril.Logic.Matching.FixedPoint.Dual.Thms
public import Silmaril.Logic.Matching.FixedPoint.Modal.Defs
public import Silmaril.Logic.Matching.FixedPoint.Modal.Thms
public import Silmaril.Logic.Matching.FixedPoint.Thms
public import Silmaril.Logic.Matching.FixedPoint.Variables.Thms
public import Silmaril.Logic.Modal.Propositional
public import Silmaril.Logic.ModalMu
public import Silmaril.Logic.ModalMu.AtomSubstitution.Audits
public import Silmaril.Logic.ModalMu.AtomSubstitution.Defs
public import Silmaril.Logic.ModalMu.AtomSubstitution.Examples
public import Silmaril.Logic.ModalMu.AtomSubstitution.Thms
public import Silmaril.Logic.ModalMu.Defs
public import Silmaril.Logic.ModalMu.Examples
public import Silmaril.Logic.ModalMu.FiniteVector.Audits
public import Silmaril.Logic.ModalMu.FiniteVector.Defs
public import Silmaril.Logic.ModalMu.FiniteVector.Examples
public import Silmaril.Logic.ModalMu.FiniteVector.Thms
public import Silmaril.Logic.ModalMu.K.Defs
public import Silmaril.Logic.ModalMu.K.Thms
public import Silmaril.Logic.ModalMu.Reachability.Defs
public import Silmaril.Logic.ModalMu.Reachability.Thms
public import Silmaril.Logic.ModalMu.Substitution.Defs
public import Silmaril.Logic.ModalMu.Substitution.Thms
public import Silmaril.Logic.ModalMu.Thms
public import Silmaril.Logic.ModalMu.Variables.Defs
public import Silmaril.Logic.ModalMu.Variables.Thms
public import Silmaril.Logic.ModalMu.Vector.Audits
public import Silmaril.Logic.ModalMu.Vector.Defs
public import Silmaril.Logic.ModalMu.Vector.Examples
public import Silmaril.Logic.ModalMu.Vector.Thms
public import Silmaril.Logic.PDL
public import Silmaril.Logic.PDL.Defs
public import Silmaril.Logic.PDL.Examples
public import Silmaril.Logic.PDL.K.Defs
public import Silmaril.Logic.PDL.K.Thms
public import Silmaril.Logic.PDL.Mu.Defs
public import Silmaril.Logic.PDL.Mu.Thms
public import Silmaril.Logic.PDL.Thms
public import Silmaril.Logic.Reachability.Defs
public import Silmaril.Logic.Reachability.Relational
public import Silmaril.Logic.Reachability.Thms
public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.Wasm.InstObs.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Logic`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism inst.comorphism.of_obs := Silmaril.Inst.Comorphism.ofObs (facts := [Silmaril.Inst.Comorphism.ofObs_modelExpansive])
silmaril comorphism logic.ctl.ctl_to_mu := Silmaril.Logic.CTL.ctlToMu (facts := [Silmaril.Logic.CTL.ctlToMu_modelExpansive])
silmaril comorphism logic.ctl.k_to_ctl := Silmaril.Logic.CTL.kToCTL (facts := [Silmaril.Logic.CTL.kToCTL_modelExpansive])
silmaril comorphism logic.institution.examples.eq_to_fol := Silmaril.Logic.Institution.Examples.eqToFol (facts := [Silmaril.Logic.Institution.Examples.eqToFol_modelExpansive])
silmaril comorphism logic.institution.examples.pl_to_fol := Silmaril.Logic.Institution.Examples.plToFol (hets := "Prop2CASL") (hets_relation := related) (facts := [Silmaril.Logic.Institution.Examples.plToFol_modelExpansive])
silmaril comorphism logic.matching.first_order.pointed.propositional_to_pointed_matching := Silmaril.Logic.Matching.FirstOrder.Pointed.propositionalToPointedMatching (facts := [Silmaril.Logic.Matching.FirstOrder.Pointed.propositionalToPointedMatching_modelExpansive])
silmaril comorphism logic.matching.fixed_point.first_order_pointed_to_fixed_point := Silmaril.Logic.Matching.FixedPoint.firstOrderPointedToFixedPoint (facts := [Silmaril.Logic.Matching.FixedPoint.firstOrderPointedToFixedPoint_modelExpansive])
silmaril comorphism logic.matching.fixed_point.first_order_to_fixed_point := Silmaril.Logic.Matching.FixedPoint.firstOrderToFixedPoint (facts := [Silmaril.Logic.Matching.FixedPoint.firstOrderToFixedPoint_modelExpansive])
silmaril comorphism logic.matching.fixed_point.modal_to_matching := Silmaril.Logic.Matching.FixedPoint.modalToMatching (facts := [Silmaril.Logic.Matching.FixedPoint.modalToMatching_modelExpansive])
silmaril comorphism logic.modal.propositional_to_modal := Silmaril.Logic.Modal.propositionalToModal
silmaril comorphism logic.modal_mu.k_to_mu := Silmaril.Logic.ModalMu.kToMu (facts := [Silmaril.Logic.ModalMu.kToMu_modelExpansive])
silmaril comorphism logic.pdl.k_to_pdl := Silmaril.Logic.PDL.kToPDL (facts := [Silmaril.Logic.PDL.kToPDL_modelExpansive])
silmaril comorphism logic.reachability.to_matching := Silmaril.Logic.Reachability.toMatching (facts := [Silmaril.Logic.Reachability.toMatching_modelExpansive])
silmaril morphism inst.morphism.of_obs := Silmaril.Inst.Morphism.ofObs (facts := [Silmaril.Inst.Morphism.ofObs_sound])
silmaril morphism logic.institution.examples.fol_to_eq := Silmaril.Logic.Institution.Examples.folToEq (facts := [Silmaril.Logic.Institution.Examples.folToEq_sound])
