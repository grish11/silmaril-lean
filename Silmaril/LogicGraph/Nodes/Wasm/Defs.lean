module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Wasm.Category.Institution.Defs
public import Silmaril.Wasm.Category.LinkSat.Defs
public import Silmaril.Wasm.Category.Programs.Defs
public import Silmaril.Wasm.FnInst.Core.Defs
public import Silmaril.Wasm.FnInst.Ground.Check.Defs
public import Silmaril.Wasm.FnInst.IR.Graph.Defs
public import Silmaril.Wasm.FnInst.IR.Lang.Defs
public import Silmaril.Wasm.FnInst.Models.Inst.Defs
public import Silmaril.Wasm.FnInst.Models.Version.Defs
public import Silmaril.Wasm.FnInst.Opt.Inst.Defs
public import Silmaril.Wasm.FnInst.Opt.Merge.Defs
public import Silmaril.Wasm.FnInst.Partial.Defs
public import Silmaril.Wasm.Institution.Api.Defs
public import Silmaril.Wasm.Institution.CompGameGraph.Defs
public import Silmaril.Wasm.Institution.DivGames.Spec.Defs
public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Institution.SpecGInst.Defs
public import Silmaril.Wasm.Models.Game.Defs
public import Silmaril.Wasm.Spec.Attest.Defs
public import Silmaril.Wasm.Spec.Format.Defs
public import Silmaril.Wasm.Spec.Graph.Defs
public import Silmaril.Wasm.Spec.Harness.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Wasm.Unified.Component.Open.Thms
public import Silmaril.Wasm.Unified.Component.Val.Thms
public import Silmaril.Wasm.Unified.Inst.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Wasm`

Registrations of the institution and room declarations of the `Wasm` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution wasm.category.wasm_prog.inst := Silmaril.Wasm.Category.WasmProg.inst
silmaril institution wasm.category.beh_inst := Silmaril.Wasm.Category.behInst
silmaril institution wasm.fn_inst.ground.check.check_inst := Silmaril.Wasm.FnInst.Ground.Check.checkInst
silmaril institution wasm.fn_inst.h_pres.inst := Silmaril.Wasm.FnInst.HPres.inst
silmaril institution wasm.fn_inst.h_pres.partial_inst := Silmaril.Wasm.FnInst.HPres.partialInst
silmaril institution wasm.fn_inst.ir.lang.inst := Silmaril.Wasm.FnInst.IR.Lang.inst
silmaril institution wasm.fn_inst.ir.node.inst := Silmaril.Wasm.FnInst.IR.Node.inst
silmaril institution wasm.fn_inst.models.body_inst := Silmaril.Wasm.FnInst.Models.bodyInst
silmaril institution wasm.fn_inst.models.k_inst := Silmaril.Wasm.FnInst.Models.kInst
silmaril institution wasm.fn_inst.models.sem_inst := Silmaril.Wasm.FnInst.Models.semInst
silmaril institution wasm.fn_inst.models.v_inst := Silmaril.Wasm.FnInst.Models.vInst
silmaril institution wasm.fn_inst.opt.merge.named_inst := Silmaril.Wasm.FnInst.Opt.Merge.namedInst
silmaril institution wasm.fn_inst.opt.seg_inst := Silmaril.Wasm.FnInst.Opt.segInst
silmaril institution wasm.fn_inst.all_inst := Silmaril.Wasm.FnInst.allInst
silmaril institution wasm.fn_inst.all_p_inst := Silmaril.Wasm.FnInst.allPInst
silmaril institution wasm.fn_inst.hole_inst := Silmaril.Wasm.FnInst.holeInst
silmaril institution wasm.fn_inst.hole_p_inst := Silmaril.Wasm.FnInst.holePInst
silmaril institution wasm.fn_inst.one_inst := Silmaril.Wasm.FnInst.oneInst
silmaril institution wasm.fn_inst.one_p_inst := Silmaril.Wasm.FnInst.onePInst
silmaril institution wasm.fn_inst.set_inst := Silmaril.Wasm.FnInst.setInst
silmaril institution wasm.fn_inst.set_p_inst := Silmaril.Wasm.FnInst.setPInst
silmaril institution wasm.institution.comp_game_graph.inst := Silmaril.Wasm.Institution.CompGameGraph.inst
silmaril institution wasm.institution.div_games.dinst := Silmaril.Wasm.Institution.DivGames.dinst
silmaril institution wasm.institution.obs_graph.inst := Silmaril.Wasm.Institution.ObsGraph.inst
silmaril institution wasm.institution.obs_semantics.inst := Silmaril.Wasm.Institution.ObsSemantics.inst
silmaril institution wasm.institution.spec_g_inst.trace_inst := Silmaril.Wasm.Institution.SpecGInst.traceInst
silmaril institution wasm.models.wasm_model.ginst := Silmaril.Wasm.Models.WasmModel.ginst
silmaril institution wasm.spec.graph.s_node.inst := Silmaril.Wasm.Spec.Graph.SNode.inst
silmaril institution wasm.spec.graph.spec_flat := Silmaril.Wasm.Spec.Graph.specFlat
silmaril institution wasm.spec.inst := Silmaril.Wasm.Spec.inst
silmaril institution wasm.unified.component.cinst := Silmaril.Wasm.Unified.Component.cinst
silmaril institution wasm.unified.component.cinst_o := Silmaril.Wasm.Unified.Component.cinstO
silmaril institution wasm.unified.component.vinst := Silmaril.Wasm.Unified.Component.vinst
silmaril institution wasm.unified.inst := Silmaril.Wasm.Unified.inst
silmaril room wasm.category.room_a := Silmaril.Wasm.Category.roomA
silmaril room wasm.category.room_e := Silmaril.Wasm.Category.roomE
silmaril room wasm.institution.obs_semantics.room := Silmaril.Wasm.Institution.ObsSemantics.room
silmaril room wasm.institution.spec_g_inst.troom := Silmaril.Wasm.Institution.SpecGInst.troom
silmaril room wasm.spec.attest.att_room := Silmaril.Wasm.Spec.Attest.attRoom
silmaril room wasm.spec.attest.pl_room := Silmaril.Wasm.Spec.Attest.plRoom
silmaril room wasm.spec.prog_room := Silmaril.Wasm.Spec.progRoom
silmaril room wasm.spec.room := Silmaril.Wasm.Spec.room
silmaril room wasm.unified.component.croom := Silmaril.Wasm.Unified.Component.croom
silmaril room wasm.unified.component.oroom := Silmaril.Wasm.Unified.Component.oroom
silmaril room wasm.unified.component.vroom := Silmaril.Wasm.Unified.Component.vroom
silmaril room wasm.unified.room := Silmaril.Wasm.Unified.room
