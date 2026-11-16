module

public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.Wasi.Spec.Thms
public import Silmaril.Wasm.Category.Api.Defs
public import Silmaril.Wasm.Category.Institution.Defs
public import Silmaril.Wasm.Category.LinkSat.Thms
public import Silmaril.Wasm.FnInst.Comor.Defs
public import Silmaril.Wasm.FnInst.Comor.Thms
public import Silmaril.Wasm.FnInst.IR.Lang.Defs
public import Silmaril.Wasm.FnInst.IR.Lang.Thms
public import Silmaril.Wasm.FnInst.Models.Inst.Defs
public import Silmaril.Wasm.FnInst.Models.Version.Defs
public import Silmaril.Wasm.FnInst.Partial.Defs
public import Silmaril.Wasm.InstObs.Defs
public import Silmaril.Wasm.InstObs.Examples.Thms
public import Silmaril.Wasm.Institution.Api.Defs
public import Silmaril.Wasm.Institution.CompGraph.Defs
public import Silmaril.Wasm.Institution.GameGraph.Defs
public import Silmaril.Wasm.Institution.GameInst.Defs
public import Silmaril.Wasm.Institution.GameInstMaps.Defs
public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Institution.Graph.Defs
public import Silmaril.Wasm.Institution.SpecGInst.Defs
public import Silmaril.Wasm.Institution.Structured.Thms
public import Silmaril.Wasm.LambdaRTL.Institution.Thms
public import Silmaril.Wasm.Models.FX.Thms
public import Silmaril.Wasm.Models.FXVModel.Thms
public import Silmaril.Wasm.Models.FunCloCompile.Thms
public import Silmaril.Wasm.Models.FunCloDiv.Thms
public import Silmaril.Wasm.Models.FunCompile.Thms
public import Silmaril.Wasm.Models.FunRefCloCompile.Thms
public import Silmaril.Wasm.Models.FunRefCloDiv.Thms
public import Silmaril.Wasm.Models.FunRefCompile.Thms
public import Silmaril.Wasm.Models.Game.Defs
public import Silmaril.Wasm.Models.Realise.Defs
public import Silmaril.Wasm.Models.Realise.Thms
public import Silmaril.Wasm.Spec.Attest.Core.Thms
public import Silmaril.Wasm.Spec.Attest.Thms
public import Silmaril.Wasm.Spec.Component.Async.Defs
public import Silmaril.Wasm.Spec.Graph.Defs
public import Silmaril.Wasm.Spec.Graph.Thms
public import Silmaril.Wasm.Spec.Joint.Defs
public import Silmaril.Wasm.Spec.Joint.Wrap.Defs
public import Silmaril.Wasm.Spec.Maps.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Wasm.Unified.Component.InstWrap.Defs
public import Silmaril.Wasm.Unified.Component.InstWrap.Thms
public import Silmaril.Wasm.Unified.Component.Open.Thms
public import Silmaril.Wasm.Unified.Component.Val.Thms

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Wasm`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism wasm.category.realiser.co_hom := Silmaril.Wasm.Category.Realiser.coHom
silmaril comorphism wasm.category.realiser.comorphism := Silmaril.Wasm.Category.Realiser.comorphism (facts := [Silmaril.Wasm.Category.Realiser.comorphism_modelExpansive])
silmaril comorphism wasm.fn_inst.ir.lang.tr.comorphism := Silmaril.Wasm.FnInst.IR.Lang.Tr.comorphism (facts := [Silmaril.Wasm.FnInst.IR.Lang.Tr.modelExpansive, Silmaril.Wasm.LambdaRTL.toRTL_modelExpansive])
silmaril comorphism wasm.fn_inst.models.forget := Silmaril.Wasm.FnInst.Models.forget
silmaril comorphism wasm.fn_inst.models.k_to_body := Silmaril.Wasm.FnInst.Models.kToBody
silmaril comorphism wasm.fn_inst.models.sem_to_body := Silmaril.Wasm.FnInst.Models.semToBody
silmaril comorphism wasm.fn_inst.hole_to_all := Silmaril.Wasm.FnInst.holeToAll (facts := [Silmaril.Wasm.FnInst.holeToAll_modelExpansive])
silmaril comorphism wasm.fn_inst.hole_to_all_p := Silmaril.Wasm.FnInst.holeToAllP
silmaril comorphism wasm.fn_inst.one_to_all := Silmaril.Wasm.FnInst.oneToAll (facts := [Silmaril.Wasm.FnInst.oneToAll_modelExpansive])
silmaril comorphism wasm.fn_inst.one_to_set := Silmaril.Wasm.FnInst.oneToSet (facts := [Silmaril.Wasm.FnInst.oneToSet_modelExpansive])
silmaril comorphism wasm.fn_inst.one_to_set_p := Silmaril.Wasm.FnInst.oneToSetP
silmaril comorphism wasm.fn_inst.set_to_all := Silmaril.Wasm.FnInst.setToAll (facts := [Silmaril.Wasm.FnInst.setToAll_modelExpansive])
silmaril comorphism wasm.fn_inst.set_to_all_p := Silmaril.Wasm.FnInst.setToAllP
silmaril comorphism wasm.inst_obs.examples.id_co := Silmaril.Wasm.InstObs.Examples.idCo (facts := [Silmaril.Wasm.InstObs.Examples.idCo_modelExpansive])
silmaril comorphism wasm.inst_obs.examples.id_co_computable := Silmaril.Wasm.InstObs.Examples.idCoComputable
silmaril comorphism wasm.institution.game_inst.co_hom := Silmaril.Wasm.Institution.GameInst.coHom (facts := [Silmaril.Wasm.Institution.GameInst.coHom_modelExpansive])
silmaril comorphism wasm.institution.game_inst.lts_co_hom := Silmaril.Wasm.Institution.GameInst.ltsCoHom
silmaril comorphism wasm.institution.game_inst.red_co_hom := Silmaril.Wasm.Institution.GameInst.redCoHom
silmaril comorphism wasm.institution.game_inst_maps.comp_co_hom := Silmaril.Wasm.Institution.GameInstMaps.compCoHom
silmaril comorphism wasm.institution.game_inst_maps.module_co_hom := Silmaril.Wasm.Institution.GameInstMaps.moduleCoHom
silmaril comorphism wasm.institution.game_inst_maps.program_co_hom := Silmaril.Wasm.Institution.GameInstMaps.programCoHom
silmaril comorphism wasm.institution.game_inst_maps.scalar_co_hom := Silmaril.Wasm.Institution.GameInstMaps.scalarCoHom
silmaril comorphism wasm.institution.obs_semantics.exp_translation.comorphism := Silmaril.Wasm.Institution.ObsSemantics.ExpTranslation.comorphism (facts := [Silmaril.Wasm.Institution.ObsSemantics.ExpTranslation.modelExpansive])
silmaril comorphism wasm.institution.obs_semantics.translation.co_hom := Silmaril.Wasm.Institution.ObsSemantics.Translation.coHom (facts := [Silmaril.Wasm.Institution.ObsSemantics.Translation.coHom_modelExpansive])
silmaril comorphism wasm.institution.spec_g_inst.spec_co_hom := Silmaril.Wasm.Institution.SpecGInst.specCoHom
silmaril comorphism wasm.models.fx.fx_co_hom := Silmaril.Wasm.Models.FX.fxCoHom
silmaril comorphism wasm.models.fx.fx_g_inst_co_hom := Silmaril.Wasm.Models.FX.fxGInstCoHom
silmaril comorphism wasm.models.fxv_model.fx_co_hom_prime := Silmaril.Wasm.Models.FXVModel.fxCoHom'
silmaril comorphism wasm.models.fxv_model.fx_fix_g_inst_co_hom := Silmaril.Wasm.Models.FXVModel.fxFixGInstCoHom
silmaril comorphism wasm.models.fxv_model.fx_g_inst_co_hom_prime := Silmaril.Wasm.Models.FXVModel.fxGInstCoHom'
silmaril comorphism wasm.models.fun_clo_compile.compile_co_hom := Silmaril.Wasm.Models.FunCloCompile.compileCoHom
silmaril comorphism wasm.models.fun_clo_div.compile_co_hom_all := Silmaril.Wasm.Models.FunCloDiv.compileCoHomAll
silmaril comorphism wasm.models.fun_compile.compile_co_hom := Silmaril.Wasm.Models.FunCompile.compileCoHom
silmaril comorphism wasm.models.fun_ref_clo_compile.compile_co_hom := Silmaril.Wasm.Models.FunRefCloCompile.compileCoHom
silmaril comorphism wasm.models.fun_ref_clo_div.compile_co_hom_all := Silmaril.Wasm.Models.FunRefCloDiv.compileCoHomAll
silmaril comorphism wasm.models.fun_ref_compile.compile_co_hom := Silmaril.Wasm.Models.FunRefCompile.compileCoHom
silmaril comorphism wasm.models.wasm_model.emb.co_hom := Silmaril.Wasm.Models.WasmModel.Emb.coHom
silmaril comorphism wasm.models.wasm_model.emb.ginst_co_hom := Silmaril.Wasm.Models.WasmModel.Emb.ginstCoHom
silmaril comorphism wasm.models.wasm_model.to_g_inst := Silmaril.Wasm.Models.WasmModel.toGInst
silmaril comorphism wasm.models.core_co_hom := Silmaril.Wasm.Models.coreCoHom
silmaril comorphism wasm.spec.component.sync_co_hom := Silmaril.Wasm.Spec.Component.syncCoHom
silmaril comorphism wasm.spec.graph.s_edge.co_hom := Silmaril.Wasm.Spec.Graph.SEdge.coHom (facts := [Silmaril.Wasm.Spec.Graph.SEdge.modelExpansive])
silmaril comorphism wasm.spec.logic_map.co_hom := Silmaril.Wasm.Spec.LogicMap.coHom (facts := [Silmaril.Wasm.Spec.LogicMap.coHom_modelExpansive])
silmaril comorphism wasm.spec.sem_map.co_hom := Silmaril.Wasm.Spec.SemMap.coHom
silmaril comorphism wasm.spec.push_co_hom := Silmaril.Wasm.Spec.pushCoHom (facts := [Silmaril.Wasm.Spec.pushCoHom_modelExpansive])
silmaril comorphism wasm.spec.sum_inl_co_hom := Silmaril.Wasm.Spec.sumInlCoHom
silmaril comorphism wasm.spec.sum_inr_co_hom := Silmaril.Wasm.Spec.sumInrCoHom
silmaril comorphism wasm.spec.wrap_co_hom := Silmaril.Wasm.Spec.wrapCoHom
silmaril comorphism wasm.unified.component.from_v := Silmaril.Wasm.Unified.Component.fromV (facts := [Silmaril.Wasm.Unified.Component.fromV_modelExpansive])
silmaril comorphism wasm.unified.component.of_closed := Silmaril.Wasm.Unified.Component.ofClosed
silmaril comorphism wasm.unified.component.to_comp := Silmaril.Wasm.Unified.Component.toComp (facts := [Silmaril.Wasm.Unified.Component.toComp_modelExpansive])
silmaril comorphism wasm.unified.component.to_comp_w := Silmaril.Wasm.Unified.Component.toCompW (facts := [Silmaril.Wasm.Unified.Component.toCompW_modelExpansive])
silmaril comorphism wasm.unified.component.to_v := Silmaril.Wasm.Unified.Component.toV (facts := [Silmaril.Wasm.Unified.Component.toV_modelExpansive])
silmaril morphism wasm.institution.comp_graph.proj_hom := Silmaril.Wasm.Institution.CompGraph.projHom
silmaril morphism wasm.institution.game_graph.proj_hom := Silmaril.Wasm.Institution.GameGraph.projHom
silmaril morphism wasm.institution.graph.proj_hom := Silmaril.Wasm.Institution.Graph.projHom
silmaril morphism wasm.institution.obs_semantics.exp_translation.morphism := Silmaril.Wasm.Institution.ObsSemantics.ExpTranslation.morphism (facts := [Silmaril.Wasm.Institution.ObsSemantics.ExpTranslation.sound])
silmaril morphism wasm.institution.obs_semantics.translation.to_hom := Silmaril.Wasm.Institution.ObsSemantics.Translation.toHom (facts := [Silmaril.Wasm.Institution.ObsSemantics.Translation.toHom_sound])
silmaril corridor wasm.category.link_corridor_a := Silmaril.Wasm.Category.linkCorridorA
silmaril corridor wasm.category.link_corridor_e := Silmaril.Wasm.Category.linkCorridorE
silmaril corridor wasm.category.prov_corridor_a := Silmaril.Wasm.Category.provCorridorA
silmaril corridor wasm.category.prov_corridor_e := Silmaril.Wasm.Category.provCorridorE
silmaril corridor wasm.spec.attest.core.core_corridor := Silmaril.Wasm.Spec.Attest.Core.coreCorridor
silmaril corridor wasm.spec.attest.corridor := Silmaril.Wasm.Spec.Attest.corridor (facts := [Silmaril.Wasm.Spec.Attest.corridor_modelExpansive])
