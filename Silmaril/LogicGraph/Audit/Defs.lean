module

public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.LogicGraph.Edges.Defs
public import Silmaril.LogicGraph.Hets.Defs
public import Silmaril.Automata.Institution.Thms
public import Silmaril.Calculi.LambdaCube.Hets.Defs
public import Silmaril.Calculi.LambdaCube.PER.CubeMorphisms.Defs
public import Silmaril.Calculi.LambdaCube.PER.PTSMorphism
public import Silmaril.Calculi.LambdaCube.STLC.Defs
public import Silmaril.Calculi.LambdaCube.Semantics
public import Silmaril.Cerberus.Institution.Defs
public import Silmaril.Cli.Institution.Defs
public import Silmaril.Compiler.Category.Cerberus.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionInstitution.Defs
public import Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.Defs
public import Silmaril.Compiler.Native.Correctness.Institution.Defs
public import Silmaril.Compiler.Native.Optimize.AddressInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.EffectsInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.FiniteInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.FloatingInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Institution.Defs
public import Silmaril.Compiler.Native.Optimize.SlotsInstitution.Defs
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Observational
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Relational
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Signature
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Transitions
public import Silmaril.Games.DInstitution.Defs
public import Silmaril.Games.InstFacade.Defs
public import Silmaril.Games.InstGraph.Defs
public import Silmaril.Games.Institution.Defs
public import Silmaril.Games.Reindex.Defs
public import Silmaril.Libc.Contract.Inst.Defs
public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.Logic.Inst.Core.Defs
public import Silmaril.Logic.Inst.Graph.Defs
public import Silmaril.Logic.Institution.Basic
public import Silmaril.Logic.Institution.Examples.Comorphisms
public import Silmaril.Logic.Institution.Examples.Equational
public import Silmaril.Logic.Institution.Examples.FirstOrder
public import Silmaril.Logic.Institution.Examples.Propositional
public import Silmaril.Logic.Institution.Examples.Unsorted
public import Silmaril.Logic.Institution.Examples.UnsortedToFOL
public import Silmaril.Logic.Institution.Grothendieck.Basic
public import Silmaril.Logic.Institution.Grothendieck.Examples.Het
public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Silmaril.Logic.Institution.Hets.SpecLanguage
public import Silmaril.Logic.Institution.Metatheory.Consilience
public import Silmaril.Logic.Institution.Metatheory.Entailment
public import Silmaril.Logic.Institution.Metatheory.HOL
public import Silmaril.Logic.Institution.Metatheory.Metamath
public import Silmaril.Logic.Institution.Morphism
public import Silmaril.Logic.Institution.Theoroidal
public import Silmaril.Logic.Institution.Theory
public import Silmaril.Machine.Abi.Defs
public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.Machine.Abi.Win64.Thms
public import Silmaril.Net.Http1.Institution.Thms
public import Silmaril.Net.Udp.Institution.Thms
public import Silmaril.SSA.LambdaRTL.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Loop.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Quotient.Defs
public import Silmaril.SSA.LambdaRTL.Version.Institution.Defs
public import Silmaril.Servers.Core.Defs
public import Silmaril.Servers.OpenApi.Thms
public import Silmaril.Wasi.Spec.Defs
public import Silmaril.Wasi.World.Defs
public import Silmaril.Wasm.Category.Api.Defs
public import Silmaril.Wasm.Category.Institution.Defs
public import Silmaril.Wasm.Category.LinkSat.Defs
public import Silmaril.Wasm.Category.LinkSat.Thms
public import Silmaril.Wasm.Category.Programs.Defs
public import Silmaril.Wasm.FnInst.Comor.Defs
public import Silmaril.Wasm.FnInst.Core.Defs
public import Silmaril.Wasm.FnInst.Ground.Check.Defs
public import Silmaril.Wasm.FnInst.IR.Graph.Defs
public import Silmaril.Wasm.FnInst.IR.Lang.Defs
public import Silmaril.Wasm.FnInst.Models.Inst.Defs
public import Silmaril.Wasm.FnInst.Models.Version.Defs
public import Silmaril.Wasm.FnInst.Opt.Inst.Defs
public import Silmaril.Wasm.FnInst.Opt.Merge.Defs
public import Silmaril.Wasm.FnInst.Partial.Defs
public import Silmaril.Wasm.InstObs.Defs
public import Silmaril.Wasm.InstObs.Examples.Thms
public import Silmaril.Wasm.Institution.Api.Defs
public import Silmaril.Wasm.Institution.CompGameGraph.Defs
public import Silmaril.Wasm.Institution.CompGraph.Defs
public import Silmaril.Wasm.Institution.DivGames.Spec.Defs
public import Silmaril.Wasm.Institution.GameGraph.Defs
public import Silmaril.Wasm.Institution.GameInst.Defs
public import Silmaril.Wasm.Institution.GameInstMaps.Defs
public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Institution.Graph.Defs
public import Silmaril.Wasm.Institution.Hooks.Defs
public import Silmaril.Wasm.Institution.SpecGInst.Defs
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
public import Silmaril.Wasm.Spec.Attest.Defs
public import Silmaril.Wasm.Spec.Attest.Thms
public import Silmaril.Wasm.Spec.Component.Async.Defs
public import Silmaril.Wasm.Spec.Format.Defs
public import Silmaril.Wasm.Spec.Graph.Defs
public import Silmaril.Wasm.Spec.Harness.Defs
public import Silmaril.Wasm.Spec.Joint.Defs
public import Silmaril.Wasm.Spec.Joint.Wrap.Defs
public import Silmaril.Wasm.Spec.Maps.Defs
public import Silmaril.Wasm.Unified.Component.Inst.Defs
public import Silmaril.Wasm.Unified.Component.InstWrap.Defs
public import Silmaril.Wasm.Unified.Component.Open.Thms
public import Silmaril.Wasm.Unified.Component.Val.Thms
public import Silmaril.Wasm.Unified.Inst.Defs
public import Silmaril.X86.BinInstitution.Defs
public import Silmaril.X86.Institution.Defs

/-!
# Logic graph: the audit

Every registration (`Silmaril.LogicGraph.{Nodes,Edges}.Defs`), the Hets list, and every header
module that declares an institution, comorphism, morphism, room or corridor (or a family of
them). `silmaril logic_audit` then records each such declaration of `Silmaril` reachable from
here, with the record that registers it, if any: what the registry omits is listed, and generic
constructions (over an arbitrary institution, room or map) are marked as such. `Proofs` and `Raw`
modules are not imported: their declarations are not an API and are not audited.
-/

silmaril logic_audit (prefix := "Silmaril")
