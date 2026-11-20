module

public import Silmaril.Wasm.Component.Reference.DirectLift.Init.Defs
import Silmaril.Wasm.Component.Reference.DirectLift.Thms
import Silmaril.Wasm.Component.Reference.Silent.Thms
import Silmaril.Wasm.Component.Reference.Embedding.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.DirectLift

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.DirectLift
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded

private theorem coreInstance {P : Profile} (sc : Scope (core3P P))
    (cfg : Machine.Config (core3P P) Unit) {slot : Nat} {wire : List (String × Nat)}
    {mod : Silmaril.Wasm.Module} {actual : List (core3P P).ExternVal}
    {store : Store (CanonHost (core3P P))} {ci : (core3P P).Inst}
    (moduleAt : sc.frame.coreModule? slot = some mod)
    (imports : coreImportsFor? cfg.store.core mod wire sc.frame = some actual)
    (prepared : (core3P P).prepare? cfg.store.core mod actual = some (store, ci, none)) :
    TRuns (instantiateDef callRecurse ⟨0⟩ [] [] sc (.coreInstance (.instantiate slot wire)))
      cfg { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++ [(core3P P).exports ci] } }
      { cfg with store := setCoreSt store cfg.store } := by
  have run : TRuns (instantiateCore ⟨0⟩ sc.frame slot wire : Canon.P (core3P P) Unit _)
      cfg ((core3P P).exports ci) { cfg with store := setCoreSt store cfg.store } := by
    unfold instantiateCore
    rw [moduleAt]
    refine (TRuns.pure _ cfg).bind ((TRuns.getStore cfg).bind ?_)
    rw [imports]
    refine (TRuns.pure _ cfg).bind ?_
    dsimp only
    rw [prepared]
    exact (TRuns.modifyStore (f := setCoreSt store) (fun _ => rfl) cfg).bind
      (f := fun _ => pure ((core3P P).exports ci)) (TRuns.pure _ _)
  exact run.bind (TRuns.pure _ _)

private theorem resolveSignature {P : Profile} (w : DirectWire) (f : Frame (core3P P)) :
    resolveFuncType? f w.signature = some w.liftType := by
  have params : ∀ xs : List (String × Syntax.Prim),
      (xs.map fun (name, ty) => (name, Syntax.VT.prim ty)).mapM
        (fun (name, ty) => (name, ·) <$> resolveValType? f ty) =
          some (xs.map fun (name, ty) => (name, primType ty)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons head tail ih =>
      rw [List.map_cons, List.mapM_cons, ih, List.map_cons]
      rfl
  unfold DirectWire.signature DirectWire.liftType resolveFuncType?
  dsimp only
  rw [params]
  cases w.result <;> rfl

private theorem typeStep {P : Profile} (w : DirectWire) (sc : Scope (core3P P)) :
    instantiateDef (σ := Unit) callRecurse ⟨0⟩ [] [] sc (.type (.func w.signature)) =
      pure { sc with frame := { sc.frame with types := sc.frame.types ++ [.func w.liftType] } } := by
  simp only [instantiateDef, staticType?, resolveSignature, Option.map_some, need, orTrap, pure_bind,
    pushEntry, Frame.push]

private noncomputable abbrev initial (P : Profile) : Machine.Config (core3P P) Unit := initConfig ()

private theorem definitionRun {w : DirectWire} {P : Profile} {shared : Store (CanonHost (core3P P))}
    {addr : Nat} (data : w.Prepared P shared addr) :
    ∃ sc, TRuns (w.component.foldlM (instantiateDef callRecurse ⟨0⟩ [] []) {})
      { initial P with store := { (initial P).store with insts := [{}], nestingDepth := 1 } } sc
      { w.ready shared addr with store := { (w.ready shared addr).store with nestingDepth := 1 } } ∧
      sc.exports = [(w.exportName, .func ⟨0⟩)] := by
  let start := { initial P with store := { (initial P).store with insts := [{}], nestingDepth := 1 } }
  change ∃ sc, TRuns _ start sc _ ∧ _
  unfold DirectWire.component
  let finished : Scope (core3P P) :=
    { frame := { w.providerFrame data.providerInst with
        coreInstances := [(core3P P).exports data.providerInst, (core3P P).exports data.consumerInst]
        coreFuncs := [addr]
        types := [.func w.liftType]
        funcs := [⟨0⟩, ⟨0⟩] }
      exports := [(w.exportName, .func ⟨0⟩)] }
  refine ⟨finished, ?_, rfl⟩
  · refine TRuns.foldlM_cons (TRuns.of_eq start (instDef_coreModule {} _)) ?_
    have noImports : coreImportsFor? start.store.core w.provider []
        { (Frame.empty : Frame (core3P P)) with coreModules := [w.provider] } = some [] := by
      unfold coreImportsFor?
      rw [data.providerImports]
      rfl
    refine TRuns.foldlM_cons (coreInstance _ start rfl noImports data.provide) ?_
    refine TRuns.foldlM_cons (TRuns.of_eq _ (instDef_coreModule _ _)) ?_
    refine TRuns.foldlM_cons (coreInstance _ _ rfl data.resolve data.consume) ?_
    refine TRuns.foldlM_cons (TRuns.of_eq _ (instDef_alias _ rfl data.lookup rfl)) ?_
    refine TRuns.foldlM_cons (TRuns.of_eq _ (typeStep w _)) ?_
    refine TRuns.foldlM_cons
      (sc₁ := { finished with frame := { finished.frame with funcs := [⟨0⟩] }, exports := [] })
      (m₁ := { w.ready shared addr with store := { (w.ready shared addr).store with nestingDepth := 1 } }) ?_ ?_
    · let beforeLift : Scope (core3P P) :=
        { finished with frame := { finished.frame with funcs := [] }, exports := [] }
      change TRuns (instantiateDef callRecurse ⟨0⟩ [] [] beforeLift (.canon (.lift 0 [] 0))) _ _ _
      rw [instDef_lift beforeLift (cf := 0) (ft := 0) (a := addr) (t := w.liftType) rfl rfl]
      exact (TRuns.allocObj ArenaField.funcs (fun _ _ => rfl) _ _).bind (TRuns.pure _ _)
    · exact TRuns.foldlM_cons (TRuns.of_eq _ (instDef_funcExport _ rfl)) (TRuns.foldlM_nil _ _)

private theorem programRun {w : DirectWire} {P : Profile} {shared : Store (CanonHost (core3P P))}
    {addr : Nat} (data : w.Prepared P shared addr) :
    SRuns (instantiateProg w.component [] : Canon.P (core3P P) Unit _) (initial P)
      [instantiatedObs ⟨0⟩ w.exportMap] .unit (w.ready shared addr) := by
  obtain ⟨sc, defs, exports⟩ := definitionRun data
  have noImport : NoImport w.component := by
    intro definition member name desc
    simp only [DirectWire.component, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h <;> rw [h] <;> intro h <;> cases h
  have complete : argsComplete w.component ([] : Exports (core3P P)) = true := by
    rw [argsComplete, importNames_nil noImport]
    rfl
  have root : TRuns (instantiateRootCall w.component [] : Canon.P (core3P P) Unit _)
      { initial P with store := DispatchSt.incNestingSt (initial P).store }
      (⟨0⟩, sc.exports)
      { w.ready shared addr with store := { (w.ready shared addr).store with nestingDepth := 1 } } := by
    unfold instantiateRootCall instantiateRoot
    refine (trapIf_run ((congrArg (!·) complete).trans rfl) _ _).bind ((TRuns.getStore _).bind ?_)
    refine (checkImport_run (precheckImports_ok _ [] _ _ noImport) _).bind
      ((TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} _).bind ?_)
    unfold instantiateComponent
    exact (defs.bind (f := fun sc => pure sc.exports) (TRuns.pure _ _)).bind
      (f := fun es => pure ((⟨0⟩ : InstId), es)) (TRuns.pure _ _)
  unfold instantiateProg
  refine SRuns.bind (os₁ := []) (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _) ?_
  refine SRuns.bind (os₁ := []) root ?_
  dsimp only
  rw [exports]
  exact SRuns.bind (os₁ := []) (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)
    (.emit (.pure _ _))

private theorem readyRun {w : DirectWire} {P : Profile} {shared : Store (CanonHost (core3P P))}
    {addr : Nat} (prof : ProfileKind) (data : w.Prepared P shared addr) :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ w.exportMap] ∧
      DetRunL prof (refHost P).hr (D P)
        { initial P with ctl := [.ofProg none (StepDefs.runProg (instantiateProg w.component []))] }
        tr (w.ready shared addr) := by
  obtain ⟨tr, quiet, obs, run⟩ := (programRun data).detRunL (prof := prof) (hr := (refHost P).hr)
    (dispatch := D P) rfl none (fun _ => pure .unit) [] []
  have done : UniqueStep prof (refHost P).hr (D P)
      { w.ready shared addr with ctl := [⟨none, .prog (pure .unit), []⟩] } .tau
      (w.ready shared addr) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨tr ++ [.tau], ?_, ?_, run.trans (.cons rfl done (.refl rfl))⟩
  · intro label member
    rcases List.mem_append.1 member with before | last
    · exact quiet label before
    · exact .inl (List.mem_singleton.1 last)
  · rw [traceObs_append, obs]
    rfl

private theorem noHostEvent {E : CoreEngine} {σ : Type} {tr : List (Label E σ)} (quiet : SRuns.Quiet tr)
    (event : HostEvent E σ) : Label.host event ∉ tr := by
  intro member
  rcases quiet _ member with h | ⟨_, h⟩ <;> cases h

theorem instantiates_iff {w : DirectWire} {P : Profile} {shared : Store (CanonHost (core3P P))}
    {addr : Nat} {prof : ProfileKind} {cfg : Machine.Config (core3P P) Unit} {owner : InstId}
    {exports : List (String × FuncId)} (data : w.Prepared P shared addr) :
    Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports ↔
      cfg = w.ready shared addr ∧ owner = ⟨0⟩ ∧ exports = w.exportMap := by
  obtain ⟨tr, quiet, obs, ready⟩ := readyRun prof data
  have decode : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, w.exportMap) := by
    rw [obs, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
  constructor
  · rintro ⟨actual, steps, noHost, ended, _, decoded⟩
    obtain ⟨_, start, run⟩ := Machine.Steps.cons_iff.1 steps
    obtain ⟨rfl, configEq⟩ := detRunL_end ready quiet rfl ((hostRun_inv start) ▸ run) noHost (.inl ended)
    have ids := Option.some.inj (decoded.symm.trans decode)
    exact ⟨configEq, (Prod.mk.inj ids).1, (Prod.mk.inj ids).2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨tr, .cons (.hostRun ⟨rfl, rfl, rfl⟩) ready.toDetRun.steps, noHostEvent quiet, rfl, rfl, decode⟩

theorem terminalReadbackOfInstantiation {w : DirectWire} {P : Profile} {I : ScalarInstance}
    {shared : Store (CanonHost (core3P P))} {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val}
    {question : I.F.Op} {prof : ProfileKind} {cfg final : Machine.Config (core3P P) Unit}
    {owner : InstId} {exports : List (String × FuncId)} {func : FuncId} {call : Nat} {out : CallOutcome}
    (data : w.Prepared P shared (I.addr question.1)) (abi : Boundary I shared x args question)
    (signature : w.liftType = liftedFt x)
    (init : Instantiates prof (refHost P).hr (D P) (initConfig ()) w.component [] cfg owner exports)
    (named : exports.lookup x.name = some func)
    (ran : Calls prof (refHost P).hr (D P) cfg ⟨call⟩ func (args.map toRefVal) final out) :
    ∃ (core : Execution.Core.Config Nat) (result : Result) (answer : I.F.Ar question),
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
      answer.toResult = result ∧ Reports x out result ∧
      core.store = Store.mapH (fun _ => 0) final.store.core ∧
      I.Activation P (Store.mapH (fun _ => 0) shared)
        [.inr (.ask question), .inr (.ans question answer)] core.store := by
  obtain ⟨rfl, rfl, rfl⟩ := (instantiates_iff data).1 init
  have functionZero : func = ⟨0⟩ := by
    simp only [DirectWire.exportMap, List.lookup_cons] at named
    split at named
    · exact (Option.some.inj named).symm
    · cases named
  subst func
  have fresh : Garb.Fresh (emptyGarb P) call := by
    constructor <;> intro item member <;> cases member
  refine terminalReadback abi (.inl rfl) fresh ⟨⟨0⟩, named, ?_, ran⟩
  change some (CFuncInst.lifted (E := core3P P) (I.addr question.1) w.liftType {} ⟨0⟩) = _
  rw [signature]

end Silmaril.Proofs.Wasm.Component.Reference.DirectLift
