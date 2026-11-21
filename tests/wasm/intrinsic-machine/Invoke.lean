module

import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Session
import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Wasm.Game.Machine.Thms
import Silmaril.Games.Abstract.StratThread.Thms
import Silmaril.Wasm.SingleThreaded.Agreement

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

private def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
private def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)
private theorem closedOk : TyOk {} closed := TyOk.check_sound (by decide +kernel)
private theorem expands : Expand closed (.func (.cons .i32 .nil) .nil) := Expand.iff.mpr rfl

private def body (extra : Bool) : Code [.i32] [] [] :=
  if extra then .seq (.localGet .here (by decide)) (.seq .unreachable .done) else .seq .unreachable .done

private def raw (extra : Bool) : Func := ⟨⟨0⟩, [], (body extra).erase⟩
private def calleeInst : ModuleInst := { types := [closed] }
private def calleeContext : Context := { types := [closed] }
private def entry (extra : Bool) : FuncInst Nat := ⟨closed, calleeInst, .wasm (raw extra)⟩
private def store (versions : List Bool) : Store Nat := { funcs := versions.map entry }

private theorem calleeOk (versions : List Bool) : ModuleInstOk (store versions) calleeInst calleeContext :=
  ModuleInstOk.mk (k := 0) (by simpa [calleeInst] using closedOk) .nil .nil .nil .nil .nil
    (by simp [calleeInst]) .nil (by simp [calleeInst]) (by simp [calleeInst]) (by simp [calleeInst]) (by simp)

private theorem storeOk (versions : List Bool) : StoreOk (store versions) := by
  constructor <;> try (solve | simp [store])
  intro fn membership
  obtain ⟨extra, _, rfl⟩ := List.mem_map.mp membership
  have codeOk : FuncOk calleeContext (raw extra) closed := .mk rfl expands .nil ((body extra).sound rfl)
  exact .wasm closedOk (calleeOk versions) rfl codeOk (Sub.refl _ (k := .def) trivial closed)

private def callerContext : Context := { funcs := [closed] }

private def caller (versions : List Bool) (address : Nat) (extra : Bool)
    (found : versions[address]? = some extra) : World Nat callerContext where
  store := store versions
  moduleInst := { funcs := [address] }
  storeOk := storeOk versions
  moduleOk := ModuleInstOk.mk (k := 0) (by simp) .nil .nil
    (.cons (ExternAddrOk.func (fi := entry extra) (by simp [store, found])) .nil) .nil .nil
    (by simp) .nil (by simp) (by simp) (by simp) (by simp)

private def call (versions : List Bool) (address : Nat) (extra : Bool)
    (found : versions[address]? = some extra) : DirectCall (caller versions address extra found) [.i32] [] :=
  ⟨⟨0⟩, address, entry extra, [], ⟨0⟩, body extra, calleeContext, calleeOk versions,
    rfl, by simp [caller, store, found], expands, rfl⟩

private theorem traps {versions : List Bool} {address : Nat} {extra : Bool}
    (found : versions[address]? = some extra) (args : Values [.i32]) :
    (call versions address extra found).runFor args 3 = some none := by
  cases args with
  | cons bits tail => cases tail; cases extra <;> rfl

example : raw false ≠ raw true := by
  intro equal
  have length := congrArg (fun fn : Func => fn.body.length) equal
  exact (by decide : (1 : Nat) ≠ 2) length

example : FunEquiv Eq (profile neverFail) noHost (store [false, true]) 0 1 :=
  ((call [false, true] 0 false rfl).entry_eq (call [false, true] 1 true rfl)
    fun args => ⟨3, 3, none, traps rfl args, traps rfl args⟩).funEquiv

example : ModuleEquiv Eq (profile neverFail) noHost (store [false]) (store [true]) := by
  apply EntryAgreement.moduleEquiv
  intro address accepted
  cases address with
  | zero =>
    exact (call [false] 0 false rfl).entry_eq (call [true] 0 true rfl)
      fun args => ⟨3, 3, none, traps rfl args, traps rfl args⟩
  | succ address =>
    obtain ⟨_, left | right⟩ := accepted
    · obtain ⟨_, _, _, found, _, _⟩ := left
      simp [store] at found
    · obtain ⟨_, _, _, found, _, _⟩ := right
      simp [store] at found

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Wasm.Game Silmaril.Wasm.Component
  Silmaril.Wasm.Component.Reference Silmaril.Wasm.Abstract.InstSession

private def observed : NumInstance :=
  ⟨⟨[], [⟨[.num (.int .i32)], []⟩], [0], store [false]⟩,
    [], [("run", ⟨[.int .i32], []⟩)], rfl, rfl⟩

private theorem stores_distinct : store [false] ≠ store [true] := by
  intro equal
  have shape := congrArg (fun s : Store Nat => s.funcs.map fun fn => match fn.code with
    | .wasm code => code.body.length
    | .host _ => 0) equal
  exact (by decide : ([1] : List Nat) ≠ [2]) shape

private theorem noImport (op : observed.inst.E.Op) : False := Fin.elim0 op.1

private theorem noLog (log : List (Call observed.inst.E)) : log = [] := by
  cases log with
  | nil => rfl
  | cons first _ => exact (noImport first.1).elim

private def exportZero : Fin observed.inst.exports.length := ⟨0, by decide +kernel⟩

private theorem observedOk (version : Bool) : observed.inst.WellFormed (store [version]) where
  storeOk := storeOk _
  addrs_length := rfl
  export_type := by
    intro slot
    have only : slot = exportZero := Fin.eq_zero (show Fin 1 from slot)
    subst slot
    exact ⟨entry version, rfl, expands⟩
  host_type := by
    intro address fn host found kind
    cases address with
    | zero => have equal : entry version = fn := Option.some.inj found; cases equal; cases kind
    | succ address => simp [store] at found

private theorem observedArgs (question : observed.inst.F.Op) :
    ∃ args : Values [.i32], question.2.val = args.erase := by
  obtain ⟨slot, values, typed⟩ := question
  have only : slot = exportZero := Fin.eq_zero (show Fin 1 from slot)
  subst slot
  cases typed with
  | cons head tail =>
    cases tail
    obtain ⟨bits, rfl⟩ := head
    exact ⟨.cons bits .nil, rfl⟩

private theorem trapReach (version : Bool) (question : observed.inst.F.Op) :
    ∃ final, Reach (profile neverFail) (store [version], observed.inst.initThread question)
      (store [version], final) ∧ ResultAt (store [version]) final .trap := by
  obtain ⟨args, equal⟩ := observedArgs question
  have only : question.1 = exportZero := Fin.eq_zero (show Fin 1 from question.1)
  have loaded : (observed.inst.initThread question).config (store [version]) =
      invoke (store [version]) 0 args.erase := by
    simp only [ScalarInstance.initThread, Thread.config, ScalarInstance.addr, equal, only]
    rfl
  let resolved := call [version] 0 version rfl
  have steps : Steps (profile neverFail) noHost (invoke (store [version]) 0 args.erase)
      ⟨store [version], {}, [.trap]⟩ := resolved.invoke_sound args 3 (traps rfl args)
  rw [← loaded] at steps
  have liftSteps {dest : Config Nat}
      (path : Steps (profile neverFail) noHost ((observed.inst.initThread question).config (store [version])) dest) :
      ∃ nextStore nextThread, Reach (profile neverFail) (store [version], observed.inst.initThread question)
        (nextStore, nextThread) ∧ nextThread.config nextStore = dest := by
    induction path with
    | refl => exact ⟨_, _, .refl, rfl⟩
    | @tail _ next _ step extension =>
      obtain ⟨nextStore, nextThread, previous, rfl⟩ := extension
      exact ⟨next.store, .active next.frame next.code, previous.tail ⟨_, _, rfl, step⟩, rfl⟩
  obtain ⟨nextStore, final, run, loadedFinal⟩ := liftSteps steps
  have retained : nextStore = store [version] := by
    simpa only [Thread.config_store] using congrArg Config.store loadedFinal
  subst nextStore
  exact ⟨final, run, congrArg Config.code loadedFinal⟩

private theorem noDivergence (version : Bool) (question : observed.inst.F.Op) :
    ¬ Silmaril.Wasm.Abstract.InstStrat.Diverges (profile neverFail)
      (store [version], observed.inst.initThread question) := by
  obtain ⟨args, equal⟩ := observedArgs question
  have only : question.1 = exportZero := Fin.eq_zero (show Fin 1 from question.1)
  intro ⟨trace, starts, steps⟩
  have finite : ¬ Execution.Core.Diverges (profile neverFail) noHost (invoke (store [version]) 0 args.erase) :=
    (call [version] 0 version rfl).invoke_not_diverges args (traps rfl args)
  apply finite
  refine ⟨fun step => (trace step).2.config (trace step).1, ?_, ?_⟩
  · dsimp only
    rw [starts]
    simp only [ScalarInstance.initThread, Thread.config, ScalarInstance.addr, equal, only]
    rfl
  · intro step
    dsimp only
    obtain ⟨frame, code, active, actual⟩ := steps step
    rw [active]
    exact actual

private theorem trapResultOnly {result : Result} (equal : result.toAdmin = [.trap]) : result = .trap := by
  cases result with
  | trap => rfl
  | throw => cases equal
  | values values =>
    have invalid := congrArg (fun code : List Admin => code.all Admin.isVal) equal
    simp [Result.toAdmin, Admin.isVal, Admin.val?] at invalid

private theorem finished (version : Bool) (question : observed.inst.F.Op)
    (log : List (Call observed.inst.E)) (ending : End (Store Nat) (Res observed.inst.exports ⊕ PUnit)) :
    (log, ending) ∈ instFinS observed.inst (profile neverFail) (store [version]) question ↔
      ending = .ret (.inr ()) (store [version]) := by
  obtain rfl := noLog log
  obtain ⟨final, run, trap⟩ := trapReach version question
  constructor
  · rintro (⟨answer, nextStore, rfl, moves⟩ | ⟨rfl, nextStore, next, moves, div⟩)
    · change observed.inst.Path _ _ [.inr (.ask question), .inr (.ans question answer)] _ at moves
      cases moves with
      | cons asks subsequent =>
        cases asks
        cases subsequent with
        | cons answers stop =>
          cases stop
          cases answers with
          | oret returning result typed =>
            have same := reach_normal_unique returning run (resultAt_no_internal result) (resultAt_no_internal trap)
            cases same
            have isTrap := trapResultOnly (result.symm.trans trap)
            subst isTrap
            cases Option.some.inj typed
            rfl
    · change observed.inst.Path _ _ [.inr (.ask question)] _ at moves
      cases moves with
      | cons asks stop =>
        cases asks
        cases stop
        exact (noDivergence version question div).elim
  · rintro rfl
    exact Or.inl ⟨.trap, _, rfl, .cons (.call _ _) (.cons (.oret run trap rfl) (.nil _))⟩

private def pair (left right : Store Nat) : Prop := left = store [false] ∧ right = store [true]

private theorem round {left right : Store Nat} (related : pair left right) :
    RoundEq (instTripleS observed.inst (profile neverFail)) (instTripleS observed.inst (profile neverFail))
      pair left right := by
  obtain ⟨rfl, rfl⟩ := related
  constructor
  · intro question log
    simp [instTripleS, finished]
  · intro question log
    simp [instTripleS, finished]
  · funext question
    ext ⟨log, op⟩
    exact (noImport op).elim
  · funext question
    ext stream
    exact (noImport (stream 0).1).elim
  · intro question log answer nextStore returned
    have same := (finished false question log _).mp returned
    obtain ⟨rfl, rfl⟩ := End.ret.inj same
    exact ⟨_, (finished true question log _).mpr rfl, rfl, rfl⟩
  · intro question log answer nextStore returned
    have same := (finished true question log _).mp returned
    obtain ⟨rfl, rfl⟩ := End.ret.inj same
    exact ⟨_, (finished false question log _).mpr rfl, rfl, rfl⟩

open Classical in
private noncomputable def replacement (instance_ : NumInstance) : Store Nat :=
  if instance_ = observed then store [true] else instance_.inst.store

open Classical in
private def invariant (instance_ : NumInstance) : Store Nat → Store Nat → Prop :=
  if instance_ = observed then pair else Eq

private theorem component_replacement (component : Comp NumInstance) :
    component.denUD (core3SemD (profile neverFail)) =
      component.denUD (threadSemSD fun instance_ =>
        instSession instance_.inst (profile neverFail) (replacement instance_)) := by
  apply denUD_core3SemD_eq_of_related_stores neverFail replacement invariant
  · intro instance_
    by_cases same : instance_ = observed
    · subst instance_; simp [invariant, replacement, pair, observed]
    · simp [invariant, replacement, same]
  · intro instance_ left right rel
    by_cases same : instance_ = observed
    · subst instance_; simpa [invariant] using round (by simpa [invariant] using rel)
    · simp only [invariant, ite_eq_right same] at rel ⊢
      exact isBisim_eq left right rel

private def exampleComponent : Comp NumInstance :=
  let ft : FuncTy := ⟨[.u32], []⟩
  .mk [] [.core observed []] [⟨"run", ft, ⟨[.lift ft], .call 0⟩⟩]

example : exampleComponent.denUD (core3SemD (profile neverFail)) =
    exampleComponent.denUD (threadSemSD fun instance_ =>
      instSession instance_.inst (profile neverFail) (replacement instance_)) :=
  component_replacement exampleComponent

#print axioms stores_distinct
#print axioms observedOk
#print axioms round
#print axioms component_replacement
#print axioms DirectCall.invoke_sound
#print axioms DirectCall.invokeOk_iff
#print axioms DirectCall.invocations_eq_iff
#print axioms DirectCall.invoke_not_diverges
#print axioms DirectCall.entry_eq
#print axioms EntryAgreement.moduleEquiv
#print axioms Silmaril.Wasm.Abstract.InstSession.denUD_core3SemD_eq_of_related_stores
#print axioms Silmaril.Wasm.Abstract.InstSession.compEquiv_of_equal_replacement_sessions_iff
