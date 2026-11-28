module

import Silmaril.Wasm.Component.Reference.SyncImportCut.Thms
import Silmaril.Wasm.Component.Reference.Litmus.Thms
import Silmaril.Wasm.Game.Machine.Thms

open Silmaril.Elgot
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store Val vals)
open Silmaril.Wasm.SingleThreaded (decompose? decompose?_top decompose?_vals_nil
  hostArity? neverFail ofFlat profile)

namespace SyncImportCutRegression

private def ready : Ready fwdS where
  good := fwdS_good
  arity := by simp [SimpleI.Arity, fwdS, ValTy.flatList, ValTy.flat]
  floatFree := by simp [SimpleI.FloatFree, fwdS, floatFreeList, floatFree]
  inst := fwdInst
  isInst := fwd_isInst

private def ask : Question fwdS.imports := ⟨⟨0, by decide⟩, ⟨[.u32 3], rfl⟩⟩
private def exportAsk : Question (exportIface fwdS) := ⟨⟨0, by decide⟩, ⟨[.u32 3], rfl⟩⟩

private def exportOp : ready.inst.F.Op :=
  ⟨⟨0, by decide⟩, ⟨[Val.i32 3], .cons ⟨3, rfl⟩ .nil⟩⟩

local notation "E" => core3P (profile neverFail)
private def ty := witFt fwdS.imports[0].2
private def lower : CanonHost E := .lowered ⟨0⟩ ty {} ⟨0⟩
private def store : Store (CanonHost E) :=
  let ft := fwdS.imports[0].2.flat
  (Silmaril.Wasm.SingleThreaded.allocHost {} ⟨ft.params, ft.results⟩ lower).1

-- The local state at the forwarded import, with the owner and host function installed.
private noncomputable def runCfg : Config E Nat where
  host := 10
  store := {
    core := store
    insts := [{}]
    funcs := [.host ty ⟨0⟩]
    tasks := [{ ft := ty, opts := {}, inst := ⟨0⟩, caller := ⟨0⟩ }]
    threads := [{ task := ⟨0⟩, status := .running }] }
  ctl := [⟨some ⟨0⟩, .core (ready.inst.initThread exportOp) (fun rs => .pure (.flat rs)), []⟩]

private theorem at_callout :
    (E).status runCfg.store.core (ready.inst.initThread exportOp) = .callout lower [Flat.i32 3] := by
  let thread := ready.inst.initThread exportOp
  have ha : hostArity? store 0 = some (lower, 1) := rfl
  have hd : decompose? store (thread.config store).code =
      some (.top [] [], 0, lower, [Val.i32 3]) := by
    change decompose? store
      (vals ([Val.i32 3] ++ [.ref (.func 0)]) ++
        [.callRefType ((store.funcs[0]?.map Silmaril.Wasm.Execution.Core.FuncInst.type).getD default)]) = _
    rw [decompose?_top (pre := [Val.i32 3]) (n := 1) (by rfl) ha (Nat.le_refl 1)]
    rfl
  have hv : ¬ ∃ vs, (thread.config store).code = vals vs := by
    rintro ⟨vs, h⟩
    rw [h, decompose?_vals_nil] at hd
    cases hd
  have ht : (thread.config store).code ≠ [.trap] := by intro h; cases h
  have he : ¬ ∃ a, (thread.config store).code = Silmaril.Wasm.Execution.Core.throwing a := by
    rintro ⟨a, h⟩
    cases h
  change flatStatus (statusP (profile neverFail) store thread) = _
  simp only [statusP, hv, ht, he, dite_false, ite_false, hd]
  rfl

private noncomputable def cut : ReferenceCut (o := neverFail) runCfg ask where
  owner := some ⟨0⟩
  thread := ready.inst.initThread exportOp
  returnTo := fun rs => .pure (.flat rs)
  frames := []
  resumers := []
  flatArgs := [.i32 3]
  focused := rfl
  status := at_callout
  flatTypes := rfl
  lifted := rfl

private theorem canDispatch : cut.CanDispatch := ⟨rfl, rfl, ⟨{}, rfl, rfl⟩, rfl⟩

private def result : Values fwdS.imports[ask.index].2.results := ⟨[.u32 13], rfl⟩

private noncomputable def host := answerHostS (profile neverFail) fwdC

-- With the stock host at state 10, the visible request gets 13 and the same
-- parked Core segment resumes. The proof uses only the public cut lemmas.
example :
    Sees (tree neverFail ready exportAsk exportOp (refCursor runCfg cut.thread)) [] (.pending ask) ∧
    ∃ tr resolved next,
      Steps Core3Adder.first.prof host.hr host.dispatch runCfg (.tau :: tr) resolved ∧
      Step Core3Adder.first.prof host.hr host.dispatch resolved .tau next ∧
      next.host = 11 ∧ refCursor next (cut.resume (some result)).2 = cut.resume (some result) ∧
      next.ctl = [⟨cut.owner, .core (cut.resume (some result)).2 cut.returnTo, cut.frames⟩] := by
  obtain ⟨seen, park⟩ := cut.request (r := ready) (q := exportAsk) (f := exportOp)
    cut.focused (.refl runCfg) (host := host) (prof := Core3Adder.first.prof) (by simp)
  obtain ⟨tr, resolved, next, run, _, pop, state, core, ctl⟩ :=
    cut.answer ready canDispatch result (g := fwdC) (s' := 11) (prof := Core3Adder.first.prof) rfl
  refine ⟨sees_iff.mpr (.pending seen), tr, resolved, next, .cons park run, pop, state, ?_, ctl⟩
  simp only [refCursor, core, ReferenceCut.resume]

-- Refusal under answerHostS takes a lockdown step from the same parked segment.
example :
    let refuse := answerHostS (profile neverFail) (σ := Nat) (fun _ _ _ => none)
    ∃ tr pre reason,
      Steps Core3Adder.first.prof refuse.hr refuse.dispatch runCfg (.tau :: tr) pre ∧
      Step Core3Adder.first.prof refuse.hr refuse.dispatch pre (.trap reason) (trapCfg pre) ∧
      (trapCfg pre).store.lockdown = true ∧ (trapCfg pre).ctl = [] := by
  let refuse := answerHostS (profile neverFail) (σ := Nat) (fun _ _ _ => none)
  have park := (cut.request (r := ready) (q := exportAsk) (f := exportOp)
    cut.focused (.refl runCfg) (host := refuse) (prof := Core3Adder.first.prof) (by simp)).2
  obtain ⟨tr, pre, reason, run, trap⟩ :=
    cut.refuses ready canDispatch (g := fun _ _ _ => none) (prof := Core3Adder.first.prof) rfl
  exact ⟨tr, pre, reason, .cons park run, trap, rfl, rfl⟩

end SyncImportCutRegression
