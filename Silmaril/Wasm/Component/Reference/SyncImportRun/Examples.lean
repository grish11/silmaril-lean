module

import Silmaril.Wasm.Component.Reference.SyncImportRun.Thms
import Silmaril.Wasm.Component.Reference.SyncImportRun.Fixture.Thms
import Silmaril.Wasm.Component.Reference.Litmus.Thms

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Component.Reference.SyncImportRun.Fixture
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH)
open Silmaril.Wasm.SingleThreaded (neverFail profile)
open Silmaril.Games.Abstract (Call)

private def ready : Ready fwdS where
  good := fwdS_good
  arity := by simp [SimpleI.Arity, fwdS, ValTy.flatList, ValTy.flat]
  floatFree := by simp [SimpleI.FloatFree, fwdS, floatFreeList, floatFree]
  inst := fwdInst
  isInst := fwd_isInst

private def exportAsk : Question (exportIface fwdS) := ⟨⟨0, by decide⟩, ⟨[.u32 3], rfl⟩⟩

private def result := [toRefVal (.u32 13)]

private theorem counter_steps {s t : Nat} {cs : List (Call (signature fwdS.imports))}
    (run : HostReplies (c := fwdS) fwdC s cs t) : t = s + cs.length := by
  induction run with
  | nil => simp
  | @cons s s' s'' m a cs reply _ ih =>
    have step : s' = s + 1 := by
      unfold fwdC at reply
      split at reply
      · exact (Prod.mk.inj (Option.some.inj reply)).2.symm
      · cases reply
    simp only [List.length_cons]
    omega

-- The stock dispatcher instantiates fwdS and invokes f(3). The counter host starts at 10,
-- answers the import with 13 and leaves state 11. The ITree has one answered import on
-- its returning path and its result carries the reached machine Core store.
example :
    ∃ (finished : Config (core3P (profile neverFail)) Nat)
      (a : Values (exportIface fwdS)[exportAsk.index].2.results)
      (cs : List (Call (signature fwdS.imports))),
      finished.host = 11 ∧ a.val.map toRefVal = result ∧ cs.length = 1 ∧
      HostReplies (c := fwdS) fwdC 10 cs finished.host ∧
      Sees ((body neverFail ready exportAsk).run ⟨ready.inst.store⟩).run cs
        (.reply (some a) (Store.mapH trampIdx finished.store.core)) := by
  obtain ⟨_, finished, _, _, init, lookup, run, host⟩ := fwd_reference_calls
  obtain ⟨a, cs, returned, replies, seen⟩ := sees_of_reference_return (o := neverFail)
    ready fwdS_inst exportAsk fwdC_ok init lookup run
  refine ⟨finished, a, cs, host, returned, ?_, replies, seen⟩
  have count := counter_steps replies
  omega
