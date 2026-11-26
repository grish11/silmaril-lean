module

public import Silmaril.Process.AbstractIO.Exact.Defs
public import Silmaril.Semantics.ExactITree.Thms
import Silmaril.Process.AbstractIO.Thms

public section

namespace Silmaril.Process.AbstractIO.Exact.Proofs

open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Exact (Kernel Observes Satisfies Step Finish satisfies_lower)
open Silmaril.Elgot.ITree.Exact.Signature.Hom (lower_vis lower_ret)
open ITreeTrace (Event)
open ITreeTrace.Exact (lowering)

theorem lower_positionedCopy (src dst : FilePosition) (count : Nat) :
    (lowering positionedCalls).lower (positionedCopy src dst count) =
      fileAPI.map (trigger (Event.call (sig := fileSignature) (.copyChunk src dst count))) := by
  rw [fileAPI.map_trigger]
  change (lowering positionedCalls).lower (positionedCopy src dst count) = copyChunk src dst count
  rw [positionedCopy, lower_vis, copyChunk, call_bind]
  congr 1
  funext reply
  cases reply with
  | error errno => exact lower_ret _ _
  | ok bytes =>
    cases bytes with
    | nil => exact lower_ret _ _
    | cons byte bytes =>
      change (lowering positionedCalls).lower
        (vis (Event.call (sig := positionedSignature) (.write dst (byte :: bytes))) ret) =
        call (.pwrite dst.fd dst.offset (byte :: bytes))
      rw [lower_vis]
      exact congrArg (vis _) (funext fun _ => lower_ret _ _)

theorem lower_network_call (req : NetworkRequest) :
    (lowering networkCalls).lower (trigger (Event.call (sig := networkSignature) req)) =
      networkAPI.map (trigger (Event.call (sig := networkSignature) req)) := by
  rw [networkAPI.map_trigger]
  cases req with
  | receiveChunk fd count =>
    change (lowering networkCalls).lower (vis (Event.call (sig := networkSignature) (.receiveChunk fd count)) ret) = call (.recv fd count)
    rw [lower_vis]
    exact congrArg (vis _) (funext fun _ => lower_ret _ _)
  | sendChunk fd bytes =>
    change (lowering networkCalls).lower (vis (Event.call (sig := networkSignature) (.sendChunk fd bytes)) ret) = sendChunk fd bytes
    rw [lower_vis, sendChunk, call_bind]
    congr 1
    funext reply
    cases reply with
    | error errno => exact lower_ret _ _
    | ok result => cases result <;> exact lower_ret _ _

theorem copy_satisfies_iff (src dst : FilePosition) (count : Nat) (pre : Store → Prop)
    (post : Store → Silmaril.Elgot.ITree.Exact.Observation profile (IOResult Nat) → Prop) :
    (∀ before, pre before → ∀ obs,
      Observes linuxKernel ()
        (fileAPI.map (trigger (Event.call (sig := fileSignature) (.copyChunk src dst count))), before) obs →
      post before obs) ↔
    Satisfies (Kernel.reduct (lowering positionedCalls) linuxKernel)
      (copySentence src dst count pre post) := by
  rw [← satisfies_lower]
  simp only [Satisfies, Silmaril.Elgot.ITree.Exact.Sentence.lower, copySentence, lower_positionedCopy]
  exact ⟨fun h ⟨⟩ => h, fun h => h ()⟩

theorem call_step_iff {A : Type} {req : signature.Request} {before after : Store}
    {batch : List Observation} {next : signature.Response req → Prog A} {tree : Prog A} :
    Step linuxKernel () (vis (Event.call (sig := signature) req) next, before) batch (tree, after) ↔
      ∃ choice, batch = [⟨req, (step choice before req).1⟩] ∧
        after = (step choice before req).2 ∧ tree = next (step choice before req).1 := by
  simp only [Step, Silmaril.Elgot.ITree.Exact.root_vis]
  constructor
  · rintro ⟨reply, ⟨label, rfl, completion⟩, rfl⟩
    obtain ⟨choice, rfl, eq⟩ := completion
    cases eq
    exact ⟨choice, rfl, rfl, rfl⟩
  · rintro ⟨choice, rfl, rfl, rfl⟩
    exact ⟨_, ⟨_, rfl, step_completion choice before req⟩, rfl⟩

theorem finish_iff {A : Type} {prog : Prog A} {before : Store} {batch : List Observation}
    {last : Silmaril.Elgot.ITree.Exact.End profile A} :
    Finish linuxKernel () (prog, before) batch last ↔
      ∃ value, prog = ret value ∧ batch = [] ∧ last = .returned value before := by
  rcases cases_visible prog with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
  · simp [Finish, Ne.symm (ret_ne_diverge (E := Event signature) (A := A) _)]
  · simp [Finish]
  · cases e with
    | call req =>
      have enabled : ∃ c, linuxKernel () before (Event.call (sig := signature) req) c :=
        ⟨.reply (step 0 before req).1 (step 0 before req).2 [⟨req, (step 0 before req).1⟩],
          ⟨_, rfl, step_completion 0 before req⟩⟩
      simp only [Finish, Silmaril.Elgot.ITree.Exact.root_vis, enabled, not_true_eq_false, false_and,
        false_or]
      constructor
      · rintro ⟨reason, store, ⟨after, label, _, _, completion⟩, _⟩
        obtain ⟨_, _, eq⟩ := completion
        cases eq
      · rintro ⟨value, eq, _⟩
        exact (ret_ne_vis value _ _ eq.symm).elim

end Silmaril.Process.AbstractIO.Exact.Proofs
