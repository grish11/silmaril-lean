module

public import Silmaril.Process.ITreeTrace.Exact.Defs
public import Silmaril.Semantics.ExactITree.Thms

public section

namespace Silmaril.Process.ITreeTrace.Exact.Proofs

open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Exact (Path Step Finish Observes)

variable {sig : TypedSyscall.Signature} {S Label A : Type}
variable {K : TypedSyscall.Kernel sig S Label}

private theorem singleton_update (pool : Pool sig Unit A) (next : Program sig A) :
    Function.update pool () next = singleton next := by
  funext tid
  cases tid
  exact Function.update_self ..

private theorem path_of_flatten {schedule : List Unit} {pool : Pool sig Unit A}
    {before after : S} {log : List Label} {stop : End sig Unit A} {value : A}
    (run : Flatten K (fun _ l => l) schedule pool before log stop after)
    (returned : stop = .returned (fun _ => value)) :
    Path (kernel K) () (pool (), before) log (ret value, after) ∧ log.length ≤ schedule.length := by
  induction run with
  | returned done =>
    cases returned
    have tree := out_injective ((done ()).trans (out_ret _).symm)
    simp only [tree]
    exact ⟨.nil _, Nat.zero_le _⟩
  | exhausted | silent | blocked | exited => cases returned
  | @exchange tid schedule pool before req next label reply after trace stop final root completion _ ih =>
    cases tid
    have head : pool () = vis (.call req) next := out_injective (root.trans (out_vis _ _).symm)
    obtain ⟨tail, bound⟩ := ih returned
    rw [singleton_update] at tail
    have step : Step (kernel K) () (pool (), before) [label] (next reply, after) := by
      simp only [head, Step, Silmaril.Elgot.ITree.Exact.root_vis]
      exact ⟨reply, ⟨label, rfl, completion⟩, rfl⟩
    exact ⟨.cons step tail, Nat.succ_le_succ bound⟩
  | skip _ _ _ ih =>
    obtain ⟨path, bound⟩ := ih returned
    exact ⟨path, Nat.le_succ_of_le bound⟩

private theorem flatten_of_path {start finish : Silmaril.Elgot.ITree.Exact.Config
      (profile S Label) (eventSignature sig) A} {log : List Label}
    (path : Path (kernel K) () start log finish)
    {fuel : Nat} {value : A} (returned : finish.1 = ret value) (bound : log.length ≤ fuel) :
    Sequential K fuel start.1 start.2 log (.returned fun _ => value) finish.2 := by
  induction path generalizing fuel with
  | nil s =>
    exact .returned (fun _ => by simp [singleton, returned])
  | @cons start mid finish batch trace step _ ih =>
    rcases start with ⟨prog, before⟩
    rcases cases_visible prog with rfl | ⟨a, rfl⟩ | ⟨R, event, next, rfl⟩
    · simp only [Step, Silmaril.Elgot.ITree.Exact.root_diverge] at step
      obtain ⟨rfl, rfl⟩ := step
      exact ih returned bound
    · simp [Step] at step
    · cases event with
      | call req =>
        simp only [Step, Silmaril.Elgot.ITree.Exact.root_vis] at step
        obtain ⟨reply, completion, tree⟩ := step
        obtain ⟨label, rfl, completed⟩ := completion
        cases fuel with
        | zero => simp at bound
        | succ fuel =>
          have tail := ih (fuel := fuel) returned (Nat.le_of_succ_le_succ bound)
          rw [tree] at tail
          refine Flatten.exchange (tid := ()) (out_vis _ _) completed ?_
          rw [singleton_update]
          exact tail

private theorem finish_returned {prog : Program sig A} {before after : S} {value : A}
    {batch : List Label} :
    Finish (kernel K) () (prog, before) batch (.returned value after) ↔
      batch = [] ∧ (prog, before) = (ret value, after) := by
  rcases cases_visible prog with rfl | ⟨a, rfl⟩ | ⟨R, event, next, rfl⟩
  · simp [Finish, show (diverge : Program sig A) ≠ ret value from by
      intro h
      simpa using congrArg out h]
  · simp [Finish, eq_comm]
  · simp [Finish, show vis event next ≠ ret value from by
      intro h
      simpa using congrArg out h]

theorem returned_iff_sequential {prog : Program sig A} {before after : S} {log : List Label}
    {value : A} {fuel : Nat} :
    Sequential K fuel prog before log (.returned fun _ => value) after ↔
      Observes (kernel K) () (prog, before) (.finished log (.returned value after)) ∧
        log.length ≤ fuel := by
  constructor
  · intro run
    obtain ⟨path, bound⟩ := path_of_flatten run rfl
    exact ⟨⟨log, (ret value, after), [], path, finish_returned.mpr ⟨rfl, rfl⟩,
      (List.append_nil _).symm⟩, by simpa using bound⟩
  · rintro ⟨⟨word, ⟨next, store⟩, batch, path, done, rfl⟩, bound⟩
    obtain ⟨rfl, eq⟩ := finish_returned.mp done
    cases eq
    simp only [List.append_nil] at bound ⊢
    exact flatten_of_path path rfl bound

end Silmaril.Process.ITreeTrace.Exact.Proofs
