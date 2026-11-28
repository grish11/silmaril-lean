module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Legacy.Defs
public import Silmaril.Machine.MulticoreVM.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Legacy

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.ThreadSync (Config Event)
open Silmaril.Machine.MulticoreVM.ThreadSync.Legacy
open Silmaril.Semantics.ConcurrentTrace (Letter LocalLetter Word mapWord)

universe u

variable {Thread Key Value Local Output : Type u}

private def liftFragment (fragment : Fragment Thread Output) :
    Fragment Thread (Event Thread Key Value Output) :=
  fragment.map (LocalLetter.map id Event.localOutput)

private theorem name_liftFragment (thread : Thread) (fragment : Fragment Thread Output) :
    nameFragment thread (liftFragment fragment) =
      (liftWord (Key := Key) (Value := Value) (nameFragment thread fragment)) := by
  simp only [nameFragment, liftFragment, liftWord, mapWord, List.map_map]
  congr 1
  funext letter
  cases letter <;> rfl

variable [DecidableEq Thread]

private theorem liftStore_update (words : Key → Value) (store : Store Thread Local)
    (thread : Thread) (next : Local) :
    (liftStore words store).put thread (.runnable next) =
      liftStore words (Function.update store thread (some next)) := by
  apply congrArg (Config.mk words)
  funext other
  change (if other = thread then some (ThreadSync.ThreadState.runnable next)
    else (store other).map _) = _
  rw [Function.update_apply]
  split <;> rfl

variable [DecidableEq Key] [DecidableEq Value]

private theorem exec_lift (localExec : LocalExec Thread Local Output) (words : Key → Value)
    (thread : Thread) (choice : PUnit) (store : Store Thread Local) :
    ThreadSync.exec (liftProgram localExec) thread [] (liftStore words store) =
      (exec localExec thread choice store).map
        (fun (next, fragment) => (liftStore words next, liftFragment fragment)) := by
  have slot : (liftStore words store).threads thread = (store thread).map .runnable := rfl
  cases atThread : store thread with
  | none => simp [ThreadSync.exec, exec, slot, atThread]
  | some localState =>
    cases nextStep : localExec thread localState with
    | none => simp [ThreadSync.exec, exec, slot, liftProgram, atThread, nextStep]
    | some result =>
      obtain ⟨next, output⟩ := result
      cases output <;>
        simp [ThreadSync.exec, exec, slot, liftProgram, atThread, nextStep, liftStore_update,
          liftFragment, LocalLetter.map]

theorem execute_lift (localExec : LocalExec Thread Local Output) (words : Key → Value)
    (schedule : Schedule Thread PUnit) (store : Store Thread Local) :
    execute (ThreadSync.exec (liftProgram localExec)) (liftSchedule schedule) (liftStore words store) =
      (execute (exec localExec) schedule store).map (liftOutcome words) := by
  induction schedule generalizing store with
  | nil => rfl
  | cons decision schedule ih =>
    simp only [liftSchedule, List.map_cons, execute, exec_lift (choice := decision.choice)]
    cases exec localExec decision.thread decision.choice store with
    | none => rfl
    | some result =>
      obtain ⟨next, fragment⟩ := result
      simp only [Option.map_some, bind, Option.bind]
      rw [show schedule.map (fun decision => ⟨decision.thread, []⟩) = liftSchedule schedule from rfl,
        ih]
      cases execute (exec localExec) schedule next with
      | none => rfl
      | some tail =>
        obtain ⟨final, word⟩ := tail
        simp [name_liftFragment, liftOutcome, liftWord, mapWord, List.map_append]

omit [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value] in
private theorem liftStore_injective (words : Key → Value) :
    Function.Injective (liftStore (Thread := Thread) (Local := Local) words) := by
  intro a b h
  funext thread
  have slots := congrArg (fun cfg : Config Thread Key Value Local => cfg.threads thread) h
  exact Option.map_injective (by intro x y eq; cases eq; rfl) slots

omit [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value] in
private theorem liftWord_injective :
    Function.Injective (liftWord (Thread := Thread) (Key := Key) (Value := Value) (Output := Output)) := by
  apply List.map_injective_iff.mpr
  intro x y h
  cases x <;> cases y <;> simp_all [Letter.map]

omit [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value] in
private theorem liftOutcome_injective (words : Key → Value) :
    Function.Injective (liftOutcome (Thread := Thread) (Local := Local) (Output := Output) words) :=
  fun _ _ h => Prod.ext (liftStore_injective words (congrArg Prod.fst h))
    (liftWord_injective (congrArg Prod.snd h))

theorem scheduled_lift_iff (localExec : LocalExec Thread Local Output) (words : Key → Value)
    (schedule : Schedule Thread PUnit) {initial final : Store Thread Local} {word : Word Thread Output} :
    Scheduled (ThreadSync.step (liftProgram localExec)) (liftSchedule schedule) (liftStore words initial)
      (liftWord word) (liftStore words final) ↔
    Scheduled (ofExecutor (exec localExec)) schedule initial word final := by
  rw [← execute_iff_scheduled, ← execute_iff_scheduled, execute_lift]
  change _ = Option.map (liftOutcome words) (some (final, word)) ↔ _
  exact (Option.map_injective (liftOutcome_injective words)).eq_iff

theorem toy_exec_eq (thread : Toy.ThreadId) (cfg : Toy.Config) :
    Toy.exec thread none cfg = exec toyLocal thread ⟨⟩ cfg := by
  have update (core : Toy.Core) : Function.update cfg thread (some core) = Toy.put cfg thread core :=
    funext fun other => Function.update_apply cfg thread (some core) other
  cases atThread : cfg thread with
  | none => simp [Toy.exec, exec, atThread]
  | some core =>
    cases atProgram : core.program with
    | nil => simp [Toy.exec, exec, toyLocal, atThread, Toy.init, atProgram]
    | cons instruction rest =>
      cases instruction <;> simp [Toy.exec, exec, toyLocal, atThread, Toy.init, atProgram, update, Toy.put]

theorem execute_toy {K V : Type} [DecidableEq K] [DecidableEq V]
    (words : K → V) (schedule : Schedule Toy.ThreadId PUnit) (initial : Toy.Config) :
    execute (ThreadSync.exec (liftProgram toyLocal)) (liftSchedule schedule) (liftStore words initial) =
      (execute Toy.exec (toySchedule schedule) initial).map (liftOutcome words) := by
  rw [execute_lift]
  have agrees (store : Toy.Config) :
      execute (exec toyLocal) schedule store = execute Toy.exec (toySchedule schedule) store := by
    induction schedule generalizing store with
    | nil => rfl
    | cons decision schedule ih =>
      obtain ⟨thread, ⟨⟩⟩ := decision
      simp only [toySchedule, List.map_cons, execute]
      rw [toy_exec_eq thread store]
      cases exec toyLocal thread ⟨⟩ store with
      | none => rfl
      | some result =>
        obtain ⟨next, fragment⟩ := result
        simp only [bind, Option.bind]
        rw [ih]
        rfl
  rw [agrees]

end Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Legacy
