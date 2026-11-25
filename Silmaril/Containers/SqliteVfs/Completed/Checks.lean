module

import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Containers.SqliteVfs.Thms

namespace Silmaril.Containers.SqliteVfs.Completed

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

private def file : FileState := ⟨[10], some .readOnly, 0⟩
private def request : Request := .read ⟨0⟩ 0 1
private def exchange : Exchange := ⟨request, .ok [10]⟩
private def events : List Event := encode [exchange] ++ [.recv request]

private theorem pendingExec :
    (machine (readOnly 8)).Exec Mach.seqPolicy (.idle file) events (.pending file request) :=
  exec_iff.mpr ⟨[exchange], file, .cons rfl (.nil _), .inr ⟨request, rfl, rfl⟩⟩

example : completed events = [exchange] := rfl

example : ∃ current, Trace.Valid (readOnly 8) file (completed events) current :=
  let ⟨current, valid, _⟩ := completed_exec_iff.mp pendingExec
  ⟨current, valid⟩

example : ¬ (runtime (readOnly 8)).beh file (.blocked events) := by
  intro observed
  have shape := (completed_blocked_iff.mp observed).1
  change [Event.recv request, Event.send exchange, Event.recv request] =
    [Event.recv request, Event.send exchange] at shape
  cases shape

example : ¬ (runtime (readOnly 8)).beh file (.blocked [.send exchange]) := by
  intro observed
  have shape := (completed_blocked_iff.mp observed).1
  change [Event.send exchange] = [Event.recv request, Event.send exchange] at shape
  cases shape

private def before : FileState := ⟨[10, 20, 30], some .readWrite, 0⟩
private def after : FileState := {before with bytes := [10, 20]}
private def page : Page := ⟨⟨0⟩, 1, 2⟩
private def truncate : Exchange := ⟨.truncate page.handle 2, .ok ()⟩

example : ∃ final, Trace.Valid (readWrite 8) before [truncate] final ∧
    CacheHit.AgreesOnPage before final page := by
  have valid : Trace.Valid (readWrite 8) before [truncate] after := .cons rfl (.nil _)
  have observed := blocked_iff.mpr ⟨[truncate], after, valid, rfl⟩
  have retains : ∀ e ∈ completed (encode [truncate]), RetainsPage page e := by
    intro e member
    simp only [completed_encode, List.mem_singleton] at member
    cases member
    exact .truncate 2 (by decide)
  obtain ⟨_, final, recovered, frame, _⟩ :=
    blocked_retaining_page 8 before page (encode [truncate]) observed retains
      (by decide) (by decide)
  exact ⟨final, recovered, frame⟩

#print axioms completed_encode
#print axioms completed_exec_iff
#print axioms completed_blocked_iff
#print axioms blocked_retaining_page

end Silmaril.Containers.SqliteVfs.Completed
