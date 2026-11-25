module

import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Thms

namespace Silmaril.Containers.SqliteVfs.MutationTrace

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

private def start : FileState := ⟨[10, 20, 30, 40, 50], some .readWrite, 0⟩
private def finish : FileState := {start with bytes := [10, 99, 30, 40]}
private def page : Page := ⟨⟨0⟩, 2, 2⟩
private def changes : Trace := [
  ⟨.write page.handle 1 [99], .ok ()⟩,
  ⟨.truncate page.handle 4, .ok ()⟩
]

private theorem changesValid : Trace.Valid (readWrite 8) start changes finish :=
  .cons rfl (.cons rfl (.nil _))

private theorem changesRetain : ∀ exchange ∈ changes, RetainsPage page exchange := by
  intro exchange member
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .write _ _ (Or.inr (by decide))
  · exact .truncate _ (by decide)

example : AgreesOnPage start finish page :=
  (trace_retains_page page changesValid changesRetain (by decide) (by decide)).1

private def cache : Cache := fun slot => if slot = 0 then some .vacant else none
private def readPage : Exchange := ⟨page.request, .ok [30, 40]⟩

example : (runtime (readWrite 8)).beh start (.blocked (encode ([readPage] ++ changes ++ [readPage]))) := by
  have valid := (runHit_after_mutation_trace 8 start finish changes cache 0 page rfl (by decide)
    rfl (by decide) changesValid changesRetain).1
  exact blocked_iff.mpr ⟨_, finish, valid, rfl⟩

example : ¬ RetainsPage page ⟨.write page.handle 2 [99], .ok ()⟩ := by
  intro admitted
  cases admitted with
  | write _ _ disjoint => exact (by decide : ¬ (4 ≤ 2 ∨ 3 ≤ 2)) disjoint

#print axioms trace_retains_page
#print axioms runHit_after_mutation_trace

end Silmaril.Containers.SqliteVfs.MutationTrace
