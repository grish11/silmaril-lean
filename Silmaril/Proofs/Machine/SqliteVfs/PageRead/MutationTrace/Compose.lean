module

public import Silmaril.Machine.SqliteVfs.PageRead.MutationTrace.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Thms
import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit
open Silmaril.Machine.SqliteVfs.PageRead.MutationFrame
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace
open Silmaril.Formats.Sqlite

private theorem complete_of_agreement {before current : FileState} {page : Page}
    (positive : 0 < page.size) (beforeFits : page.offset + page.size ≤ before.bytes.length)
    (agrees : AgreesOnPage before current page) :
    page.offset + page.size ≤ current.bytes.length := by
  apply Nat.le_of_not_gt
  intro short
  have inside : page.size - 1 < page.size := by omega
  have missing : current.bytes[page.offset + (page.size - 1)]? = none :=
    List.getElem?_eq_none_iff.mpr (by omega)
  have first := agrees (page.size - 1) inside
  rw [missing, List.getElem?_eq_none_iff] at first
  omega

theorem trace_retains_page {capacity : Nat} {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, RetainsPage page exchange)
    (complete : page.offset + page.size ≤ before.bytes.length) (positive : 0 < page.size) :
    AgreesOnPage before after page ∧ after.mode page.handle = before.mode page.handle := by
  induction valid with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | @cons before middle after request response rest next _ ih =>
    have guard := allowed ⟨request, response⟩ (by simp)
    have frame : AgreesOnPage before middle page ∧ middle.mode page.handle = before.mode page.handle := by
      cases guard with
      | write offset data apart => exact write_preserves_page page next complete apart
      | truncate size kept => exact truncate_preserves_page page next complete kept
    have tail := ih (fun exchange member => allowed exchange (List.mem_cons_of_mem _ member))
      (complete_of_agreement positive complete frame.1)
    exact ⟨fun i within => (frame.1 i within).trans (tail.1 i within), tail.2.trans frame.2⟩

private theorem fill_eq (capacity : Nat) (file : FileState) (cache : Cache) (slot : SlotId) (page : Page) :
    fill (readOnly capacity) file cache slot page = fill (readWrite capacity) file cache slot page := rfl

private theorem append_trace {State : Type} {handler : Handler State}
    {before middle after : State} {first last : Trace}
    (front : Trace.Valid handler before first middle) (back : Trace.Valid handler middle last after) :
    Trace.Valid handler before (first ++ last) after := by
  induction front with
  | nil => exact back
  | cons step _ rest => exact .cons step (rest back)

theorem runHit_after_mutation_trace (capacity : Nat) (before after : FileState) (trace : Trace)
    (cache : Cache) (target : SlotId) (page : Page) (owned : cache target = some .vacant)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false)
    (complete : page.offset + page.size ≤ before.bytes.length)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (allowed : ∀ exchange ∈ trace, RetainsPage page exchange) :
    let original := fill (readWrite capacity) before cache target page
    let fresh := fill (readWrite capacity) after cache target page
    Trace.Valid (readWrite capacity) before (original.trace ++ trace ++ fresh.trace) after ∧
      ∀ (base db root : Nat) (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State),
        runHit? original.cache target page base db root program fuel initial =
          runPage? fresh.result.toOption base db root program fuel initial := by
  have positive : 0 < page.size := by
    have count := admitted.2.2.1
    change 0 < (page.size : Int) at count
    omega
  obtain ⟨agrees, mode⟩ := trace_retains_page page valid allowed complete positive
  have liveAfter : (after.mode page.handle).isNone = false := mode ▸ live
  have vm := (runHit_matches_refetch capacity before after cache target page owned admitted
    live liveAfter complete agrees).2
  obtain ⟨_, _, refreshed⟩ := hit_after_fill_matches_refetch capacity before after cache target page
    owned admitted live liveAfter complete agrees
  have original := (ite_eq_left complete).mp
    (readOnly_fill capacity before cache target page owned admitted live)
  have originalValid := fill_trace (readWrite capacity) before cache target page
  have freshValid := fill_trace (readWrite capacity) after cache target page
  dsimp only at originalValid freshValid ⊢
  rw [← fill_eq, original] at originalValid
  rw [← fill_eq, refreshed] at freshValid
  refine ⟨?_, vm⟩
  rw [← fill_eq, ← fill_eq capacity after, original, refreshed]
  exact append_trace (append_trace originalValid valid) freshValid

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.MutationTrace
