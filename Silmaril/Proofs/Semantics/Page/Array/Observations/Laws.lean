module

public import Silmaril.Semantics.Page.Array.Defs
public import Silmaril.Semantics.ReadWrite.Observations.Defs
import Silmaril.Semantics.Page.Array.Thms

public section
namespace Silmaril.Proofs.Semantics.Page.Array.Observations

open Silmaril.Semantics.Page Silmaril.Semantics.ReadWrite

universe v
variable {Content : Type v} {n : Nat}

theorem undef_access_frames :
    (UndefArray.access n Content).Frames (UndefArray.access n Content).read := by
  intro initial next page value other write different
  rw [← UndefArray.memory_read next, ← UndefArray.memory_read initial]
  refine (Store.access_frames_read (mapStore Nat Content)) (address := page) (value := value) ?_ different
  rw [UndefArray.memory_write, write]
  rfl

theorem undef_access_readsAfterWrite : (UndefArray.access n Content).ReadsAfterWrite := by
  intro initial next page written observed write read
  change (if h : page < n then some (override initial ⟨page, h⟩ (some written)) else none) =
    some next at write
  split at write
  · rename_i bound
    cases write
    simpa [UndefArray.access, bound, override] using read.symm
  · contradiction

theorem access_frames : (Array.access n Content).Frames (Array.access n Content).read := by
  intro initial next page written other write different
  rw [← Array.embed_read next, ← Array.embed_read initial]
  refine undef_access_frames (address := page) (value := written) ?_ different
  rw [Array.embed_write, write]
  rfl

theorem access_readsAfterWrite : (Array.access n Content).ReadsAfterWrite := by
  intro initial next page written observed write read
  refine undef_access_readsAfterWrite (initial := initial.embed) (next := next.embed)
    (address := page) ?_ ((Array.embed_read next page).trans read)
  rw [Array.embed_write, write]
  rfl

end Silmaril.Proofs.Semantics.Page.Array.Observations
