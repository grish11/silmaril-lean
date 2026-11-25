module

public import Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadBoundary

open Silmaril.Machine
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Silmaril.Machine.SqliteRead (Context Status BufferView)

theorem read_range_of_admission (req : SqliteRead.Request) (env : Context) (safe : env.Admits req) :
    ReadRange (req.offset.toNat : Int) (req.amount.toNat : Int) := by
  obtain ⟨_, _, _, count, countBound, endBound, _, _⟩ := safe
  unfold ReadRange maxOffset maxCount
  change 0 ≤ (req.offset.toNat : Int) ∧ 0 < (req.amount.toNat : Int) ∧
    (req.amount.toNat : Int) ≤ ((2^31 - 1 : Nat) : Int) ∧
    (req.offset.toNat : Int) + (req.amount.toNat : Int) ≤ ((2^63 - 1 : Nat) : Int)
  omega

theorem page_admitted {binding : FileBinding} (req : SqliteRead.Request) (page : Page) (env : Context)
    (safe : env.Admits req) (aligned : MatchesPage binding req page) (positive : 0 < page.number) :
    page.Admitted := by
  refine ⟨positive, ?_⟩
  rw [← aligned.offset, ← aligned.amount]
  exact read_range_of_admission req env safe

private abbrev available := Silmaril.Machine.SqliteRead.available

private theorem available_length (bytes : Bytes) (req : SqliteRead.Request) :
    (available (bytes.map UInt8.toBitVec) req).length =
      min req.amount.toNat (bytes.length - req.offset.toNat) := by
  simp [available, Silmaril.Machine.SqliteRead.available]

private theorem available_byte (bytes : Bytes) (req : SqliteRead.Request) (i : Nat)
    (within : i < (available (bytes.map UInt8.toBitVec) req).length) :
    (available (bytes.map UInt8.toBitVec) req)[i]? =
      some ((bytes[req.offset.toNat + i]?.getD 0).toBitVec) := by
  rw [available_length] at within
  have count : i < req.amount.toNat := by omega
  have file : req.offset.toNat + i < bytes.length := by omega
  unfold available Silmaril.Machine.SqliteRead.available
  rw [List.getElem?_take_of_lt count, List.getElem?_drop, List.getElem?_map,
    getElem?_pos bytes _ file]
  rfl

private theorem full_handler_reply (bytes : Bytes) (req : SqliteRead.Request) (before after : BufferView)
    (positive : 0 < req.amount.toNat) (law : SqliteRead.Handler (bytes.map UInt8.toBitVec) req before after .ok) :
    req.offset.toNat + req.amount.toNat ≤ bytes.length ∧
      ∀ i, i < req.amount.toNat →
        after (req.buffer.toNat + i) = some ((bytes[req.offset.toNat + i]?.getD 0).toBitVec) := by
  obtain ⟨length, writes⟩ := law.2
  have bound := length
  rw [available_length] at bound
  refine ⟨by omega, ?_⟩
  intro i inside
  have within : i < (available (bytes.map UInt8.toBitVec) req).length := length ▸ inside
  exact (writes i within).trans (available_byte bytes req i within)

private theorem short_handler_reply (bytes : Bytes) (req : SqliteRead.Request) (before after : BufferView)
    (positive : 0 < req.amount.toNat)
    (law : SqliteRead.Handler (bytes.map UInt8.toBitVec) req before after .shortRead) :
    bytes.length < req.offset.toNat + req.amount.toNat ∧
      ∀ i, i < req.amount.toNat →
        after (req.buffer.toNat + i) = some ((bytes[req.offset.toNat + i]?.getD 0).toBitVec) := by
  obtain ⟨length, writes⟩ := law.2
  have limit := length
  rw [available_length] at limit
  have short : bytes.length < req.offset.toNat + req.amount.toNat := by omega
  refine ⟨short, ?_⟩
  intro i inside
  have slot : i < (available (bytes.map UInt8.toBitVec) req ++
      List.replicate (req.amount.toNat - (available (bytes.map UInt8.toBitVec) req).length) 0).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [writes i slot]
  by_cases inFile : i < (available (bytes.map UInt8.toBitVec) req).length
  · rw [List.getElem?_append_left inFile, available_byte bytes req i inFile]
  · have outside : bytes.length ≤ req.offset.toNat + i := by
      rw [available_length] at inFile length
      omega
    have missing : bytes[req.offset.toNat + i]? = none := List.getElem?_eq_none_iff.mpr outside
    have padding : i - (available (bytes.map UInt8.toBitVec) req).length <
        req.amount.toNat - (available (bytes.map UInt8.toBitVec) req).length := by omega
    rw [List.getElem?_append_right (Nat.le_of_not_gt inFile), missing, List.getElem?_replicate]
    simp [padding]

theorem returning_handler_agrees_with_fill {binding : FileBinding}
    (req : SqliteRead.Request) (page : Page) (env : Context) (file : FileState)
    (capacity : Nat) (cache : Cache) (target : SlotId) (before after : BufferView) (status : Status)
    (safe : env.Admits req) (aligned : MatchesPage binding req page) (positive : 0 < page.number)
    (live : (file.mode page.handle).isNone = false) (owned : cache target = some .vacant)
    (law : SqliteRead.Handler (file.bytes.map UInt8.toBitVec) req before after status) :
    let outcome := fill (readOnly capacity) file cache target page
    let buffer := readBytes file.bytes page.offset page.size
    Silmaril.Machine.SqliteRead.Framed req before after ∧
      match status with
      | .ok => outcome =
          ⟨.ok buffer, file, cache.install target page buffer, [⟨page.request, .ok buffer⟩]⟩ ∧
          ∀ i, i < page.size → after (req.buffer.toNat + i) = (buffer[i]?).map UInt8.toBitVec
      | .shortRead => outcome = ⟨.error .shortRead, file, cache, [⟨page.request, .shortRead buffer⟩]⟩ ∧
          ∀ i, i < page.size → after (req.buffer.toNat + i) = (buffer[i]?).map UInt8.toBitVec
      | .other _ => True := by
  have count := safe.2.2.2.1
  have admitted := page_admitted req page env safe aligned positive
  have fillLaw := readOnly_fill capacity file cache target page owned admitted live
  refine ⟨law.1, ?_⟩
  cases status with
  | ok =>
    obtain ⟨full, wrote⟩ := full_handler_reply file.bytes req before after count law
    rw [aligned.offset, aligned.amount] at full wrote
    refine ⟨(ite_eq_left full).mp fillLaw, fun i within => ?_⟩
    simpa [readBytes, within] using wrote i within
  | shortRead =>
    obtain ⟨short, wrote⟩ := short_handler_reply file.bytes req before after count law
    rw [aligned.offset, aligned.amount] at short wrote
    refine ⟨(ite_eq_right (Nat.not_le_of_gt short)).mp fillLaw, fun i within => ?_⟩
    simpa [readBytes, within] using wrote i within
  | other _ => trivial

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadBoundary
