module

public import Silmaril.Formats.Dasl.FileInode.Defs
import Silmaril.Proofs.Formats.Dasl.FileInode

public section

namespace Silmaril.Formats.Dasl.FileInode

variable {Name : Type} {limits : Limits} {observed extension : Snapshot Name}

theorem resolves_length {depth link length data}
    (valid : Resolves limits extension depth link length data) : data.length = length :=
  Proofs.Formats.Dasl.FileInode.resolvesLength valid

/-- The declared prefix sum is the exact byte offset of the next child. -/
theorem prefix_length {depth : Nat} {inode : Inode Name} {chunks : List Bytes}
    (matching : List.Forall₂ (fun child => Resolves limits extension depth child.link child.size) inode chunks)
    (index : Nat) : (chunks.take index).flatten.length = size (inode.take index) :=
  Proofs.Formats.Dasl.FileInode.prefixLength matching index

/-- A successful partial observation reads the exact slice in every valid agreeing
extension, even if that extension needs more fuel to recover the whole file. -/
theorem range_sound (agrees : observed.Agrees extension) {fuel depth root length data offset count result}
    (valid : Resolves limits extension depth (.obj root) length data)
    (hit : read limits observed fuel root (some (offset, count)) = .ok result) :
    offset + count ≤ length ∧ result = slice data offset count :=
  Proofs.Formats.Dasl.FileInode.rangeSound agrees valid hit

theorem range_complete {fuel depth root length data offset count}
    (valid : Resolves limits extension depth (.obj root) length data) (enough : depth ≤ fuel) :
    read limits extension fuel root (some (offset, count)) =
      if offset + count ≤ length then .ok (slice data offset count) else .error (.outOfBounds length) :=
  Proofs.Formats.Dasl.FileInode.rangeComplete valid enough

theorem recover_sound (agrees : observed.Agrees extension) {fuel depth root length data result}
    (valid : Resolves limits extension depth (.obj root) length data)
    (hit : read limits observed fuel root none = .ok result) : result = data :=
  Proofs.Formats.Dasl.FileInode.recoverSound agrees valid hit

theorem recover_complete {fuel depth root length data}
    (valid : Resolves limits extension depth (.obj root) length data) (enough : depth ≤ fuel) :
    read limits extension fuel root none = .ok data :=
  Proofs.Formats.Dasl.FileInode.recoverComplete valid enough

end Silmaril.Formats.Dasl.FileInode
