module

public import Silmaril.Formats.Iroh.Defs
public import Silmaril.Formats.Bao.Thms
import Silmaril.Proofs.Formats.Iroh.Layout

public section

namespace Silmaril.Formats.Iroh

open Bao (Bytes Tape readHeader)

theorem readResponse_spec {query : Boundaries} {input rest : Bytes} {size : Nat}
    {fields : List Bytes} :
    readResponse query input = some (size, fields, rest) ↔
      readHeader input = some (size, fields.flatten ++ rest) ∧
      coverageBytes size query ≤ (fields.flatten ++ rest).length ∧
      Tape (responsePlan size query).preorder fields := Proofs.Formats.Iroh.readResponse_spec

theorem readMemory_spec {root : Hash} {size : Nat} {order : Order} {body : Bytes}
    {fields : List Bytes} :
    readMemory root size order body = some ⟨root, size, order, fields⟩ ↔
      size < Bao.u64Limit ∧ body.length = outboardSize size ∧
      Tape (outboardLayout order size) fields ∧ body = fields.flatten :=
  Proofs.Formats.Iroh.readMemory_spec

theorem outboard_order (size : Nat) :
    (outboardLayout .post size).Perm (outboardLayout .pre size) :=
  Bao.pairs_perm (Bao.fullPlan size groupChunks)

theorem readTrailer_spec {input body : Bytes} {size : Nat} :
    readTrailer input = some (size, body) ↔
      ∃ header : Bytes, header.length = 8 ∧ Bao.getLE header = size ∧ input = body ++ header :=
  Proofs.Formats.Iroh.readTrailer_spec

/-- The 16 KiB profile drops coordinates, not merely bytes, from the official Bao outboard.
The inverse needs missing chaining values or the original payload and a hash kernel. -/
theorem outboard_sublist (size : Nat) :
    (outboardLayout .pre size).Sublist (Bao.Encoding.outboard.layout size) :=
  Bao.pairs_sublist size groupChunks [⟨0, Bao.chunks size⟩] ⟨0, Bao.chunks size⟩ false

end Silmaril.Formats.Iroh
