module

public import Silmaril.Formats.Bao.Opening.Defs
import Silmaril.Proofs.Formats.Bao.Layout
import Silmaril.Proofs.Formats.Bao.Coverage
import Silmaril.Proofs.Formats.Bao.Release
import Silmaril.Proofs.Formats.Bao.Opening

public section

namespace Silmaril.Formats.Bao

theorem takeExact_spec {width : Nat} {input field rest : Bytes} :
    takeExact width input = some (field, rest) ↔ field.length = width ∧ input = field ++ rest :=
  Proofs.Formats.Bao.takeExact_spec

theorem readHeader_spec {input rest : Bytes} {size : Nat} :
    readHeader input = some (size, rest) ↔
      ∃ header : Bytes, header.length = 8 ∧ getLE header = size ∧ input = header ++ rest :=
  Proofs.Formats.Bao.readHeader_spec

theorem readHeader_bound {input rest : Bytes} {size : Nat}
    (parsed : readHeader input = some (size, rest)) : size < u64Limit :=
  Proofs.Formats.Bao.readHeader_bound parsed

theorem readHeader_putLE64 {size : Nat} (body : Bytes) (range : size < u64Limit) :
    readHeader (putLE64 size ++ body) = some (size, body) :=
  Proofs.Formats.Bao.readHeader_putLE64 body range

theorem readSlots_spec {layout : List Slot} {fields : List Bytes} {input rest : Bytes} :
    readSlots layout input = some (fields, rest) ↔
      Tape layout fields ∧ input = fields.flatten ++ rest := Proofs.Formats.Bao.readSlots_spec

theorem readFrame_spec {layout : List Slot} {fields : List Bytes} {input : Bytes} :
    readFrame layout input = some fields ↔ Tape layout fields ∧ input = fields.flatten :=
  Proofs.Formats.Bao.readFrame_spec

theorem decode_spec {encoding : Encoding} {size : Nat} {input : Bytes} {fields : List Bytes} :
    decode encoding input = some (size, fields) ↔
      encoding.valid = true ∧ encoding.bodyFits size fields.flatten.length = true ∧
      readHeader input = some (size, fields.flatten) ∧ Tape (encoding.layout size) fields :=
  Proofs.Formats.Bao.decode_spec

theorem pairs_perm (tree : Plan) : (tree.pairs true).Perm (tree.pairs false) :=
  Proofs.Formats.Bao.pairs_perm tree

theorem detach_spec {layout : List Slot} {fields : List Bytes} :
    Tape layout fields ↔ ∃ proof : Detached layout,
      detach layout fields = some proof ∧ proof.fields = fields :=
  Proofs.Formats.Bao.detach_spec

theorem pairs_sublist (size group : Nat) (query : List Interval) (span : Span) (postorder : Bool) :
    ((planAt size group query span).pairs postorder).Sublist
      ((planAt size 1 query span).pairs postorder) :=
  Proofs.Formats.Bao.pairs_sublist size group query span postorder

theorem coverage_at (size group : Nat) (query : List Interval) (span : Span) (index : Nat)
    (inside : Contains span index) (selected : Selected query index) :
    ∃ leaf width, Slot.data leaf width ∈ (planAt size group query span).preorder ∧ Contains leaf index :=
  Proofs.Formats.Bao.coverage_at size group query span index inside selected

theorem selected_of_data (size group : Nat) (query : List Interval) (span leaf : Span)
    (width index : Nat) (found : Slot.data leaf width ∈ (planAt size group query span).preorder)
    (inside : Contains leaf index) : Selected query index :=
  Proofs.Formats.Bao.selected_of_data size group query span leaf width index found inside

theorem runSteps_spec {hash : HashOps} {size : Nat} {state final : Session}
    {fields : List Bytes} {events : List Event} :
    runSteps hash size state fields = some (events, final) ↔ Steps hash size state fields events final :=
  Proofs.Formats.Bao.runSteps_spec

theorem release_checked {hash : HashOps} {size : Nat} {tree : Plan} {digest : Digest}
    {fields : List Bytes} {events : List Event} {final : Session}
    (trace : Steps hash size (start tree digest) fields events final) :
    (∀ event ∈ events, Checked hash tree digest event) ∧
      (rightEdgeClaim size final = some size ↔ ∃ event ∈ events, EdgeEvent size event) :=
  Proofs.Formats.Bao.release_checked trace

theorem verifyFrame_sound {hash : HashOps} {size : Nat} {tree : Plan} {digest : Digest}
    {body : Bytes} {events : List Event} {length : Option Nat}
    (verified : verifyFrame hash size tree digest body = some (events, length)) :
    (∀ event ∈ events, Checked hash tree digest event) ∧
      (length = some size ↔ ∃ event ∈ events, EdgeEvent size event) :=
  Proofs.Formats.Bao.verifyFrame_sound verified

theorem lowerPrefix_spec {expected : Digest} {plan : Plan} {fields : List Bytes}
    {frontier : Frontier} : lowerPrefix plan expected fields = some frontier ↔
      Fills expected plan fields frontier [] ∧ (∀ cv, frontier ≠ .opaque cv) :=
  Proofs.Formats.Bao.lowerPrefix_spec

theorem split_matches_byte_geometry (first size : Nat) (positive : 0 < size) :
    ((Span.mk first (chunks size)).split.2.first, (Span.mk first (chunks size)).split.1.count) =
      (first + 2 ^ ((size - 1) / chunkBytes).log2, 2 ^ ((size - 1) / chunkBytes).log2) :=
  Proofs.Formats.Bao.split_matches_byte_geometry first size positive

theorem releaseRanges_spec {Range : Digest → Nat → Nat → Bytes → Prop}
    {Trusted EOF : Digest → Nat → Prop} {digest : Digest} {claim : Nat}
    {permit : Option (PLift (ExtentEvidence Trusted EOF digest claim))}
    {pending : List (StagedRange Range digest claim)} {output : List (Nat × Bytes)} :
    releaseRanges permit pending = some output ↔
      permit.isSome = true ∧ output = pending.map (fun fragment => (fragment.offset, fragment.bytes)) :=
  Proofs.Formats.Bao.releaseRanges_spec

/-- No cross-extent range statement follows from a checked range alone. Supply the
independent EOF comparison (or externally trusted length) and the same-extent theorem. -/
theorem released_slice_or_collision {Range : Digest → Nat → Nat → Bytes → Prop}
    {Trusted EOF : Digest → Nat → Prop} {digest : Digest} {claim referenceSize : Nat}
    {permit : Option (PLift (ExtentEvidence Trusted EOF digest claim))}
    {pending : List (StagedRange Range digest claim)} {output : List (Nat × Bytes)}
    {Slice : Nat → Bytes → Prop} {Collision : Prop}
    (trustedExtent : Trusted digest claim → claim = referenceSize)
    (checkedExtent : EOF digest claim → claim = referenceSize ∨ Collision)
    (sameExtent : ∀ {offset bytes}, Range digest claim offset bytes → claim = referenceSize →
      Slice offset bytes ∨ Collision)
    (released : releaseRanges permit pending = some output) :
    ∀ entry ∈ output, Slice entry.1 entry.2 ∨ Collision :=
  Proofs.Formats.Bao.released_slice_or_collision trustedExtent checkedExtent sameExtent released

end Silmaril.Formats.Bao
