module

public import Silmaril.Formats.Dasl.MeasuredSequence.Defs
import Silmaril.Proofs.Formats.Dasl.MeasuredSequence

@[expose] public section

namespace Silmaril.Formats.Dasl.MeasuredSequence

variable {Name Item : Type} {item : Encode.TotalCodec Item (Shallow Name)}

theorem decode_object {resolve : Name → Option (Editable Item)} (name : Name) :
    decodeShape? item resolve (.ref (.obj name)) = resolve name := rfl

/-- For inline children and children supplied by the resolver alike, the join
uses their recovered sizes and rejects an empty child. -/
theorem decode_branch {resolve : Name → Option (Editable Item)} {leftShape rightShape : Shallow Name}
    {left right : Editable Item} (leftHit : decodeShape? item resolve leftShape = some left)
    (rightHit : decodeShape? item resolve rightShape = some right) :
    decodeShape? item resolve (branchShape leftShape rightShape) = join? left right :=
  Proofs.Formats.Dasl.MeasuredSequence.decodeBranch leftHit rightHit

theorem shape_recovers (item : Encode.TotalCodec Item (Shallow Name))
    (resolve : Name → Option (Editable Item)) (tree : Editable Item) :
    decodeShape? item resolve (encodeShape item tree.val) = some tree :=
  Proofs.Formats.Dasl.MeasuredSequence.shapeRecovery item resolve tree

/-- The inline codec preserves the exact valid editable tree, not only its list. -/
def rawCodec (item : Encode.TotalCodec Item (Shallow Name)) : Encode.TotalCodec (Editable Item) (Shallow Name) where
  encode tree := encodeShape item tree.val
  decode? := decodeShape? item (fun _ => none)
  recovers := shape_recovers item (fun _ => none)

theorem normalized_encode_eq_iff {left right : Semantics.MeasuredSequence.Tree Item} :
    encodeNormalized item left = encodeNormalized item right ↔
      Semantics.MeasuredSequence.flatten left = Semantics.MeasuredSequence.flatten right :=
  ⟨fun same => Semantics.MeasuredSequence.normalize_eq_iff.mp
    (congrArg Subtype.val ((normalizedCodec item).injective same)),
   fun same => congrArg (normalizedCodec item).encode
    (Subtype.ext (Semantics.MeasuredSequence.normalize_eq_iff.mpr same))⟩

/-- Strict acceptance is inherited from the payload codec. Without this premise,
the encoder is still canonical by contents, but payload aliases may decode. -/
theorem normalized_accepts_exact
    (exactItem : ∀ ⦃shape value⦄, item.decode? shape = some value → item.encode value = shape)
    {shape : Shallow Name} {tree : Normalized Item} :
    (normalizedCodec item).decode? shape = some tree ↔ (normalizedCodec item).encode tree = shape :=
  ⟨Proofs.Formats.Dasl.MeasuredSequence.normalizedExact exactItem,
    fun same => same ▸ (normalizedCodec item).recovers tree⟩

/-- Normalize any successfully decoded editable representation, including one
whose subtrees were supplied explicitly by the resolver. -/
theorem normalize_shape_recovers {resolve : Name → Option (Editable Item)} {shape : Shallow Name}
    {tree : Editable Item} (hit : decodeShape? item resolve shape = some tree) :
    (normalizeShape? item resolve shape).bind (normalizedCodec item).decode? = some (rebuild tree.val) := by
  rw [normalizeShape?, hit]
  exact (normalizedCodec item).recovers (rebuild tree.val)

end Silmaril.Formats.Dasl.MeasuredSequence
