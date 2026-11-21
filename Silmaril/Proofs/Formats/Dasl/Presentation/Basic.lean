module
public import Silmaril.Formats.Dasl.Presentation.Defs

public section
namespace Silmaril.Proofs.Formats.Dasl.Presentation
open Silmaril.Formats Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Encode
variable {Ast Wire : Type}

theorem parse_per (codec : TotalCodec Ast Value) (parse : Wire → Option Ast) :
    PER.ofDecoder (codec.parseAbstract? parse) = PER.ofDecoder parse := by
  apply PER.ext
  intro left right
  change (∃ value, codec.parseAbstract? parse left = some value ∧
    codec.parseAbstract? parse right = some value) ↔ ∃ value, parse left = some value ∧ parse right = some value
  cases hl : parse left <;> cases hr : parse right <;> simp [TotalCodec.parseAbstract?, hl, hr]
  rename_i lhs rhs
  exact ⟨fun same => codec.injective (congrArg Subtype.val same), congrArg codec.intoAbstract⟩

end Silmaril.Proofs.Formats.Dasl.Presentation
