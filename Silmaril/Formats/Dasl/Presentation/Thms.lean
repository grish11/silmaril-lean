module
public import Silmaril.Formats.Dasl.Presentation.Defs
import Silmaril.Proofs.Formats.Dasl.Presentation.Basic

public section
namespace Silmaril.Formats.Dasl.Encode.TotalCodec
variable {Ast Wire : Type}

theorem intoAbstract_injective (codec : TotalCodec Ast Value) : Function.Injective codec.intoAbstract :=
  fun _ _ h => codec.injective (congrArg Subtype.val h)

theorem pull_abstract_equality (codec : TotalCodec Ast Value) :
    (PER.equality codec.Abstract).pull codec.intoAbstract = PER.equality Ast :=
  PER.ext fun _ _ => ⟨fun h => codec.intoAbstract_injective h, fun h => congrArg codec.intoAbstract h⟩

@[simp] theorem from_intoAbstract (codec : TotalCodec Ast Value) (ast : Ast) :
    codec.fromAbstract? (codec.intoAbstract ast) = some ast := codec.recovers ast

@[simp] theorem into_fromAbstract (codec : TotalCodec Ast Value) (value : codec.Abstract) :
    (codec.fromAbstract? value).map codec.intoAbstract = some value := by
  obtain ⟨ast, encoded⟩ := value.property
  have eq : codec.intoAbstract ast = value := Subtype.ext encoded
  rw [← eq, from_intoAbstract, Option.map_some]

theorem parseAbstract_recover (codec : TotalCodec Ast Value) (parse : Wire → Option Ast) (input : Wire) :
    (codec.parseAbstract? parse input).bind codec.fromAbstract? = parse input := by
  cases h : parse input <;> simp [parseAbstract?, h]

theorem parseAbstract_per (codec : TotalCodec Ast Value) (parse : Wire → Option Ast) :
    PER.ofDecoder (codec.parseAbstract? parse) = PER.ofDecoder parse :=
  Proofs.Formats.Dasl.Presentation.parse_per codec parse

end Silmaril.Formats.Dasl.Encode.TotalCodec
