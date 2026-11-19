module

public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs

/-! Selected integer-member struct initializer equations from pinned Cerberus
`translation.lem:2782–2818,782–798` at
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. Actual tag-member types determine
assignment conversions. Missing members retain unspecified values; multiple
initializers retain the upstream reversed unsequenced evaluation list and
standard annotation. No typing or memory-validity law is assumed here. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.StructInitializers
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

abbrev Tags := List (Sym × TagDefinition)
abbrev Input := Identifier × Option (Ctype × State.ElabM Effect)

def members (tags : Tags) (tag : Sym) : Except String
    (List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) := do
  let some (_, .struct fields _) := tags.find? (fun entry => decide (entry.1.key = tag.key))
    | throw "ill-typed AilEstruct: missing struct tag"
  return fields

def translate (runtime : List Runtime.Binding) (tags : Tags) (tag : Sym)
    (inputs : List Input) : State.ElabM Effect := do
  let fields ← Constants.liftResult (members tags tag)
  let (values, patterns, effects) ← inputs.foldlM (fun (values, patterns, effects) (name, input) => do
    let some (_, _, _, _, destination) := fields.find? (fun field => field.1.key == name.key)
      | throw (.message "ill-typed AilEstruct: missing struct member")
    match input with
    | none => return ((name, unspecified destination) :: values, patterns, effects)
    | some (source, child) =>
        let .mk _ (.basic (.integer _)) := source
          | throw (.message "unsupported: struct initializer source is not a direct integer")
        let .mk _ (.basic (.integer _)) := destination
          | throw (.message "unsupported: struct initializer destination is not a direct integer")
        let core ← child
        let loaded ← State.wrappedFreshSymbol (.loaded .integer)
        let converted ← Constants.liftResult
          (Conversion.loadedArithmetic runtime source destination loaded.expression)
        return ((name, converted) :: values, loaded.pattern :: patterns, core :: effects))
    ([], [], [])
  let result := pureEffect (specified (structPure tag values.reverse))
  match patterns, effects with
  | [pattern], [effect] => return weakSequence pattern effect result
  | _ :: _, _ :: _ =>
      let pattern ← Constants.liftResult (tuplePattern patterns)
      return weakSequence pattern (addStandard "§6.7.9#23" (unseqEffect effects)) result
  | _, _ => throw (.message "ill-typed AilEstruct: no explicit initialized member")

end Silmaril.Cerberus.Elaboration.StructInitializers
