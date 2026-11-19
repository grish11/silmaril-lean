module
public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs
/-! Selected integer-element array initializer equations from pinned Cerberus
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`, `translation.lem:2745–2780,782–798`.
Actual element CType determines assignment conversion. Missing elements retain
unspecified values. Freshness, reversed unsequenced evaluation and annotations
are retained; no typing, initialization-validity or refinement law is assumed. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ArrayInitializers
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction
abbrev Input := Option (Ctype × State.ElabM Effect)
def translate (runtime : List Runtime.Binding) (destination : Ctype)
    (inputs : List Input) : State.ElabM Effect := do
  let .mk _ (.basic (.integer _)) := destination
    | throw (.message "unsupported: array initializer element is not a direct integer")
  let (values, patterns, effects) ← inputs.foldlM (fun (values, patterns, effects) input => do
    match input with
    | none => return (unspecified destination :: values, patterns, effects)
    | some (source, child) =>
      let .mk _ (.basic (.integer _)) := source
        | throw (.message "unsupported: array initializer source is not a direct integer")
      let core ← child
      let loaded ← State.wrappedFreshSymbol (.loaded .integer)
      let converted ← Constants.liftResult
        (Conversion.loadedArithmetic runtime source destination loaded.expression)
      return (converted :: values, loaded.pattern :: patterns, core :: effects)) ([],[],[])
  let result := pureEffect (specified (array values.reverse))
  match patterns, effects with
  | [pattern], [effect] => return weakSequence pattern effect result
  | _ :: _, _ :: _ =>
    let pattern ← Constants.liftResult (tuplePattern patterns)
    return weakSequence pattern (addStandard "§6.7.9#23" (unseqEffect effects)) result
  | _, _ => throw (.message "ill-typed AilEarray: no explicit initialized element")
end Silmaril.Cerberus.Elaboration.ArrayInitializers
