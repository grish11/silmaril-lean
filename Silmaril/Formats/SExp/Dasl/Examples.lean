module
import Silmaril.Formats.SExp.Dasl.Thms

namespace Silmaril.Formats.SExpDasl

example : (parseSymbolsAbstract? "(a b . c)").isNone = true := by decide +kernel
example : (parseSymbolsAbstract? "(a (b) ())").isSome = true := by decide +kernel
example : (parseRivestAbstract? (Bytes.ofList [40, 49, 58, 255, 41])).isSome = true := by decide +kernel
example : (parseRivestAbstract? (Bytes.ofList [48, 49, 58, 97])).isNone = true := by decide +kernel

end Silmaril.Formats.SExpDasl
