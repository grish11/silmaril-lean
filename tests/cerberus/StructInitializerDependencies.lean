module
public import Silmaril.Cerberus.Elaboration.GlobalOrder.Defs
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Construction
private def symbol (n : Nat) : Sym := ⟨⟨[]⟩, n, .none⟩
private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def name : Identifier := ⟨.unknown, "x"⟩
private def tags : StructInitializers.Tags :=
  [(symbol 1, .struct [(name, ⟨[]⟩, none, ⟨false,false,false⟩, intType)] none)]

-- Missing tags/members and an all-unspecified initializer reject explicitly.
example : (State.run (StructInitializers.translate [] [] (symbol 1) []) context).1.isOk = false := by cbv
example : (State.run (StructInitializers.translate [] tags (symbol 1) [(name, none)]) context).1.isOk = false := by cbv
example : (State.run (StructInitializers.translate [] tags (symbol 1)
    [(⟨.unknown,"absent"⟩, none)]) context).1.isOk = false := by cbv

-- Preserve the pinned wildcard reset, even within constructor patterns.
example : GlobalOrder.symbolsInPattern [symbol 1] (wildcard .unit) = [] := by cbv
example : GlobalOrder.symbolsInPattern []
    (.mk [] (.ctor .tuple [symbolPattern (symbol 1) .unit, wildcard .unit])) = [] := by cbv
-- A binding's initializer is free; only its body occurrences are bound.
example : GlobalOrder.freePure (letPure (symbolPattern (symbol 1) .unit)
    (symbolPure (symbol 2)) (symbolPure (symbol 1))) = .ok [symbol 2] := by cbv
example : GlobalOrder.freePure (casePure (symbolPure (symbol 2))
    [(symbolPattern (symbol 1) .unit, symbolPure (symbol 1))]) = .ok [symbol 2] := by cbv
-- Unsequenced dependency aggregation cannot hide an external object reference.
example : GlobalOrder.freeEffect (unseqEffect
    [pureEffect (symbolPure (symbol 2)), pureEffect (symbolPure (symbol 3))]) =
    .ok [symbol 3, symbol 2] := by cbv
