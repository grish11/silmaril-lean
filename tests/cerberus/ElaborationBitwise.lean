module

public import Silmaril.Cerberus.Elaboration.Bitwise.Defs

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def type : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def convSymbol : Sym := ⟨⟨[]⟩, 5, .id "conv_int"⟩
private def runtime : List Runtime.Binding :=
  [(convSymbol, .function (.object .integer) [] (integer 0))]
private def child : State.ElabM Effect := do
  let _ ← State.freshDescription .none
  return pureEffect (specified (integer 1))
private def translated := State.run
  (Bitwise.translate Target.pinnedApple Target.emptyEnvironment runtime type type type .band child child) context

-- The source allocates exactly four wrappers, then translates both children.
example : translated.2.freshness.next = 106 := by cbv
example : (match translated.1 with
  | .ok (.mk _ (.wseq (.mk _ (.ctor .tuple ((.mk _ (.base (some symbol, _))) :: _))) _ _)) => some symbol.number
  | _ => none) = some 100 := by cbv
example : (match translated.1 with
  | .ok (.mk _ (.wseq _ _ (.mk _ (.pure (.mk _ _ (.case_ _ [_, (_, fallback)])))))) => some fallback
  | _ => none) = some (unspecified type) := by cbv

example : Bitwise.operatorData .band = .ok ("§6.5.10", .ivAnd) := rfl
example : Bitwise.operatorData .bxor = .ok ("§6.5.11", .ivXor) := rfl
example : Bitwise.operatorData .bor = .ok ("§6.5.12", .ivOr) := rfl
example : (State.run (Bitwise.translate Target.pinnedApple Target.emptyEnvironment []
    type type type .band child child) context).1.isOk = false := by cbv
example : (State.run (Bitwise.translate {Target.pinnedApple with cheri := true}
    Target.emptyEnvironment runtime type type type .band child child) context).1.isOk = false := by cbv
