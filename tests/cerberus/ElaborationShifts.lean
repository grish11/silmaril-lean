module
public import Silmaril.Cerberus.Elaboration.Shifts.Defs
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction
private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def type : Ctype := .mk [] (.basic (.integer (.signed .int)))
-- Bodies are irrelevant to these syntax/allocation tests; execution uses the
-- actual pinned runtime in ShiftRuntime, never these placeholders.
private def runtime : List Runtime.Binding := [
 (⟨⟨[]⟩, 1, .id "conv_int"⟩, .function (.object .integer) [] (integer 0)),
 (⟨⟨[]⟩, 2, .id "ctype_width"⟩, .function (.object .integer) [] (integer 0)),
 (⟨⟨[]⟩, 3, .id "is_representable_integer"⟩, .function .boolean [] (boolean false))]
private def child : State.ElabM Effect := do
 let _ ← State.freshDescription .none
 return pureEffect (specified (integer 1))
private def translated := State.run (Shifts.left Target.pinnedApple Target.emptyEnvironment
 runtime .unknown type type type child child) context
example : translated.2.freshness.next = 109 := by cbv
example : translated.1.isOk = true := by cbv
example : (match translated.1 with
 | .ok (.mk _ (.wseq (.mk _ (.ctor .tuple ((.mk _ (.base (some symbol, _))) :: _))) _ _)) => some symbol.number
 | _ => none) = some 100 := by cbv
private def branch (index : Nat) : Option Pure := match translated.1 with
 | .ok (.mk _ (.wseq _ _ (.mk _ (.pure (.mk _ _ (.case_ _ branches)))))) => (branches[index]?).map Prod.snd
 | _ => none
example : branch 0 = some (standardUndefined .unknown "§6.5#5" .UB036_exceptional_condition) := by cbv
example : branch 1 = branch 0 := by cbv
example : (State.run (Shifts.left {Target.pinnedApple with cheri := true}
 Target.emptyEnvironment runtime .unknown type type type child child) context).2.freshness.next = 100 := by cbv
example : (State.run (Shifts.left Target.pinnedApple Target.emptyEnvironment []
 .unknown type type type child child) context).1.isOk = false := by cbv
private def unsignedType : Ctype := .mk [] (.basic (.integer (.unsigned .int)))
private def unsignedTranslation := State.run (Shifts.left Target.pinnedApple Target.emptyEnvironment
 runtime .unknown unsignedType unsignedType type child child) context
example : (match unsignedTranslation.1 with
 | .ok (.mk _ (.wseq _ _ (.mk _ (.pure (.mk _ _ (.case_ _ branches)))))) => (branches[1]?).map Prod.snd
 | _ => none) = some (unspecified unsignedType) := by cbv
-- Cn signed shifts use their primitive rather than requiring a Driver runtime
-- representability binding. Missing width remains an error in either backend.
example : (State.run (Shifts.left Target.pinnedApple Target.emptyEnvironment
 (runtime.take 2) .unknown type type type child child) {context with backend := "Cn"}).1.isOk = true := by cbv
example : (State.run (Shifts.left Target.pinnedApple Target.emptyEnvironment
 (runtime.take 2) .unknown type type type child child) context).1.isOk = false := by cbv
example : (State.run (Shifts.left Target.pinnedApple Target.emptyEnvironment
 (runtime.take 1) .unknown type type type child child) {context with backend := "Cn"}).1.isOk = false := by cbv
