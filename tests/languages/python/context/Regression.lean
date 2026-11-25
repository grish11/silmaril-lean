module

import Silmaril.Languages.Python.Core.Context.Thms
meta import Silmaril.Languages.Python.Core.Context.Defs
meta import Silmaril.Languages.Python.Core.Defs

open Silmaril.Languages.Python.Core

private def quotient : Expr := .binary .floorDiv (.int 7) (.int (-3))
private def nested : Expr := .binary .add (.binary .add (.int 2) (.int 5)) quotient

example : Context.focus nested = .redex [.left .add quotient] ⟨.add, 2, 5⟩ := rfl

example : Context.focus (.binary .add (.int 7) quotient) =
    .redex [.right .add 7] ⟨.floorDiv, 7, -3⟩ := rfl

example : Context.reduce (.binary .add (.int 7) quotient) = some (.ok (.binary .add (.int 7) (.int (-3)))) :=
  rfl

private def zero : Expr := .binary .floorDiv (.int 1) (.int 0)

private def failure : Expr :=
  .binary .add (.int 9) (.binary .add zero (.binary .add (.int 2) (.int 5)))

example : Context.focus failure =
    .redex [.right .add 9, .left .add (.binary .add (.int 2) (.int 5))] ⟨.floorDiv, 1, 0⟩ := rfl

example : Context.advance (.returning failure) = some (none, .raising .zeroDivisionError) :=
  Context.advance_iff.mpr (.expr (.right (.left (.compute (.divZero 1)))))

example : Context.advance (.raising .zeroDivisionError) =
    some (some (.error .zeroDivisionError), .finished (.error .zeroDivisionError)) := rfl

#guard match Context.advance (.returning nested) with
  | some (none, .returning after) => after == .binary .add (.int 7) quotient
  | _ => false

#print axioms Context.focus_iff
#print axioms Context.plug_step
#print axioms Context.reduces_iff
#print axioms Context.advance_eq_core
