module

public import Silmaril.Cerberus.Elaboration.Conversion.Defs
public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.ControlTests.Defs

/-! Integer conditional construction from pinned `translation.lem:2323–2400`.
The test callback must elaborate the actual typed-Ail TestEq-zero expression.
It runs before the two condition wrappers; both branch syntax trees are then
constructed in source order, but only the selected branch executes in Core.
Floating/pointer results and GNU omitted-middle conditionals are not ported. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Conditionals
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

structure Binders where
  loaded : State.WrappedSymbol
  object : State.WrappedSymbol

def freshBinders : State.ElabM Binders := do
  let loaded ← State.wrappedFreshSymbol (.loaded .integer)
  let object ← State.wrappedFreshSymbol (.object .integer)
  return ⟨loaded, object⟩

/-- Source branch evaluation precedes allocation of its conversion wrapper. -/
def convertBranch (bindings : List Runtime.Binding) (source destination : Ctype)
    (child : State.ElabM Effect) : State.ElabM Effect := do
  let core ← child
  let loaded ← State.wrappedFreshSymbol (.loaded .integer)
  let converted ← Constants.liftResult
    (Conversion.loadedArithmetic bindings source destination loaded.expression)
  return strongSequence loaded.pattern core (pureEffect converted)

def finish (logical : Bool) (location : Loc) (binders : Binders)
    (test yes no : Effect) : Effect :=
  let decision := ifEffect (operation .eq binders.object.expression (integer 0)) yes no
  let decision := if logical then decision else addStandard "§6.5.15#4, sentence 2" decision
  let result := strongSequence binders.loaded.pattern test
    (caseEffect binders.loaded.expression
      [(specifiedPattern binders.object.pattern, decision),
       (unspecifiedPattern (wildcard .ctype), pureEffect
         (undefined location (.UB_CERB004_unspecified .UB_unspec_conditional)))])
  if logical then result else addStandard "§6.5.15#4, sentence 1" result

/-- Integer-only domain of the pinned implicit branch conversion. The `logical`
flag suppresses conditional standard tags for the source's &&/|| desugaring. -/
def translate (logical : Bool) (bindings : List Runtime.Binding) (location : Loc)
    (resultType yesType noType : Ctype) (test yes no : State.ElabM Effect) : State.ElabM Effect := do
  unless ControlTests.integerType resultType && ControlTests.integerType yesType &&
      ControlTests.integerType noType do
    throw (.message "unsupported: conditional result and branches must be direct integers")
  let coreTest ← test
  let binders ← freshBinders
  let coreYes ← convertBranch bindings yesType resultType yes
  let coreNo ← convertBranch bindings noType resultType no
  return finish logical location binders coreTest coreYes coreNo

end Silmaril.Cerberus.Elaboration.Conditionals
