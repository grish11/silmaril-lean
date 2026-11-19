module

import Silmaril.Cerberus.Elaboration.Statements.Thms

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Construction

-- Pinned translation.lem:3908–3911 uses the full return CType and does not
-- translate the integer child or allocate a discarded wrapper on this path.
private def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def pointerType : Ctype := .mk [.loc (.point "return.c" 1 1)]
  (.pointer ⟨false, false, false⟩ intType)
private def label : Sym := ⟨⟨[]⟩, 10, .return_⟩
private def object : Sym := ⟨⟨[]⟩, 11, .objectAddress "local"⟩
private def location : Loc := .point "return.c" 2 3
private def environment : Statements.Environment := ⟨pointerType, label, false⟩
private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 200⟩ .normal "Driver"
private def literal (n : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] location
    (.const (.integer (.iconstant n .decimal none)))
private def action (n : Int) := Statements.returnExpression Target.pinnedApple Target.emptyEnvironment []
  environment (literal n) location

example : (State.run (action 0) context).1 =
    .ok (Construction.run label [specified (nullptr pointerType)]) := by cbv
example : (State.run (action 0) context).2.freshness.next = 100 := by cbv
-- The exact captured object kill precedes the transfer; no object lifetime is
-- silently discarded merely because the returned value is null.
example : (State.run (State.withBlockObjects [(object, (⟨false, false, false⟩, intType))] (action 0)) context).1 =
    .ok ([], [], Lifetimes.returnRun location label [(object, intType)]
      [specified (nullptr pointerType)]) := by cbv
-- A nonzero integer is not a supported pointer return conversion.
example : (State.run (action 1) context).1 =
    .error (.message "unsupported: pointer return from nonpointer expression") := by cbv
example : (State.run (Statements.returnExpression {Target.pinnedApple with cheri := true}
    Target.emptyEnvironment [] environment (literal 0) location) context).1 =
    .error (.message "unsupported: CHERI pointer return") := by cbv
example : (State.run (Statements.returnExpression Target.pinnedApple Target.emptyEnvironment []
    {environment with noreturn := true} (literal 0) location) context).1 =
    .error (.message "noreturn statement elaboration is not ported") := by cbv

-- Compare the complete generated pointer comparison, including allocation
-- before child translation, unsequenced execution and the precise UB fallback.
private def leftPointer : State.ElabM Effect := pure (pureEffect (specified (nullptr intType)))
private def comparison (ne : Bool) := State.run
  (Comparisons.pointers Target.pinnedApple ne location leftPointer leftPointer) context
private def wrapped (n : Nat) (type : BaseType) : Pat :=
  symbolPattern ⟨⟨[]⟩, n, .none⟩ type
private def value (n : Nat) : Pure := symbolPure ⟨⟨[]⟩, n, .none⟩
private def expectedComparison (ne : Bool) : Effect :=
  weakSequence (.mk [] (.ctor .tuple [wrapped 100 (.loaded .pointer), wrapped 101 (.loaded .pointer)]))
    (unseq [pureEffect (specified (nullptr intType)), pureEffect (specified (nullptr intType))])
    (caseEffect (.mk [] () (.ctor .tuple [value 100, value 101]))
      [(.mk [] (.ctor .tuple [specifiedPattern (wrapped 102 (.object .pointer)),
          specifiedPattern (wrapped 103 (.object .pointer))]),
        weakSequence (wrapped 104 .boolean)
          (memoryOperation (if ne then .ptrNe else .ptrEq) [value 102, value 103])
          (pureEffect (standardPure "§6.5.9#3" (Comparisons.booleanInteger (value 104))))),
       (wildcard (.tuple [.loaded .pointer, .loaded .pointer]),
         pureEffect (undefined location (.UB_CERB004_unspecified .UB_unspec_equality_both_arith_or_ptr)))])
example : (comparison false).1 = .ok (expectedComparison false) := by cbv
example : (comparison true).1 = .ok (expectedComparison true) := by cbv
example : (comparison false).2.freshness.next = 105 := by cbv
example : (State.run (Comparisons.pointers {Target.pinnedApple with cheri := true}
    false location leftPointer leftPointer) context).1.isOk = false := by cbv
