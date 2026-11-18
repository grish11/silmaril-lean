module

public import Silmaril.Cerberus.Elaboration.Members.Defs

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def tag : Sym := ⟨⟨[]⟩, 7, .id "record"⟩
private def aggregate : Ctype := .mk [] (.struct tag)
private def pointer : Ctype := .mk [] (.pointer ⟨false, false, false⟩ aggregate)
private def member : Identifier := .mk .unknown "value"
private def child : State.ElabM Effect := do
  let _ ← State.freshDescription .none
  return pureEffect (specified (integer 1))
private def translated (strict : Bool) := State.run
  (Members.pointerMember false strict .unknown pointer member child) context

-- Both modes allocate all four upstream wrappers before translating the child.
example : (translated false).2.freshness.next = 105 := by cbv
example : (translated true).2.freshness.next = 105 := by cbv
example : (translated false).1.isOk = true := by cbv
example : (translated true).1.isOk = true := by cbv
example : Members.aggregateTag aggregate = .ok tag := rfl
example : Members.aggregateTag (.mk [] (.atomic aggregate)) = .ok tag := rfl
example : (State.run (Members.pointerMember true false .unknown pointer member child)
    context).2.freshness.next = 100 := by cbv
example : (State.run (Members.pointerMember true false .unknown pointer member child)
    context).1.isOk = false := by cbv
example : (State.run (Members.pointerMember false false .unknown aggregate member child)
    context).1.isOk = false := by cbv

private def branch (strict : Bool) (index : Nat) : Option Effect :=
  match (translated strict).1 with
  | .ok (.mk _ (.sseq _ _ (.mk _ (.case_ _ branches)))) => (branches[index]?).map Prod.snd
  | _ => none
private def objectSymbol : Sym := ⟨⟨[]⟩, 101, .none⟩
private def testSymbol : Sym := ⟨⟨[]⟩, 102, .none⟩

-- Unspecified pointer values retain their upstream UB in both modes.
example : branch false 0 = some (pureEffect
    (undefined .unknown (.UB_CERB004_unspecified .UB_unspec_memberofptr))) := by cbv
example : branch true 0 = branch false 0 := by cbv
-- Non-strict mode permits the upstream non-ISO member shift explicitly.
example : branch false 1 = some (pureEffect
    (memberShift (symbolPure objectSymbol) tag member)) := by cbv
-- Strict mode checks dereference validity and retains the invalid-pointer UB.
example : branch true 1 = some
    (weakSequence (symbolPattern testSymbol .boolean)
      (memoryOperation .ptrValidForDeref [ailCtype aggregate, symbolPure objectSymbol])
      (pureEffect (ifPure (symbolPure testSymbol)
        (memberShift (symbolPure objectSymbol) tag member)
        (standardUndefined .unknown "§6.5.2.3#4, sentence 4" .UB043_indirection_invalid_value)))) := by cbv

private def direct (lvalue : Bool) := State.run
  (Members.directMember false lvalue .unknown aggregate member child) context

-- Address projection allocates one wrapper before the child. Loaded projection
-- allocates its second wrapper after the child, as in the pinned equation.
example : (direct true).2.freshness.next = 102 := by cbv
example : (direct false).2.freshness.next = 103 := by cbv
example : (direct true).1 = .ok
    (addStandard "§6.5.2.3#3, sentence 2"
      (strongSequence (symbolPattern ⟨⟨[]⟩, 100, .none⟩ (.object .pointer))
        (pureEffect (specified (integer 1)))
        (pureEffect (memberShift (symbolPure ⟨⟨[]⟩, 100, .none⟩) tag member)))) := by cbv
private def directBranch (index : Nat) : Option Pure :=
  match (direct false).1 with
  | .ok (.mk _ (.sseq _ _ (.mk _ (.pure (.mk _ _ (.case_ _ branches)))))) =>
      (branches[index]?).map Prod.snd
  | _ => none
example : directBranch 0 = some
    (undefined .unknown (.UB_CERB004_unspecified .UB_unspec_rvalue_memberof)) := by cbv
example : directBranch 1 = some
    (memberOf tag member (symbolPure ⟨⟨[]⟩, 102, .none⟩)) := by cbv
example : (State.run (Members.directMember true true .unknown aggregate member child)
    context).1.isOk = false := by cbv
example : (State.run (Members.directMember false true .unknown pointer member child)
    context).1.isOk = false := by cbv
example : (State.run (Members.directMember false true .unknown (.mk [] (.atomic aggregate))
    member child) context).1.isOk = true := by cbv
