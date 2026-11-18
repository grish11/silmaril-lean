module

public import Silmaril.Cerberus.Elaboration.Constants.Defs

/-! The non-CHERI pointer-member equation from pinned Cerberus
`translation.lem:2909–2962`, commit
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. Strict pointer arithmetic is an explicit input;
non-strict mode retains the upstream non-ISO branch instead of asserting
validity. Four wrappers precede child translation in either mode. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Members
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

def aggregateTag : Ctype → Except String Sym
  | .mk _ (.struct tag) | .mk _ (.union tag) => .ok tag
  | .mk _ (.atomic (.mk _ (.struct tag)))
    | .mk _ (.atomic (.mk _ (.union tag))) => .ok tag
  | _ => .error "ill-typed AilEmemberofptr: expected pointer to struct or union"

def pointerReferent : Ctype → Except String (Ctype × Sym)
  | .mk _ (.pointer _ type) => do return (type, ← aggregateTag type)
  | _ => .error "ill-typed AilEmemberofptr: expected pointer"

def pointerMember (cheri strict : Bool) (location : Loc) (pointerType : Ctype)
    (member : Identifier) (child : State.ElabM Effect) : State.ElabM Effect := do
  if cheri then throw (.message "unsupported: CHERI pointer-member elaboration")
  let (referent, tag) ← Constants.liftResult (pointerReferent pointerType)
  let loaded ← State.wrappedFreshSymbol (.loaded .pointer)
  let object ← State.wrappedFreshSymbol (.object .pointer)
  let test ← State.wrappedFreshSymbol .boolean
  let result ← State.wrappedFreshSymbol (.object .pointer)
  let coreChild ← child
  let _ := result -- Upstream allocates this wrapper even in the non-CHERI branch.
  let specifiedBranch := if strict then
    weakSequence test.pattern (memoryOperation .ptrValidForDeref [ailCtype referent, object.expression])
      (pureEffect (ifPure test.expression (memberShift object.expression tag member)
        (standardUndefined location "§6.5.2.3#4, sentence 4" .UB043_indirection_invalid_value)))
    else pureEffect (memberShift object.expression tag member)
  return addStandard "§6.5.2.3#4, sentence 2" (strongSequence loaded.pattern coreChild
    (caseEffect loaded.expression
      [(Construction.unspecifiedPattern (wildcard .ctype),
        pureEffect (undefined location (.UB_CERB004_unspecified .UB_unspec_memberofptr))),
       (Construction.specifiedPattern object.pattern, specifiedBranch)]))

end Silmaril.Cerberus.Elaboration.Members
