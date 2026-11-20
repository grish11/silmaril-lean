module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.Wasm.Validation.Generic.Defs
public import Silmaril.Wasm.Validation.Generic.Signature.Defs

@[expose] public section

namespace Silmaril.Wasm.Generic.SSA

open Silmaril.Isotope.LambdaSSA
open Validation

/-- A declaration's types supply the real LambdaSSA value context and the
return label; trap is a separate label, not part of the Core result type. -/
abbrev DeclaredBody {τ : Type} (Φ : Type) [TypeFormers τ] [HasTy Φ τ] (trap : τ)
    (sig : Signature.Func τ) := { code : Region Φ // code.HasType sig.params.reverse [sig.result, trap] }

/-- Reinterpreting the type codes of one opcode set must preserve its actual
primitive signature and the constructors used in LambdaSSA typing. -/
structure TypeMap (Φ τ σ : Type) [TypeFormers τ] [TypeFormers σ] [HasTy Φ τ] [HasTy Φ σ] where
  run : τ → σ
  mapProduct : ∀ left right, run (product left right) = product (run left) (run right)
  mapSum : ∀ left right, run (coprod left right) = coprod (run left) (run right)
  mapUnit : run unit = unit
  mapEmpty : run empty = empty
  mapSrc : ∀ op : Φ, run (instrSrc op) = instrSrc op
  mapTrg : ∀ op : Φ, run (instrTrg op) = instrTrg op

/-- A partial encoding of the *external* signature. For example, SSA pairs or
sums may be legal internally and have no encoding as individual Core values. -/
structure Boundary (τ : Type) where
  arg : τ → Option CValType
  result : τ → Option (List CValType)
  trap : τ

/-- An SSA function at a fixed Core declaration, with independent type codes
for LambdaSSA. Parameters are in Wasm order; the SSA lookup order is reversed.
The two external labels are return and trap. SSA variables are not Core locals. -/
structure AtCore (Φ τ : Type) [TypeFormers τ] [HasTy Φ τ] (boundary : Boundary τ)
    (context : Context) (signature : DefType) where
  typeRef : Inductive.Bounded context.types signature
  params : List τ
  result : τ
  coreParams : List CValType
  coreResults : List CValType
  paramsOk : params.mapM boundary.arg = some coreParams
  resultOk : boundary.result result = some coreResults
  signatureOk : signature.funcType? = some (coreParams, coreResults)
  code : Region Φ
  typed : code.HasType params.reverse [result, boundary.trap]

def AtCore.syntax {Φ τ : Type} [TypeFormers τ] [HasTy Φ τ] {boundary : Boundary τ}
    {context : Context} {signature : DefType} (fn : AtCore Φ τ boundary context signature) :
    TypeIdx × Region Φ :=
  let ref : Intrinsic.Ref .type_ context.types signature := fn.typeRef.erase
  (ref.index, fn.code)

end Silmaril.Wasm.Generic.SSA
