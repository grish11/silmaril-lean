module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Basic
public import Silmaril.Wasm.Abstract.SSAFragment.Thms

/-!
# The fragment denotation against Core 3.0

A Core 3.0 call site holding a structured native fragment function has
exactly the behaviours read off the abstract body of the function: composed
from `IsFragmentSite.callSem` (Core behaviours are the fragment runs) and
`toAFun_denFunc` (the abstract body's denotation is the fragment runs).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
  Silmaril.Wasm.Abstract.FragBody Silmaril.Wasm.SSA Silmaril.Elgot.ITree
  Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {E : Sig.{0}} {S : Type 1}

theorem callSem_eq_den {H : Type} {x : Silmaril.Wasm.Abstract.CallSite H} {ft : FuncType}
    {bf : Binaryen.BFunc} {f : FragFunc} (hx : Silmaril.Wasm.Abstract.IsFragmentSite x ft bf f)
    {vs : List Val} (hok : InvokeOk x.store x.addr vs) (P : Numerics.Profile) (st : S) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧
      Silmaril.Wasm.Abstract.callSem P x vs =
        (fun y => outBeh (endFOut y.2)) '' toAFun (denFunc f : Hom E S PUnit.{2} _ _) st ⟨args⟩ := by
  obtain ⟨args, hv, -, h⟩ := hx.callSem hok P
  refine ⟨args, hv, ?_⟩
  rw [h, toAFun_denFunc]
  ext b
  constructor
  · rintro (⟨o, ho, rfl⟩ | ⟨rfl, hno⟩)
    · exact ⟨([], foutEnd o st), .inl ⟨o, ho, rfl⟩, by cases o <;> rfl⟩
    · exact ⟨([], .div), .inr ⟨rfl, hno⟩, rfl⟩
  · rintro ⟨y, (⟨o, ho, rfl⟩ | ⟨rfl, hno⟩), rfl⟩
    · exact .inl ⟨o, ho, by cases o <;> rfl⟩
    · exact .inr ⟨rfl, hno⟩

end Silmaril.Proofs.Wasm.Abstract.FragBody
