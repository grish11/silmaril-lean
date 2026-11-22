module

public import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Thms
public import Silmaril.Wasm.Component.Reference.Adequacy.Thms
import Silmaril.Wasm.Component.Reference.Sound.Thms

public section

namespace Silmaril.Wasm.Component.IntrinsicWiring

open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- An exact presentation of an adequate `Simple` component transports its terminating
single-call observer to the existing component game. Neither the type checker nor matching
interfaces establishes the instantiation or ABI premises in `Simple.Adequate`. -/
theorem Closed.terminal_iff {interface : ComponentType Nat Core3Extern}
    (typed : Closed .p2 core3Profile core3ModuleType? interface)
    {simple : Simple} (exactRef : typed.erase = simple.toRef) (adequate : simple.Adequate)
    (P : Profile) (prof : ProfileKind) (index : Fin simple.exports.length)
    {funcType : Types.FuncType Nat} (exposed : Exposure interface simple.exports[index].name (.func funcType))
    (args : List Val) (typedArgs : ValTy.checkList simple.exports[index].ty.params args = true)
    (outcome : Outcome) (terminal : outcome.Term) :
    outcome ∈ exportBehaviours prof (refHost P) () typed.erase [] interface.exports[exposed.index].1 (args.map toRefVal) ↔
      IRObs (k := simple.toComp.exports.length) (simple.toComp.den (modSem P))
        ⟨index, by simp [Simple.toComp]⟩ args outcome := by
  rw [exactRef, exposed.entry]
  exact ⟨Simple.sound P prof simple adequate.good adequate.floatFree adequate.inst adequate.arity index args typedArgs outcome,
    Simple.complete P prof simple adequate index args typedArgs outcome terminal⟩

end Silmaril.Wasm.Component.IntrinsicWiring
