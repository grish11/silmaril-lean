module

public import Silmaril.Wasm.Game.Accept.Complete.Thms

/-! # One-call module acceptors are complete for no infinite specification: examples -/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept.Examples

open Silmaril.Formats.Accept

/-- No one-call module acceptor accepts every byte string. -/
example (A : ModuleAcceptor) : ¬ Lang.Complete A.lang (Set.univ : Set (List UInt8)) :=
  A.not_complete_of_infinite Set.infinite_univ

/-- Nor every string of zeros. -/
example (A : ModuleAcceptor) :
    ¬ Lang.Complete A.lang (Set.range fun n => List.replicate n (0 : UInt8)) :=
  A.not_complete_of_infinite (Set.infinite_range_of_injective fun _ _ h => by
    simpa using congrArg List.length h)

end Silmaril.Wasm.Game.Accept.Examples
