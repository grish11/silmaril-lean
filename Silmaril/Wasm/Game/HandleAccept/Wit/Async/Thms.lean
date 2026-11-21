module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Async.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Endpoints.Thms

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Async

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine

variable {E : CoreEngine} {World Base : Type}

/-- Every sequence of old calls has the identical reference effect program, hence the same
execution and reply observations under any interpretation of its effects. This does not
project a mixed async run to an old run. -/
theorem runCalls_legacy (base : Base → P E World (List FlatValue)) (limits : Component.Limits)
    (quirks : Quirks) (calls : List Base) :
    runCalls base limits quirks (calls.map Sum.inl) = Prog.mapM base calls := by
  induction calls with
  | nil => rfl
  | cons call calls ih =>
    simp only [runCalls] at ih
    simp only [runCalls, List.map_cons, Prog.mapM, program, ih]

end Silmaril.Wasm.Game.HandleAccept.Wit.Async
