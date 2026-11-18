module

public import Silmaril.Wasm.Component.Reference.ListLift.Defs
import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Inst
import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Call

@[expose] public section

/-!
# Components whose exports take lists: results

**`acceptSound`**: every `ListComp` satisfies `AcceptSound`. For a well-formed component
(`Good`) whose module is instantiated as `Inst` assumes, every behaviour of the reference
machine (`core3P P`, the reference host, every component choice profile) that instantiates
`c.toRef`, calls an export on well-typed list values and returns `true` lowers the values
through the component's allocator and memory (`LParams`: allocator Core runs, alignment and
bounds, little-endian writes) to a store from which the lifted core function returns a nonzero
`i32`.

Proofs in `Silmaril.Proofs.Wasm.Component.Reference.ListLift`: the instantiation phase
(`instPhaseL`, `Inst*.lean`) and the call phase (`callPhaseL`, `Call.lean`, with the nested
allocator call in `Realloc.lean`, `store_list_into_range` in `StoreList.lean` and the element
and parameter lowering in `Lower.lean`), combined by `acceptSound_of_phases`.

Only accepting behaviours are characterised: traps, divergence and `false` answers impose
nothing. The typing hypotheses of `Inst` (`realloc`, `core`, `memI32`) are needed: the reference
machine does not check the types of flat results (see `ListComp.Inst`).
-/

namespace Silmaril.Wasm.Component.Reference.ListLift

/-- **Accepting calls of a list-taking component have a Core-level explanation.** -/
theorem acceptSound (c : ListComp) : AcceptSound c :=
  Silmaril.Proofs.Wasm.Component.Reference.ListLift.acceptSound_of_phases
    Silmaril.Proofs.Wasm.Component.Reference.ListLift.instPhaseL
    Silmaril.Proofs.Wasm.Component.Reference.ListLift.callPhaseL c

end Silmaril.Wasm.Component.Reference.ListLift
