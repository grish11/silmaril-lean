module

public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Wasm.Component.InstExport.Defs
public import Silmaril.Wasm.Component.InstEngine.Defs
public import Silmaril.Wasm.SingleThreaded.Interface
import Silmaril.Proofs.Wasm.Component.InstRef.Ref
import Silmaril.Proofs.Wasm.Component.InstRef.Det

/-!
# Start functions: the instantiating IR against the reference machine, on litmus components

All proved. Each theorem pairs a play of the instantiating IR `Comp.denI (core3SemI P)` of
`c.toComp` with a run of the reference machine on `c.toRef`, **executed**: the reference side is
a kernel evaluation (`decide +kernel`) of the reference machine's executable drivers
(`LinkedSession.sessSummary`, `callSummaryI`, a trap summary over the Core 3.0 stepper),
turned into behaviours by the drivers' soundness theorems. Proofs in
`Silmaril.Proofs.Wasm.Component.InstRef`.

* `callSI_agree` (every profile `P`): the IR instantiation of `callSI` makes the host call
  `f(u32 1)`, answered `()`, and is ready; the reference machine, under the logging host
  `embL`, instantiates `callSI` (an `InstResult.instance`, no export call) with the host log
  `logOfCalls [f(u32 1) ↦ ()]`, the same call. `callSI_asks_det`: at a deterministic profile,
  the host calls of **every** IR play are a prefix of `[f(u32 1)]`.
* `globSI_agree` (every profile `P`): the IR instantiation of `globSI` is ready, and `get()`
  is then answered `u32 42`; the reference machine's `get()` after instantiation returns
  `u32 42`.
* `trapSI_agree` (every profile `P`): the IR instantiation of `trapSI` fails; the reference
  machine's instantiation traps (`InstResult.traps`). `trapSI_denX`: at a deterministic profile
  the IR export phase of `trapSI` never answers.

**Scope.** These are agreements on three litmus components, each pairing one IR play with one
reference run (both machines are existential: a set of plays, a set of behaviours). The
reference runs are at the Core 3.0 stepper of `core3 neverFail` with the first scheduling
oracle. A general theorem relating `Comp.denI (core3SemI P)` to the reference machine's
instantiation on the `SimpleI` fragment (every start function, every host) is not proved here;
the existing reference soundness theorems for start functions (`SimpleI.sound_startS`) assume
that the start function makes no import call (`ImpModule.StartNoCall`), which `callSI` does
not satisfy.
-/

public section

namespace Silmaril.Wasm.Component.InstRef

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **A start function calling a host import: the IR and the reference machine make the same
host call.** -/
theorem callSI_agree (P : Profile) :
    instPlay (F := sigU) [⟨fV, unitV⟩] (InstAns.ready (R := Unit)) ∈
        callSI.toComp.denI (core3SemI P) ∧
      (([] : List (Option (List Value.Val))), ((), logOfCalls [⟨fV, unitV⟩])) ∈
        LinkedSession.sessRunBehaviours first.prof (Host.ofEmbedder embL) ((), []) callSI.toRef
          callSI.imports [] :=
  ⟨by
    rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
    exact Silmaril.Proofs.Wasm.Component.InstRef.callSI_inst P,
   Silmaril.Proofs.Wasm.Component.InstRef.callSI_ref⟩

/-- **At a deterministic profile, the IR's host calls of `callSI` are a prefix of
`[f(u32 1)]`**, in every play. -/
theorem callSI_asks_det (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ callSI.toComp.denI (core3SemI (profile o))) : lowerAsks p <+: [fV] :=
  Silmaril.Proofs.Wasm.Component.InstRef.callSI_asks hp

/-- **A start function's write, read by an export: both machines answer `get()` with `42`.** -/
theorem globSI_agree (P : Profile) :
    ([askInst, ansInst .ready, askEx (0, .vals []), ansEx (0, .vals []) (some (.vals [.u32 42]))] :
        List (Move sigU sigUI)) ∈ globSI.toComp.denI (core3SemI P) ∧
      Outcome.returns (some ([Silmaril.Wasm.Component.Val.u32 42].map toRefVal)) ∈
        exportBehavioursI first.prof
          (Host.ofEmbedder Silmaril.Wasm.Component.Reference.Litmus.embI) () globSI.toRef
          globSI.imports "get" [] :=
  ⟨Silmaril.Proofs.Wasm.Component.InstRef.globSI_get P,
   Silmaril.Proofs.Wasm.Component.InstRef.globSI_ref⟩

/-- **A trapping start function: the IR instantiation fails and the reference machine's
instantiation traps.** -/
theorem trapSI_agree (P : Profile) :
    ([askInst, ansInst (.fail ())] : List (Move sigU sigUI)) ∈
        trapSI.toComp.denI (core3SemI P) ∧
      InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embT) (initConfig ())
        trapSI.toRef [] :=
  ⟨Silmaril.Proofs.Wasm.Component.InstRef.trapSI_inst P,
   Silmaril.Proofs.Wasm.Component.InstRef.trapSI_ref⟩

/-- **At a deterministic profile, the IR export phase of `trapSI` never answers.** -/
theorem trapSI_denX (o : GrowOracle) : trapSI.toComp.denX (core3SemI (profile o)) = ⊥ :=
  Silmaril.Proofs.Wasm.Component.InstRef.trapSI_denX

end Silmaril.Wasm.Component.InstRef
