module

public import Silmaril.Wasm.Component.InstTests.Defs
public import Silmaril.Wasm.Component.InstSem.Defs
public import Silmaril.Wasm.Component.InstExport.Defs
public import Silmaril.Wasm.SingleThreaded.Interface
import Silmaril.Proofs.Wasm.Component.InstTests.Bin

/-!
# Component test binaries: theorems

All proved; proofs in `Silmaril.Proofs.Wasm.Component.InstTests`. The bytes are lowered by
`Binary.parseComponent` (checked by the kernel's definitional check), then read by the
instantiating denotation `Comp.denI` over `Binary.coreModSemI P`: each core module is decoded and
run on the Core 3.0 engine at profile `P`, its start function at instantiation. This is the
reading of `Silmaril.Wasi.Accept.componentBytesSystemCore3I P` before its export phase. Plays
are over `sigU ↠ sigUI`: `askInst`/`ansInst a` are the instantiation question and its answer,
`.inl` moves are calls of the host import `f` (`fV k` is `f(u32 k)`), `askEx`/`ansEx` are export
calls.

**`starts.wasm`.**

* `parse_starts`: the bytes lower to `startsComp`;
* `starts_inst` (every profile `P`): `[inst, f(1), (), f(2), (), ready, get(), 42]` is a play:
  the start functions run in instance order, the first two calling the host, the third writing
  the global that the exported `get` then reads;
* `starts_denX_get` (every profile): in the export phase `Comp.denX`, `get()` is answered `42`;
* `starts_asks` (deterministic profiles `profile o`): in **every** play, the host calls are a
  prefix of `f(1), f(2)`: no other call, no other order, and no call in the export phase;
* `starts_complete` (deterministic profiles): a complete instantiation `[inst] ++ cs ++ [a]`
  whose host answers are those of the typed host `unitHost` makes exactly the calls
  `startsTrace` and ends `ready`;
* `starts_get` (deterministic profiles): every answer to `get()`, in every play, is `42`.

**`trap.wasm`.**

* `parse_trap`: the bytes lower to `trapComp`;
* `trap_inst` (every profile): `[inst, fail ()]` is a play;
* `trap_plays` (deterministic profiles): every play is a prefix of `[inst, fail ()]`, possibly
  followed by one Opponent move that is never answered; hence `trap_not_ready` (instantiation
  never succeeds), `trap_no_host_calls` (in particular the second instance's start function never
  calls `f(2)`), `trap_no_exports` (`get` is never answered) and `trap_denX` (the export phase is
  `⊥`).

**What is quantified.** Plays are finite. The existence statements give one play at every
profile; the exclusion statements are about every finite play at a deterministic profile
`profile o` (every `GrowOracle o`). A start function that never returns produces no move, so
divergence is not observed by these statements (at `profile o` the start runs of these modules
reach their normal forms, so they do not diverge, but that is not stated here). The host is
typed: `f` is answered `()` (`unitHost`); `starts_asks` and the `trap` statements hold whatever
the host answers. No async, resources or streams occur: the lowering rejects them.
-/

public section

namespace Silmaril.Wasm.Component.InstTests

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-! ## The bytes -/

/-- **`starts.wasm` lowers to `startsComp`.** -/
theorem parse_starts : Binary.parseComponent startsBytes = .ok startsComp :=
  Silmaril.Proofs.Wasm.Component.InstTests.parse_starts

/-- **`trap.wasm` lowers to `trapComp`.** -/
theorem parse_trap : Binary.parseComponent trapBytes = .ok trapComp :=
  Silmaril.Proofs.Wasm.Component.InstTests.parse_trap

/-! ## `starts.wasm` -/

/-- **Instantiation calls `f(1)`, then `f(2)`, is ready, and `get()` then answers `42`**, at
every profile. -/
theorem starts_inst (P : Profile) :
    instPlay (F := sigU) startsTrace .ready ++ [askEx getV, ansEx getV v42] ∈
      startsComp.denI (Binary.coreModSemI P) :=
  Silmaril.Proofs.Wasm.Component.InstTests.starts_inst_bin P

/-- **In the export phase, `get()` is answered `42`**, at every profile. -/
theorem starts_denX_get (P : Profile) :
    ([.inr (.ask getV), .inr (.ans getV v42)] : List (Move sigU sigU)) ∈
      startsComp.denX (Binary.coreModSemI P) :=
  Silmaril.Proofs.Wasm.Component.InstTests.starts_denX_bin P

/-- **The host calls of every play are a prefix of `f(1), f(2)`**, at a deterministic
profile. -/
theorem starts_asks (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ startsComp.denI (Binary.coreModSemI (profile o))) :
    lowerAsks p <+: startsTrace.map Sigma.fst :=
  Silmaril.Proofs.Wasm.Component.InstTests.starts_asks_bin hp

/-- **A complete instantiation answered by the typed host is `startsTrace`, then `ready`**, at
a deterministic profile. -/
theorem starts_complete (o : GrowOracle) {cs : List (Σ _ : sigU.Op, Option Payload)}
    {a : InstAns Unit}
    (hp : instPlay (F := sigU) cs a ∈ startsComp.denI (Binary.coreModSemI (profile o)))
    (hc : ∀ x ∈ cs, x.2 = unitHost x.1) : cs = startsTrace ∧ a = .ready :=
  Silmaril.Proofs.Wasm.Component.InstTests.starts_complete_bin hp hc

/-- **Every answer to `get()` is `42`**, at a deterministic profile. -/
theorem starts_get (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ startsComp.denI (Binary.coreModSemI (profile o))) {r : Option Payload}
    (hr : ansEx getV r ∈ p) : r = v42 :=
  Silmaril.Proofs.Wasm.Component.InstTests.starts_get_bin hp hr

/-! ## `trap.wasm` -/

/-- **The instantiation fails**, at every profile. -/
theorem trap_inst (P : Profile) :
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
      trapComp.denI (Binary.coreModSemI P) :=
  Silmaril.Proofs.Wasm.Component.InstTests.trap_inst_bin P

/-- **Every play is a prefix of `[inst, fail ()]`**, possibly followed by one Opponent move that
is never answered, at a deterministic profile. -/
theorem trap_plays (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) :
    p <+: [askInst, ansInst (.fail ())] ∨
      ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: [askInst, ansInst (.fail ())] ∧ x.IsO :=
  Silmaril.Proofs.Wasm.Component.InstTests.trap_plays_bin hp

/-- **The instantiation never succeeds**, at a deterministic profile. -/
theorem trap_not_ready (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) : ansInst .ready ∉ p := by
  intro h
  rcases Silmaril.Proofs.Wasm.Component.InstTests.trap_moves_bin hp _ h with h | h | h <;> cases h

/-- **No host call happens**: in particular `call2`'s start function never calls `f(2)`. -/
theorem trap_no_host_calls (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) : lowerAsks p = [] :=
  Silmaril.Proofs.Wasm.Component.InstTests.trap_asks_bin hp

/-- **The export `get` is never answered.** -/
theorem trap_no_exports (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) (q : sigU.Op) (r : Option Payload) :
    ansEx q r ∉ p := by
  intro h
  rcases Silmaril.Proofs.Wasm.Component.InstTests.trap_moves_bin hp _ h with h | h | h <;> cases h

/-- **The export phase is `⊥`**, at a deterministic profile. -/
theorem trap_denX (o : GrowOracle) : trapComp.denX (Binary.coreModSemI (profile o)) = ⊥ :=
  Silmaril.Proofs.Wasm.Component.InstTests.trap_denX_bin

end Silmaril.Wasm.Component.InstTests
