module

public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs
public import Silmaril.Wasm.Component.InstWired.Defs

/-!
# The behavioural bridge on import-wired binaries: the reference half

`DecoderBridge.Sem` states the behavioural goals `Task.failAdequacy` and `Task.startAdequacy`
(the IR instantiation of a binary against the reference machine on the REF reading). This module
splits the failure goal, on a sub-fragment, into the IR half (proved, `Sim.Thms`) and a
reference half (open), stated on **core engine runs** rather than on IR plays.

## The sub-fragment

`HostWired r` (decidable: `hostWired r = true`): the REF reading `r` is in the fragment
(`refRead r = some R`) and every import of every core instantiation is wired, in `R`, to one of
the component's function imports (`Impl.Scoped R.imports.length`): through `canon lower` of an
import, as in both test binaries. So no core instance imports a function of another core
instance (cross-instance calls, which the reference machine makes inside one shared core store,
are excluded). On such binaries the IR reading is import-wired (`InstWired.ImportWired`), and
its instantiation plays are node by node (`InstWired.nodesInst_of_denI`).

## The node outcomes

`NodeQuiet a cm args` (at the IR profile `profile neverFail`): the engine instance of the
decoded module `cm` (`Param.instOfI (core3P …) (Binary.coreModule cm) …`, before its start
function) instantiates with answer `a` (`InstWired.EngineInst`: no instance, no start function,
or a start run returning or trapping), and each of its import calls during the start function is
answered at once by its wiring `args` (no host call: a trap of the argument lowering).

## The goals

* `Task.failAdequacyWired`: `Task.failAdequacy` for binaries whose REF reading is `HostWired`
  (the original `Task.failAdequacy` is kept: it has no fragment hypothesis);
* `Task.failRefWired`: **the reference half**: for such a binary whose IR reading has the
  core nodes `ps`, if for some `k` the nodes before `k` are `NodeQuiet .ready` and node `k` is
  `NodeQuiet (.fail ())`, the reference machine traps under the logging host. Its hypotheses
  are facts about core engine runs of the decoded modules, one module at a time; its conclusion
  is about the reference machine. What it needs is the simulation of the reference machine's
  instantiation (`Instantiate.instantiateDef`, the shared core store, `runStart`) by those runs.

`Sim.Thms.failAdequacyWired_of`: `Task.failRefWired → Task.failAdequacyWired` (proved).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- `Impl.Scoped`, as a Boolean. -/
def scopedB (e : Nat) (im : Impl) : Bool :=
  match im.target with
  | .call r => decide (r < e)
  | .const _ => true

/-- Every import of every core instantiation of the symbolic reading is wired to an import. -/
def rstWired (R : RSt) : Bool := R.nodes.all fun p => p.2.all (scopedB R.imports.length)

/-- The sub-fragment, as a Boolean (kernel-checkable). -/
def hostWired (r : RefComponent) : Bool := (refRead r).any rstWired

/-- **Import-wired REF readings**: in the fragment, and every core instantiation's imports
are wired to the component's function imports. -/
def HostWired (r : RefComponent) : Prop := hostWired r = true

instance (r : RefComponent) : Decidable (HostWired r) :=
  inferInstanceAs (Decidable (hostWired r = true))

/-- **A quiet node outcome**: the engine instance of the decoded module `cm` answers `inst` with
`a` (at `profile neverFail`), each of its import calls answered at once by the wiring `args`
over the `n` imports. -/
def NodeQuiet (n : Nat) (a : InstAns Unit) (cm : Binary.CoreMod) (args : List Impl) : Prop :=
  ∃ ys : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload),
    EngineInst (core3P (profile neverFail))
      (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule cm)
        (CoreModule.imports cm) (CoreModule.exports cm))
      (CoreModule.imports cm) ys a ∧
    ∀ y ∈ ys, implsN n args (CoreModule.imports cm).length y.1 = .pure y.2

/-- **Refined open goal**: `Task.failAdequacy` on binaries whose REF reading is import-wired. -/
def Task.failAdequacyWired : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    HostWired r → c.imports = hostI →
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI)

/-- **Open goal, the reference half**: on an import-wired binary, if the core engine runs of its
decoded modules make the nodes before `k` ready and node `k` fail, each without a host call, the
reference machine's instantiation traps. -/
def Task.failRefWired : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (k : Nat) (hk : k < ps.length),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    HostWired r → c.imports = hostI → c.nodes = coreNodes ps →
    (∀ j (hj : j < k), NodeQuiet hostI.length .ready (ps[j]'(by omega)).1 (ps[j]'(by omega)).2) →
    NodeQuiet hostI.length (.fail ()) ps[k].1 ps[k].2 →
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI)

end Silmaril.Wasm.Component.DecoderBridge
