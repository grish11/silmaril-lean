module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Holds10

/-!
# 1.0 leg 3: the open part outside round 4's invariants

`Sim10.Utf8Strip10.Task.unstripStep10` assumes only that the image of the source is typed in
`utf8Env10T (fwdB10 nd r)`. Under round 4's invariants (`Plain10`, `GSetOk`, `MemsAligned10`) it
is `XSwap.unstripStep10_inv`, which does not use its stripped-step hypothesis. So the frozen
statement reduces to configurations that violate one of them:

* **`Task.unstripStep10Out`** (frozen, open): `Task.unstripStep10` with
  `¬ (Plain10 c.code ∧ GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store)` added.
* **`unstripStep10_of_out`**: `Task.unstripStep10Out → Task.unstripStep10`.
* **`unstripStep10Out_of_unstripStep10`**: the converse; the two are equivalent, so nothing is
  lost by the restatement.

`MemsAligned10` cannot simply be dropped from the forward theorem (`not_wholeStepFwd10_unaligned`);
whether the stripped-step hypothesis rules out those configurations is what remains.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Config HostSemantics Step)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 fwdB10)

/-- **Leg 3 for 1.0 outside round 4's invariants** (frozen, open): `Task.unstripStep10` at
configurations whose code is not `Plain10`, or that violate `GSetOk`, or whose memories are not
aligned. -/
def Task.unstripStep10Out : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice)
    (host : HostSemantics H) (c c' : Config H),
    Typed10 (utf8Env10T (fwdB10 nd r)) hn c →
    ¬ (Plain10 c.code ∧ GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store) →
    Step host c c' →
      SStepB (utf8Env10T (fwdB10 nd r)) (configV hn (stripConfig10 c))
          (configV hn (stripConfig10 c')) →
        SStepB (utf8Env10T (fwdB10 nd r)) (configV hn c) (configV hn c')

/-- **`Task.unstripStep10` from its part outside round 4's invariants.** -/
theorem unstripStep10_of_out (h : Task.unstripStep10Out) : Task.unstripStep10 := by
  intro H hn nd r host c c' hc hs hss
  by_cases hi : Plain10 c.code ∧ GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store
  · exact Sim20.XSwap.unstripStep10_inv hc hi.1 hi.2.1 hi.2.2 hs hss
  · exact h H hn nd r host c c' hc hi hs hss

/-- The restatement loses nothing: `Task.unstripStep10` gives `Task.unstripStep10Out`. -/
theorem unstripStep10Out_of_unstripStep10 (h : Task.unstripStep10) : Task.unstripStep10Out :=
  fun H hn nd r host c c' hc _ hs hss => h H hn nd r host c c' hc hs hss

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
