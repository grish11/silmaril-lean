module

public import Silmaril.Wasm.Abstract.PubViewExample.Thms
public import Silmaril.Wasm.Abstract.FunctorP.Thms
public import Silmaril.Wasm.Abstract.BodyStrat.Thms
import Silmaril.Proofs.Wasm.Abstract.PubOpenWitness.Basic

/-!
# Public equivalence does not imply open equivalence: a witness

`PubViewExample` has two exports, function `0` of `callMod` (`call 1`, where function `1` returns
`42`) and function `0` of `inlineMod` (`i32.const 42`). They are publicly equivalent through the
code-forgetting view `codeView` (`pubEquivV_inline`): the internal call is a Core step, and the
public interaction does not show it.

The **open presentation** `FunctorP.OpEquivP` compares code lists under every oracle by their
logged runs `EvalLXP` and pending calls `ReachXP`, and there **every call is an event**. It is
intensional: it records internal calls, which the public semantics hides. It is not the public
semantics. The two function-`0` bodies differ there:

* **the bodies** (`callMod_bodies`, `inlineMod_bodies`, `callStore_body`, `inlineStore_body`):
  the code that the logged frame `FrameLXP` runs for a function is `liftInstrs fn.body`, the
  `BExpr` lift of its Core body. The lift of `call 1` is `[.op (.call ⟨1⟩) []]` and the lift of
  `i32.const 42` is `[.op (.intConst .i32 42) []]`; these are the bodies of function `0` in the
  modules and in the stores of their instantiations;
* **open inequivalence** (`not_opEquivP_call_inline`): `[call 1]` has a pending call at the empty
  log, under every oracle, in a store and frame where index `1` names a function;
  `[i32.const 42]` makes no call event, so has no pending call at any log;
* **in the canonical game** (`toDStratBody_call_inline_ne`): their canonical body strategies
  differ (`BodyStrat.toDStratBody_denL_iff`);
* **the witness** (`public_not_open`): the two exports are publicly equivalent through
  `codeView`, and their bodies are not open-equivalent.

**Scope.** This is one witness: public equivalence through a view does not imply open
equivalence of the bodies. It is not a statement about contextual equivalence or full
abstraction, and the open presentation is not claimed to be adequate for the public semantics.
The open statements hold at every host function type `H` and are used at `H = Empty`.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.PubOpenWitness.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.PubOpenWitness

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.FunctorP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.BodyStrat Silmaril.Wasm.Abstract.PubViewExample
open Silmaril.Wasm.Numerics (Profile)

/-! ## The bodies -/

/-- The lifted bodies of the functions of `callMod`: `[call 1]`, then `[i32.const 42]`. -/
theorem callMod_bodies : callMod.funcs.map (fun fn => liftInstrs fn.body) =
    [[.op (.call ⟨1⟩) []], [.op (.intConst .i32 42) []]] := rfl

/-- The lifted bodies of the functions of `inlineMod`: `[i32.const 42]` twice. -/
theorem inlineMod_bodies : inlineMod.funcs.map (fun fn => liftInstrs fn.body) =
    [[.op (.intConst .i32 42) []], [.op (.intConst .i32 42) []]] := rfl

/-- Function `0` of `callStore` is Wasm code whose lifted body is `[call 1]`. -/
theorem callStore_body :
    ∃ (fi : FuncInst Empty) (fn : Func), callStore.funcs[0]? = some fi ∧ fi.code = .wasm fn ∧
      liftInstrs fn.body = [.op (.call ⟨1⟩) []] :=
  Silmaril.Proofs.Wasm.Abstract.PubOpenWitness.callStore_body

/-- Function `0` of `inlineStore` is Wasm code whose lifted body is `[i32.const 42]`. -/
theorem inlineStore_body :
    ∃ (fi : FuncInst Empty) (fn : Func), inlineStore.funcs[0]? = some fi ∧
      fi.code = .wasm fn ∧ liftInstrs fn.body = [.op (.intConst .i32 42) []] :=
  Silmaril.Proofs.Wasm.Abstract.PubOpenWitness.inlineStore_body

/-! ## Open inequivalence -/

/-- **`[call 1]` and `[i32.const 42]` are not open-equivalent**: the call is an event, so the
first has a pending call where the second has none. -/
theorem not_opEquivP_call_inline {H : Type} :
    ¬ OpEquivP H [.op (.call ⟨1⟩) []] [.op (.intConst .i32 42) []] :=
  Silmaril.Proofs.Wasm.Abstract.PubOpenWitness.not_opEquivP_call_inline

/-- **Their canonical body strategies differ.** -/
theorem toDStratBody_call_inline_ne {H : Type} :
    toDStratBody (denL (H := H) [.op (.call ⟨1⟩) []]) ≠
      toDStratBody (denL [.op (.intConst .i32 42) []]) :=
  fun h => not_opEquivP_call_inline ((toDStratBody_denL_iff _ _).mp h)

/-! ## The witness -/

/-- **Public does not imply open.** The exports at function `0` of `callStore` and `inlineStore`
are publicly equivalent through `codeView`, which hides the internal call; their bodies `[call 1]`
and `[i32.const 42]` are not `OpEquivP`, because the open presentation logs the internal call as
an event. A witness only: not contextual full abstraction. -/
theorem public_not_open (P : Profile) (host : HostSemantics Empty) :
    PubEquivV codeView P host InvOk callStore 0 inlineStore 0 ∧
      ¬ OpEquivP Empty [.op (.call ⟨1⟩) []] [.op (.intConst .i32 42) []] :=
  ⟨pubEquivV_inline P host, not_opEquivP_call_inline⟩

end Silmaril.Wasm.Abstract.PubOpenWitness
