module

public import Silmaril.Wasm.Abstract.StoreBody.Defs
import Silmaril.Proofs.Wasm.Abstract.StoreBody.Basic

/-!
# Folded Wasm bodies over the actual store: theorems

For the denotation `den`/`denList` of folded trees into `BodyM` over the actual
store (`Silmaril.Wasm.Abstract.StoreBody.Defs`):

* **Primitives are the interpreter's.** `run_flatK`: a lifted flat instruction
  runs to exactly the tree of `Binaryen.evalFlat`'s outcome on the current
  store: the new store and frame with its flow, the trap, or (no outcome)
  silent divergence. In particular the store effects of `global.set` and of
  integer `store` are `evalFlat`'s (`run_globalSet` as an example).
* **Loops are Elgot iteration.** `den_loop_unfold`: the fixpoint law unfolds a
  loop once.
* **Sound for the native interpreter.** `run_sound`: on call-free,
  `try_table`-free trees, every outcome of `Binaryen.run` (any fuel) is the
  abstract body's outcome, with the same final store, frame and flow (a trap
  as the trap effect).

**Not yet.** The converse (an abstract outcome is reached by the interpreter
with some fuel, and abstract divergence is exhaustion of every fuel), calls
(F4) and `try_table` (F5), and the connection to Core 3.0 through the
interpreter's adequacy.
-/

public section

namespace Silmaril.Wasm.Abstract.StoreBody

open Silmaril.Wasm Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core

variable {E : Sig.{0}} {H : Type}

/-- **The lifted primitive.** A flat instruction's body runs to the tree of the
native interpreter step on the current store. -/
theorem run_flatK (i : Instr) (f : Frame) (stk : List Val) (s : Store H) :
    ((flatK i f stk : M E H Res).run ⟨s⟩).run = evalTree (evalFlat s f stk i) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.run_flatK i f stk s

/-- Example of a store effect: `global.set` writes the global through
`Store.setGlobal`, as `evalFlat` does. -/
theorem run_globalSet (g : GlobalIdx) (f : Frame) (v : Val) (r : List Val) (s : Store H)
    {p : Nat × GlobalInst} (hg : s.global? f g = some p) :
    ((flatK (.globalSet g) f (v :: r) : M E H Res).run ⟨s⟩).run =
      Silmaril.Elgot.ITree.ret (.ok (⟨(f, .normal r)⟩, ⟨s.setGlobal p.1 v⟩)) := by
  rw [run_flatK]; simp [evalFlat, hg, evalTree]

/-- A loop unfolds once (the Elgot fixpoint law). -/
theorem den_loop_unfold (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (den (.loop bt body) f stk : M E H Res) =
      (loopBody bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => den (.loop bt body) c.down.1 c.down.2) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.den_loop_unfold bt body f stk

/-- **Sound for the native interpreter.** On call-free trees, every outcome of
`Binaryen.run`, at any fuel, is the abstract body's outcome. -/
theorem run_sound {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (hc : callFreeL es = true) (h : run n s f stk es = some r) :
    ((denList es f stk : M E H Res).run ⟨s⟩).run = evalTree (some r) :=
  Silmaril.Proofs.Wasm.Abstract.StoreBody.run_sound n hc h

end Silmaril.Wasm.Abstract.StoreBody
