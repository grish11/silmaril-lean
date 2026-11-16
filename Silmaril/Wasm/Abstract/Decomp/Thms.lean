module

public import Silmaril.Wasm.Abstract.Decomp.Defs
public import Silmaril.Wasm.Abstract.Closing.Thms
public import Silmaril.Wasm.Interp.Diverge.Thms
public import Silmaril.Games.Abstract.Module.Thms
import Silmaril.Proofs.Wasm.Abstract.Decomp.Native
import Silmaril.Proofs.Wasm.Abstract.Decomp.Bridge
import Silmaril.Proofs.Wasm.Abstract.Decomp.Core

/-!
# Decomposing divergence; the enriched closing against Core 3.0: theorems

**Native decomposition, any store.**

* `funDiv_local_or_reach`: a diverging call either diverges *within its own
  function* (`wasmLocalDiv`: every callee terminates; silent loops, and loops
  calling returning functions forever) or reaches, after a terminating
  prefix, a call that diverges.
* `funDiv_path_or_chain`: iterating, a diverging call reaches a locally
  diverging call by finitely many descents (`BodyPath`), or starts an
  infinite chain of descents. The converse for paths is `funDiv_of_path`.

**Representation bridge.** A native descent is a descent of the open module
(`bodyReach_iff_descends`): `BodyReach x y ↔ Shape.Descends wasmOpen
(Shape.close wasmOpen) x [] y`, for a typed `x`.

**Against Core 3.0** (closed host; typed, native, arity-checked stores; every
profile):

* `diverges_iff_path_or_chain`: Core divergence of an invocation is a
  `Shape.DescPath` of `wasmOpen` to a locally diverging call, or a
  `Shape.DivChain` of `wasmOpen`. These are the two kinds of divergence, kept
  apart.
* **`wasmFun_eq_closedDL`**: the Core 3.0 abstract function is the enriched
  closing `Shape.closeDL wasmOpen wasmLocalDiv`.
* `wasmClosedDL_of_ne_div`: off `div`, the enriched closing is `close wasmOpen`
  (the closed outcomes, `close_wasmOpen`). So the enrichment changes nothing
  about returns, exceptions and traps.

`closeD wasmOpen` alone is sound (`closeD_subset_wasmFun`). It is not
complete, because it misses local divergence; `closeDL` adds exactly that.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **A diverging call diverges within its function, or reaches a diverging
call.** Any store. -/
theorem funDiv_local_or_reach {x : (wasmOShape H).self.Op} (h : Interp.FunDiv x.2.2 x.1 x.2.1) :
    wasmLocalDiv x ∨ ∃ y, BodyReach x y ∧ Interp.FunDiv y.2.2 y.1 y.2.1 :=
  Silmaril.Proofs.Wasm.Abstract.Decomp.callDiv_decomp h

/-- **A diverging call reaches local divergence by finitely many descents, or
starts an infinite chain of descents.** Any store. -/
theorem funDiv_path_or_chain {x : (wasmOShape H).self.Op} (h : Interp.FunDiv x.2.2 x.1 x.2.1) :
    (∃ z, BodyPath x z ∧ wasmLocalDiv z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, BodyReach (g n) (g (n + 1)) :=
  Silmaril.Proofs.Wasm.Abstract.Decomp.callDiv_path_or_chain h

/-- A descent path to local divergence diverges. Any store. -/
theorem funDiv_of_path {x z : (wasmOShape H).self.Op} (h : BodyPath x z) (hz : wasmLocalDiv z) :
    Interp.FunDiv x.2.2 x.1 x.2.1 :=
  Silmaril.Proofs.Wasm.Abstract.Decomp.callDiv_of_path h hz

/-- **Native descents are descents of the open module.** -/
theorem bodyReach_iff_descends {x y : (wasmOShape H).self.Op}
    (hx : ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), x.2.2.funcs[x.1]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs)) :
    BodyReach x y ↔ Shape.Descends wasmOpen (Shape.close wasmOpen) x [] y :=
  Silmaril.Proofs.Wasm.Abstract.Decomp.bodyReach_iff_descends hx

/-- **Core 3.0 divergence decomposes** into a descent path to local divergence
or a divergence chain of the open module. -/
theorem diverges_iff_path_or_chain {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Diverges P closedHost (invoke s a vs) ↔
      (∃ z, Shape.DescPath wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ [] z ∧ wasmLocalDiv z) ∨
        Shape.DivChain wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ [] :=
  Silmaril.Proofs.Wasm.Abstract.Decomp.diverges_iff_path_or_chain hs hF hS hok P

/-- **The Core 3.0 abstract function is the enriched closing of the open
module.** -/
theorem wasmFun_eq_closedDL {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    wasmFun P closedHost a s vs = wasmClosedDL a s vs :=
  Silmaril.Proofs.Wasm.Abstract.Decomp.wasmFun_eq_closedDL hs hF hS hok P

/-- **Off `div`, the enriched closing is the plain closing** (any store). -/
theorem wasmClosedDL_of_ne_div {s : Store H} {a : Nat} {vs : List Val}
    {y : CallBeh Sig.empty (Store H) (List Val ⊕ Nat)} (hy : y.2 ≠ .div) :
    y ∈ wasmClosedDL a s vs ↔ y ∈ Shape.close wasmOpen a s vs :=
  Shape.mem_closeDL_of_ne_div hy

end Silmaril.Wasm.Abstract
