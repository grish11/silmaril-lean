module

public import Silmaril.WasmSpec.Adder.Thms
public import Silmaril.Proofs.WasmSpec.Add3.Tactic

/-!
# Wasm specification library: `Add3` v1, results

Solutions of `Spec` (see `manifest.toml`):

* `tactic`: `Silmaril.WasmSpec.Add3.spec_tactic` (`Silmaril.Proofs.WasmSpec.Add3.Tactic`).

Canonical results:

* `Silmaril.WasmSpec.Add3.spec : Spec`: correct for **every** adder meeting
  `Adder.CallSpec`;
* `Silmaril.WasmSpec.Add3.spec_with_adder`: linked with `Adder`'s own `$add`
  (`Adder.callSpec`): if function `0` of the instance is an `Adder` function
  instance, `$add3` returns `x + y + z`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Add3

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Logic.Core

/-- The canonical solution: the kernel-checked `tactic` one. -/
theorem spec : Spec := spec_tactic

/-- `$add3` linked with `Adder`'s `$add`. -/
theorem spec_with_adder {H : Type} {P : Profile} {host : HostSemantics H} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {s : Store H} {m : ModuleInst}
    (hcode : fi.code = .wasm Adder.addFunc) (he : Expand fi.type (.func ps rs))
    (hps : ps.length = 2) (hrs : rs.length = 1) (hm : m.funcs[0]? = some a)
    (hs : s.funcs[a]? = some fi) (x y z : BitVec 32) :
    WP P host s (Frame.forCall m [.i32 x, .i32 y, .i32 z] add3Func.locals)
      (expression add3Func.body) (funcPost P host 1 fun s' r => s' = s ∧ r = [.i32 (x + y + z)]) :=
  spec P host a (fun s => s.funcs[a]? = some fi) s m
    (Adder.callSpec (fun _ h => h) hcode he hps hrs) hm (by rw [hs]; rfl) hs x y z

end Silmaril.WasmSpec.Add3

/-- info: 'Silmaril.WasmSpec.Add3.spec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Add3.spec_tactic

/-- info: 'Silmaril.WasmSpec.Add3.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Add3.spec

/-- info: 'Silmaril.WasmSpec.Add3.spec_with_adder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.Add3.spec_with_adder
