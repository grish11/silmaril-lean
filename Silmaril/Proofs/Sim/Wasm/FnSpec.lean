module

public import Silmaril.Sim.Wasm.FnSpec.Defs
public import Silmaril.Sim.Wasm.Thms
public import Silmaril.Wasm.Verify.FnSpec.Thms

/-!
# Proofs: per-method soundness from `Verify.FnSpec`

Names are in `Silmaril.Sim.Wasm.ExportSim`, exported by `Silmaril/Sim/Wasm/FnSpec/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Wasm.ExportSim

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)

variable {C L V H : Type} {K : ExportSim C L V H} {B : Machine C L V}
  {R : Store H → B.St → Prop} {c : C}

/-- **Per-method soundness from `wasm_vc`**: the verification condition of the method's body
for `methodFnSpec`, a store relation that pins the method's code, and matching arities. -/
theorem methodOK_of_vc {K : ExportSim C L V Nat} {R : Store Nat → B.St → Prop} {n : Nat}
    {fn : Func} {fi : FuncInst Nat} {ps rs : Validation.Ty (.list .val)}
    (hvc : (K.methodFnSpec B R c n).vc fn) (hc : fi.code = .wasm fn)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : (K.args c).length = ps.length)
    (hrs : rs.length = n) (hfi : ∀ s b, R s b → s.funcs[K.addr c]? = some fi) :
    K.MethodOK B R c := by
  intro b s s' f' res hR hok hs
  have hv := Silmaril.Wasm.Verify.FnSpec.sound (P := K.P) (host := K.host) (a := K.addr c) hvc hc
    he (fun _ => hps) hrs b
  obtain ⟨res', he', hpost⟩ :=
    Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals hv ⟨hfi s b hR, rfl, hR⟩ hs
  cases he'
  exact hpost hok

end Silmaril.Sim.Wasm.ExportSim

end
