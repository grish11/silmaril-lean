module

public import Silmaril.Sim.Wasm.Open.Defs
public import Silmaril.Sim.Wasm.Thms
public import Silmaril.Wasm.Logic.Open.Thms

/-!
# Proofs: per-method soundness for open modules

Names are in `Silmaril.Sim.Wasm.ExportSim`, exported by `Silmaril/Sim/Wasm/Open/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Wasm.ExportSim

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)
open Silmaril.Wasm.Logic.Open (OMod ModuleSat specHost)

variable {C L V H : Type} {K : ExportSim C L V H} {B : Machine C L V}
  {R : Store H → B.St → Prop} {c : C}

/-- **Per-method soundness for an open module** (imports are host stubs answered by the most
general environment meeting the import contracts `Γi`): the module meets its export contexts
`Γe`, and `Γe` holds the ghost-free method specification at the method's address. -/
theorem methodOK_of_moduleSat {M : OMod H} {bind : H → Nat}
    {Γi Γe : Silmaril.Wasm.Logic.Hoare.Ctx H} (hsat : ModuleSat K.P M bind Γi Γe)
    (hhost : K.host = specHost bind Γi) (hΓ : Γe (K.addr c) = some (K.methodSpecU B R c)) :
    K.MethodOK B R c := by
  apply methodOK_of_fspecValidU
  rw [hhost]
  exact fun n => hsat.2 n _ _ hΓ

/-- **Per-method soundness from a core verified once against accessor contracts.** The core
`M` is an open module whose imports (the accessors `$rget $rset $fget $fset $fset6`, as host
stubs) meet the contracts `Γi`; it meets the method specifications `Γe`. A representation (G
or M) supplies the accessors as the host relation `K.host`; if that relation is sound and live
for `Γi` (one small problem per accessor), every method is sound for that representation. -/
theorem methodOK_of_core {M : OMod H} {bind : H → Nat} {Γi Γe : Silmaril.Wasm.Logic.Hoare.Ctx H}
    (hm : ModuleSat K.P M bind Γi Γe)
    (hsound : ∀ h s args o, K.host h s args o → specHost bind Γi h s args o)
    (hlive : ∀ h s args (S : FSpec H), Γi (bind h) = some S → S.pre s args →
      ∃ o, K.host h s args o)
    (hΓ : Γe (K.addr c) = some (K.methodSpecU B R c)) : K.MethodOK B R c :=
  fun b _ _ _ res hR hok hs =>
    Silmaril.Wasm.Logic.Open.ModuleSat.invoke_vals hm hsound hlive hΓ ⟨rfl, b, hR⟩ hs res rfl hok b hR

end Silmaril.Sim.Wasm.ExportSim

end
