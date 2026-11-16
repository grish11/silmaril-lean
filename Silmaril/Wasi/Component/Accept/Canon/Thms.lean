module

public import Silmaril.Wasi.Component.Accept.Canon.Defs
public import Silmaril.Wasi.Component.Accept.Thms

/-! # Module and component acceptance through the canonical ABI: theorems

Under the correspondence `CanonLowerAccept`, the module's byte language through the core
import equals the component's through the WIT import.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games
open Silmaril.Wasm.Game.Accept (Callout)
open Silmaril.Wasm.Numerics (Profile)

/-- **Correspondence gives equal byte languages** (any callout set, for instance
`Silmaril.Wasm.Game.Accept.Callouts P UEnvOk 0 m`). -/
theorem accepted_eq_of_canonLowerAccept {I X : Set FnName} {callouts : Set Callout}
    {imp : String × String} {σ : Strategy (nsig I) (nsig X)} {f : FnName}
    (h : CanonLowerAccept callouts imp σ f) :
    {w | ∃ o ∈ callouts, o.imp = imp ∧ o.bytes32 = some w} = bytesLang σ f := by
  ext w
  change _ ↔ w ∈ importAccepted σ f (args1 bytes?)
  rw [mem_importAccepted_iff]
  constructor
  · rintro ⟨o, ho, hi, hw⟩; exact h.lower o ho hi w hw
  · rintro ⟨s, m, hs, args, he, hw⟩; exact h.lift s m hs args w he hw

/-- **A module and a component in canonical-ABI correspondence accept the same bytes.** -/
theorem bytesLang_eq_of_canonLowerAccept {P : Profile} {m : Silmaril.Wasm.Module}
    {imp : String × String} {I X : Set FnName} {σ : Strategy (nsig I) (nsig X)} {f : FnName}
    (h : CanonLowerAccept (Silmaril.Wasm.Game.Accept.Callouts P Silmaril.Wasm.Game.UEnvOk 0 m)
      imp σ f) :
    Silmaril.Wasm.Game.Accept.bytesLang P m imp = bytesLang σ f :=
  accepted_eq_of_canonLowerAccept h

end Silmaril.Wasi.Accept
