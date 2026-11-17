module

public import Silmaril.Wasm.Execution.InstantiateTrap.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
public import Silmaril.Wasm.Game.SpecGlobals.Thms

/-!
# Proofs: completeness of the trap-aware instantiation

`instantiateT?_ne_fail_iff`: for a valid module, imports of the import types and a typed store,
`instantiateT?` ends in a result or a trap exactly when an `Instantiate` derivation exists
(`exists_instantiate_iff_prepare?_isSome`, `Game.prepare_segments_not_fail`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.InstantiateTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

theorem instantiateT?_ne_fail_iff {P : Profile} {host : HostSemantics Nat} {s : Store Nat}
    {m : Module} {xas : List ExternAddr} {xtI xtE : List CExternType}
    (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s) (hx : List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateT? s m xas ≠ .fail ↔ ∃ c, Instantiate P host s m xas c := by
  have hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI :=
    ⟨xtE, xtI, hm, hx⟩
  constructor
  · intro hne
    cases h : instantiateT? s m xas with
    | ok s' f st =>
      obtain ⟨c, -, -, hI, -⟩ := instantiateT?_ok_sound (P := P) (host := host) hvalid h
      exact ⟨_, hI⟩
    | trap s' =>
      obtain ⟨c, st, -, -, hI, -⟩ := instantiateT?_trap_sound (P := P) (host := host) hvalid h
      exact ⟨_, hI⟩
    | fail => exact absurd h hne
  · intro hI hf
    have hp := (exists_instantiate_iff_prepare?_isSome hvalid).1 hI
    rcases instantiateT?_eq_fail_iff.1 hf with hn | ⟨c, st, hp', hseg⟩
    · rw [hn] at hp; cases hp
    · exact Game.prepare_segments_not_fail hm hs hx hp' hseg

end Silmaril.Proofs.Wasm.Game.InstantiateTrap

end
