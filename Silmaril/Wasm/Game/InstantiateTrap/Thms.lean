module

public import Silmaril.Wasm.Execution.InstantiateTrap.Thms
public import Silmaril.Wasm.Game.SpecGlobals.Thms
import Silmaril.Proofs.Wasm.Game.InstantiateTrap

/-!
# The trap-aware instantiation against the specification's instantiation

For the trap-aware instantiations `instantiateT?` (globals allocated twice, as `$instantiate`)
and `instantiateOnceT?` (globals allocated once) of `Silmaril.Wasm.Execution.InstantiateTrap`:

* `instantiateT?_ne_fail_iff` (**completeness**): for a valid module, imports of the import types
  and a typed store, `instantiateT?` ends in a result or a segment trap exactly when an
  `Instantiate` derivation exists, at every profile and host. With `instantiateT?_trap_sound` and
  `instantiateT?_ok_sound` (`….Execution.InstantiateTrap.Thms`), every `Instantiate`
  configuration runs to `instantiateT?`'s outcome.
* `instantiateOnceT?_trap_spec`, `instantiateOnceT?_trap_outcome`: modules **with globals**: when
  single allocation traps in the store `s''`, the specification's instantiation (`prepare?` of the
  module itself, every global allocated twice) plays as the thread stopped at that trap in `s''`
  (`spec_trap_seg`, up to the global-address embedding of `Silmaril.Proofs.Wasm.Game.SpecGlobals`),
  and for validated modules its closed program fails exactly with `traps`
  (`spec_trap_outcome_valid`). For a module without globals no embedding is needed:
  `instantiateOnceT? = instantiateT?` (`instantiateOnceT?_of_nil`).
-/

@[expose] public section

namespace Silmaril.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- **Completeness**: `instantiateT?` does not fail exactly when the specification's
instantiation is defined. -/
theorem instantiateT?_ne_fail_iff {P : Profile} {host : HostSemantics Nat} {s : Store Nat}
    {m : Module} {xas : List ExternAddr} {xtI xtE : List CExternType}
    (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s) (hx : List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiateT? s m xas ≠ .fail ↔ ∃ c, Instantiate P host s m xas c :=
  Silmaril.Proofs.Wasm.Game.InstantiateTrap.instantiateT?_ne_fail_iff hm hs hx

/-- **A segment trap of single allocation is the specification's instantiation stopped at that
trap**, every profile, for a module whose active-segment offsets are constant instructions, in a
host-free typed store. -/
theorem instantiateOnceT?_trap_spec {s s'' : Store Nat} {m : Module} {xas : List ExternAddr}
    (hs : StoreOk s) (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (hm : (∀ e ∈ m.elems, ∀ y off, e.mode = .active y off → ∀ i ∈ off, i.IsConstI) ∧
      ∀ d ∈ m.data, ∀ y off, d.mode = .active y off → ∀ i ∈ off, i.IsConstI)
    (h : instantiateOnceT? s m xas = .trap s'') :
    ∃ (c : Config Nat) (st : Option FuncIdx) (f : Frame),
      prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile), ∃ (W : List Val) (R : List Admin),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s'' (configThread ⟨s'', f, vals W ++ .trap :: R⟩) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s'' (configThread ⟨s'', f, vals W ++ .trap :: R⟩) K := by
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, hT, -⟩ :=
    instantiateOnceT?_trap_steps (P := Profile.spec) (host := fun _ _ _ _ => False) h
  obtain ⟨c, hc, hI⟩ := spec_trap_seg hs hw hxb hm hg hp hT
  exact ⟨c, st, c₁.frame, hc, hI⟩

/-- **A segment trap of single allocation fails the specification's instantiation with
`traps`**, validated modules, every profile and environment. -/
theorem instantiateOnceT?_trap_outcome {s s'' : Store Nat} {m : Module} {mt : CModuleType}
    {xas : List ExternAddr} (hv : validate? m = some mt) (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (h : instantiateOnceT? s m xas = .trap s'') :
    ∃ (c : Config Nat) (st : Option FuncIdx), prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile) (K : Env I.E),
        ¬ (I.closedSpec P (c.withStart st) K).InstReady ∧
        ¬ (I.closedSpec P (c.withStart st) K).InstDiverges ∧
        ∀ b, (I.closedSpec P (c.withStart st) K).InstFails b ↔ b = .traps := by
  obtain ⟨s₁, f₁, vs, c₁, st, hg, hp, hT, -⟩ :=
    instantiateOnceT?_trap_steps (P := Profile.spec) (host := fun _ _ _ _ => False) h
  obtain ⟨c, hc, hI⟩ := spec_trap_outcome_valid hv hs hw hxb hg hp hT
  exact ⟨c, st, hc, hI⟩

end Silmaril.Wasm.Game

end
