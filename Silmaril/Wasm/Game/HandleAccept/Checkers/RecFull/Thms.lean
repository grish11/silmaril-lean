module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.Sat
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.Total

/-!
# The full recursive-properness checker: what is proved

* `recFullCheck` validates and instantiates (`recFullCheck_instance`).
* **Hoare-logic specification** (`recFullCheck_sat`): in every environment `ρ` and every
  profile, the instance meets the cons reader specification `consISpec consIx ρ recProperL`
  with the store invariant `consInv`. The exported function calls itself; the proof (in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull`) gives the internal call the
  specification "if it returns normally, the argument denotes a recursively proper list" and
  proves it for arguments of every size by induction on the size, the recursive calls being on
  strictly smaller elements.
* **Termination** (`recFullCheck_tsat`): the same specification holds with **total
  correctness** (`TGameSat`) under the most general terminating environment of the cons reader
  specification, in every environment `ρ` and profile: every export call returns or traps, at
  every nesting depth. Every fixed `ρ` is well founded here (it maps handles to finite trees;
  correct `car`/`cdr` answers name subtrees): the spine loop has the variant "cons cells of the
  cursor's tree" and the recursion is by induction on the size bound. Consequently
  (`recFullCheck_dsound`, by `Silmaril.Wasm.Logic.GameLink.dstrategy_sound`) the
  divergence-observing strategy of the instance refines `dagStrat`: it diverges only after a
  play in which the environment broke the cons reader specification in `ρ` (or never answered).
* **Soundness**: under the trapping read policy and every accept policy but `ub`, in every set
  of environments and every profile, the checker accepts only recursively proper lists
  (`recFullCheck_sound`), at every nesting depth, unlike the depth-two `recProperCheck`.
* `(((1)))` (`deep1`) is recursively proper (`deep1_mem_recProperL'`) and rejected by every run
  of `recProperCheck` (`recProperCheck_rejects_deep1`); `Examples` shows `recFullCheck` accepts
  it.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle

theorem recFullCheck_instance : (Verify.instance? recFullCheck).isSome = true := by
  decide +kernel

theorem deep1_mem_recProperL' : deep1 ∈ recProperL := deep1_mem_recProperL

/-- **`recFullCheck` meets the cons reader specification of `recProperL`.** -/
theorem recFullCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P
    (Verify.instOf recFullCheck) (consInv recFullCheck) (consISpec consIx ρ recProperL)
    (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.recFullCheck_sat

/-- **`recFullCheck` terminates**: it meets the cons reader specification of `recProperL` with
total correctness. -/
theorem recFullCheck_tsat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.TGameSat P
    (Verify.instOf recFullCheck) (consInv recFullCheck) (consISpec consIx ρ recProperL)
    (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecFull.recFullCheck_tsat

/-- **No divergence against environments meeting the specification**: the
divergence-observing strategy of `recFullCheck` refines the divergence-aware assume/guarantee
strategy. -/
theorem recFullCheck_dsound (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    (Verify.instOf recFullCheck).dstrategy P (Verify.instOf recFullCheck).store ≤
      Silmaril.Wasm.Logic.OpenTotal.dagStrat (consISpec consIx ρ recProperL) (topISpec _) :=
  Silmaril.Wasm.Logic.GameLink.dstrategy_sound (recFullCheck_tsat P ρ) rfl

/-- **`recFullCheck` accepts only recursively proper lists**, at every depth. -/
theorem recFullCheck_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P recFullCheck consIx .trap oa Envs ⊆ recProperL :=
  consLang_sound_of_forall (fun ρ _ => recFullCheck_sat P ρ) rfl hoa

/-- **`recFullCheck` rejects `dottedElem`** in every environment and profile. -/
theorem recFullCheck_rejects_dottedElem (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    dottedElem ∉ moduleConsLang P recFullCheck consIx .trap oa Envs :=
  fun h => dottedElem_not_mem_recProperL (recFullCheck_sound P hoa Envs h)

/-- **`recProperCheck` rejects `(((1)))`**: it is nested three deep. -/
theorem recProperCheck_rejects_deep1 (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    deep1 ∉ moduleConsLang P recProperCheck consIx .trap oa Envs :=
  fun h => deep1_not_mem_nestL (recProperCheck_sound P hoa Envs h)

end Silmaril.Wasm.Game.HandleAccept.Checkers
