module

public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs
import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.Witness

/-!
# Resumable-session adequacy of the component IR: theorems

For simple components in the fragment `Simple.Adequate` (float-free, within the flat arities,
the module instantiated as the IR assumes, no imports), at every silmaril profile `P` and every
component choice profile `prof` (no determinism is assumed):

* **sessions of the specification and of the reference machine** (`Simple.sess_specToRef`,
  `Simple.sess_refToSpec`): the resumable reference sessions (`sessObs`) are exactly the
  sessions of the canonical-ABI specification (`SessSpec`), in which a trapped call
  (`TrapAt`) leaves the Core store it reached and the next call starts there;
* **sessions of the IR** (`Simple.sess_complete`, `Simple.sess_sound`): the IR play of a typed
  session (`sessMoves`, each call answered by its results or by a trap, later calls continuing
  after traps) is a play of `c.toComp.den (modSem P)` exactly when its outcomes are a
  reference session behaviour;
* **resumable-session adequacy** (`Simple.sessAdequacy`): `RefSessEquiv P prof c c'` holds
  exactly when `c` and `c'` have the same export types and the same IR plays at the untyped
  export interface (`pubPlays`): full equality of the finite IR strategies, not only of their
  trap-last plays (#669's `Simple.adequacy`). `RefSessEquiv` refines `RefPubEquiv`
  (`RefSessEquiv.refPubEquiv`);
* **the gap of #669 is closed** (`witness_session`, `witness_not_sessEquiv`,
  `refPubEquiv_not_refSessEquiv`): #669's witnesses `pokePeekS` and `zeroS` are `RefPubEquiv`,
  but the session `poke, peek` answers `trap, 1` for `pokePeekS` (the IR play
  `poke · trap · peek · 1`) and never for `zeroS`.

Modelling choice: the session resumes after a trap (`resumeCfg`), matching the Wasm session
reading of `Silmaril.Games.Abstract.StratSession` (a trap aborts the call, not the instance).
REF itself locks the store down after a trap (`Machine.trapCfg`); `RefSessEquiv` is defined
from reference-machine runs only.

Not claimed: divergence and infinite plays (`Comp.den` is finite plays, and a session records
terminating outcomes only; the infinite case is the game-level infinite closure, see
`StratSession.threadS`'s `inf` component), contextual full abstraction (the observer is a host
calling exports in sequence), and the correctness of the parser from bytes to `Comp`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.{CallTrap,RefSess,IRSess,Main,
Witness}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **Specification sessions are reference sessions** (proved). -/
theorem Simple.sess_specToRef (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (s : Silmaril.Wasm.Execution.Core.Store Nat) (ht : TypedCalls c calls)
    (h : SessSpec P c I I.store (specCalls c calls) outs s) :
    refOuts outs ∈ sessObs P prof c calls :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.sess_specToRef P prof c hc hI calls
    outs s ht h

/-- **Reference sessions are specification sessions** (proved). -/
theorem Simple.sess_refToSpec (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (ht : TypedCalls c calls)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ sessObs P prof c calls) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal)))
      (s : Silmaril.Wasm.Execution.Core.Store Nat),
      c.mod.IsInst I ∧ SessSpec P c I I.store (specCalls c calls) outs s ∧ o = refOuts outs :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.sess_refToSpec P prof c hc calls ht ho

/-- **Completeness for sessions** (proved): the IR play of a typed session, continuing after
traps, is a reference session behaviour. -/
theorem Simple.sess_complete (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : TypedCalls c calls) (hlen : calls.length = outs.length)
    (h : sessMoves c calls outs ∈ c.toComp.den (modSem P)) :
    refOuts outs ∈ sessObs P prof c calls :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.sess_complete P prof c hc calls outs
    ht hlen h

/-- **Soundness for sessions** (proved): every reference session behaviour of typed calls is
the IR play of the session. -/
theorem Simple.sess_sound (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (ht : TypedCalls c calls)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ sessObs P prof c calls) :
    ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
      sessMoves c calls outs ∈ c.toComp.den (modSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.sess_sound P prof c hc calls ht ho

/-- **Resumable-session adequacy of the component IR** (proved, every profile and component
choice profile): for adequate simple components, the resumable-session equivalence on the
reference machine holds exactly when the export types and the IR plays are the same.
Terminating outcomes and finite plays only; not contextual full abstraction. -/
theorem Simple.sessAdequacy (P : Profile) (prof : ProfileKind) {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) :
    RefSessEquiv P prof c c' ↔ SameTypes c c' ∧
      pubPlays (c.toComp.den (modSem P)) = pubPlays (c'.toComp.den (modSem P)) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.sessAdequacy P prof hc hc'

/-- **The session equivalence refines the public equivalence** of #669 (proved). -/
theorem RefSessEquiv.refPubEquiv {P : Profile} {prof : ProfileKind} {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) (h : RefSessEquiv P prof c c') :
    RefPubEquiv P prof c c' :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.refPubEquiv_of_sess hc hc' h

/-! ## The trap witnesses of #669 -/

/-- **The session `poke, peek` answers `trap, 1` for `pokePeekS` and never for `zeroS`**
(proved, every deterministic profile and component choice profile). -/
theorem witness_session (o : Silmaril.Wasm.SingleThreaded.GrowOracle) (prof : ProfileKind) :
    refOuts [none, some [.u32 1]] ∈ sessObs (Silmaril.Wasm.SingleThreaded.profile o) prof
        pokePeekS [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] ∧
      refOuts [none, some [.u32 1]] ∉ sessObs (Silmaril.Wasm.SingleThreaded.profile o) prof
        zeroS [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.witness_session o prof

/-- **The witnesses of #669 are not session-equivalent** (proved). -/
theorem witness_not_sessEquiv (o : Silmaril.Wasm.SingleThreaded.GrowOracle) (prof : ProfileKind) :
    ¬ RefSessEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS zeroS :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.witness_not_sessEquiv o prof

/-- **`RefPubEquiv` does not imply `RefSessEquiv`** (proved): the witnesses are publicly
equivalent on the reference machine, and a resumable session tells them apart. -/
theorem refPubEquiv_not_refSessEquiv (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (prof : ProfileKind) :
    RefPubEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS zeroS ∧
      ¬ RefSessEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS zeroS :=
  ⟨Silmaril.Proofs.Wasm.Component.Reference.Adequacy.witness_equiv o prof,
    witness_not_sessEquiv o prof⟩

end Silmaril.Wasm.Component.Reference
