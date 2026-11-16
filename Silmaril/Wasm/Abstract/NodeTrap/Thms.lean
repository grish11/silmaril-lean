module

public import Silmaril.Wasm.Abstract.NodeTrap.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Games.Abstract.SessionTrap.Thms
public import Silmaril.Wasm.Component.DWiringMulti.Thms
public import Silmaril.Wasm.Component.OutOfRange.Thms
import Silmaril.Proofs.Wasm.Abstract.NodeTrap.Node

/-!
# Core 3.0 instance rounds abort on an import trap: theorems

Core Wasm traps the caller of a trapping callee: an import call answered by `Answer.trap`
resumes the instance thread with `TRAP` in the callout context (`resumeResult`), and from such a
trapped configuration every host-free step keeps the store, stays trapped and shrinks the code
(`Silmaril.Wasm.Game.trapped_step`, `trapped_step_lt`). A trapped configuration is at no callout
and finishes only with a trap. So, for every profile `P` and with no typing hypothesis:

* **The instance triple** (`instTripleS_trapAbortsRound`): `TrapAbortsRound IsTrapA
  (instTripleS I P)`. In every finished activation whose import log contains a trapped call, that
  call is the last one and the activation returns the trap `.ret (.inr ()) s'` (never `.div`: a
  trapped thread terminates); no pending call and no productive stream follows a trapped call.
* **The session** (`instSession_trapAbortsBelow`): in every play of `instSession I P s`, a trap
  answer from below is followed, if at all, by the trap answer `.inr ()`
  (`SessionTrap.threadS_trapAbortsBelow`).
* **The nodes** (`trapPropagating_core3SemD`): every core node of the divergence-observing Core
  3.0 component semantics propagates traps on `sigU`:
  `TrapPropagating (Node.denD (core3SemD P) e (.core m args))`. The node is the instance strategy
  between one-shot handlers (`implsN`, `importH` below; `exportH`, `widenH` above); `importH` reads
  the IR trap `none` as `Answer.trap`, and the others keep `none`.

* **The module above `implsN`** (`trapPropagating_sem_widenH`): the module's strategy seen
  through `widenH` propagates traps too. Below it, `implsN e args` is trap-silent when every
  wiring program in `args` calls the environment (`trapSilent_implsN`: an argument that does not
  lift, a call out of range or a missing program answers `none`). So such a core node has no
  silent chatter: it diverges exactly where its module does (`div_dcoreNode_core3SemD`).

Hence, for a component whose first node is a Core 3.0 core node, the divergences of
`Comp.denD (core3SemD P)` have no chatter between `maskH` and the first node
(`div_denD_core3SemD`, from `div_denD_multi`), and a core node seen at interface sizes diverges
only where it diverges itself (`div_atSizes_core3SemD`, from `div_atSizes_of_trapPropagating`).

## What is not claimed

* Nested component nodes `.inst c args`: their trap propagation is a property of the nested
  component's wiring (`maskH`, `exportsH`, the nodes), not of Core; `div_denD_multi_of_forall`
  needs it for every node. Only the first node matters for `div_denD_multi`.
* The relation of `semOfSD`'s `importH`/`exportH` coercions to `ExtSession`'s `toU`/`ofU` (a
  `core3SemD` node as an `ext`-session on `sigS`).

Proofs in `Silmaril.Proofs.Wasm.Abstract.NodeTrap`.
-/

public section

namespace Silmaril.Wasm.Abstract.NodeTrap

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.SessionTrap
open Silmaril.Wasm.Game Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

section Instance

variable {I : ScalarInstance} {P : Profile}

/-- **Every round of a Core 3.0 instance aborts at an import trap.** -/
theorem instTripleS_trapAbortsRound : TrapAbortsRound IsTrapA (instTripleS I P) :=
  Silmaril.Proofs.Wasm.Abstract.NodeTrap.instTripleS_trapAbortsRound

/-- **After an import trap, the instance session answers the trap `.inr ()`**, if it moves at
all. -/
theorem instSession_trapAbortsBelow (s : Store Nat) :
    TrapAbortsBelow IsTrapA (instSession I P s) :=
  threadS_trapAbortsBelow instTripleS_trapAbortsRound s

/-- After an import trap, the instance session makes no further import call in that round. -/
theorem instSession_trapEndsBelow (s : Store Nat) : TrapEndsBelow IsTrapA (instSession I P s) :=
  (instSession_trapAbortsBelow s).trapEndsBelow

end Instance

/-- **A Core 3.0 core node propagates traps.** -/
theorem trapPropagating_core3SemD (P : Profile) (e : Nat) (m : NumInstance) (args : List Impl) :
    TrapPropagating (Node.denD (core3SemD P) e (.core m args)) :=
  Silmaril.Proofs.Wasm.Abstract.NodeTrap.trapPropagating_core3SemD P e m args

/-- **The module of a Core 3.0 core node, seen through `widenH`, propagates traps**: the layer
of the node above `implsN`. -/
theorem trapPropagating_sem_widenH (P : Profile) (m : NumInstance) :
    TrapPropagating
      (((core3SemD P).sem m).comp (DStrategy.ofHandler (widenH m.exports.length))) :=
  Silmaril.Proofs.Wasm.Abstract.NodeTrap.trapPropagating_sem_widenH P m

/-- **`implsN` is trap-silent when every wiring program calls the environment** (as `canon
lower` of a component import does): it answers without a call only with the trap `none`. -/
theorem trapSilent_implsN (e : Nat) (args : List Impl) (t : Nat)
    (hargs : ∀ im ∈ args, ∃ r, im.target = .call r) : TrapSilent (implsN e args t) :=
  Silmaril.Proofs.Wasm.Abstract.NodeTrap.trapSilent_implsN e args t hargs

/-- **No silent chatter from `implsN` at a Core 3.0 core node** whose wiring programs all call
the environment: the node diverges exactly where its module does, through `implsN` below and
`widenH` above. -/
theorem div_dcoreNode_core3SemD (P : Profile) (e : Nat) (m : NumInstance) (args : List Impl)
    (hargs : ∀ im ∈ args, ∃ r, im.target = .call r) :
    (Node.denD (core3SemD P) e (.core m args)).div = {p | ∃ u v, Zip u v p ∧
      u ∈ Strategy.ofHandler (implsN e args m.imports.length) ∧ ∃ a b, Zip a b v ∧
        a ∈ ((core3SemD P).sem m).div ∧ b ∈ Strategy.ofHandler (widenH m.exports.length)} := by
  rw [Node.denD, div_dcoreNode]
  ext p
  exact or_iff_left ((trapPropagating_sem_widenH P m).not_silentChatter
    (trapSilent_implsN e args _ hargs))

/-- **No chatter at `maskH` below a Core 3.0 core node**: the environment after it has only the
node's own divergences. -/
theorem obs_ext_maskH_core3SemD (P : Profile) (e : Nat) (m : NumInstance) (args : List Impl) :
    DObs.of (DStrategy.ext e (DStrategy.ofHandler (maskH e))
      (Node.denD (core3SemD P) e (.core m args))) =
      firstObs e (Node.denD (core3SemD P) e (.core m args)) :=
  obs_ext_maskH e (trapPropagating_core3SemD P e m args)

/-- **Divergence of a component over Core 3.0 instances whose first node is a core node**: the
node's own divergences and the chatter of later nodes with the environment so far, routed
through the wiring (`div_denD_multi`). -/
theorem div_denD_core3SemD (P : Profile) (J : Iface) (m : NumInstance) (args : List Impl)
    (ns : List (Node NumInstance)) (xs : List Silmaril.Wasm.Component.Export) :
    ((Comp.mk J (.core m args :: ns) xs).denD (core3SemD P)).div =
      {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
        u ∈ Strategy.ofHandler (widenH J.length) ∧
          t ∈ Strategy.ofHandler (narrowH xs.length) ∧ ∃ d x, Zip d x v ∧
            d ∈ (nodesObs (core3SemD P) (J.length + (Node.core m args).width) ns
              (firstObs J.length (Node.denD (core3SemD P) J.length (.core m args)))).div ∧
            x ∈ Strategy.ofHandler (exportsH (envAfter J.length (.core m args :: ns)) xs)} :=
  div_denD_multi _ J _ ns xs (trapPropagating_core3SemD P _ m args)

/-- **A Core 3.0 core node at interface sizes diverges only where it diverges itself.** -/
theorem div_atSizes_core3SemD {n k : Nat} (P : Profile) (e : Nat) (m : NumInstance)
    (args : List Impl) :
    (DStrategy.atSizes n k (Node.denD (core3SemD P) e (.core m args))).div =
      {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
        u ∈ Strategy.ofHandler (widenH n) ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
          v ∈ (Node.denD (core3SemD P) e (.core m args)).div} :=
  DStrategy.div_atSizes_of_trapPropagating (trapPropagating_core3SemD P e m args)

end Silmaril.Wasm.Abstract.NodeTrap
