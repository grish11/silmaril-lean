module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Thms
public import Silmaril.Games.Abstract.StratLegal.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Triple
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Det
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Trap

/-!
# Session objects of linked components with host imports: theorems

**Scope.** `HLinked2` (`HLinkedSession.Defs`), every profile `P` and component choice profile
`prof`. The reference host is the logging host `answerHostS P (logG g)` of a typed deterministic
stateful answering function `g` (`HLinked2.HostTyped`), as in `HLinked2.RefSessEquivFull`
(`HLinkedSessionInf`). The session objects are those of `HLinkedSessionObj.Defs`.

**Hypotheses.** The realizability theorems hold for every typed host (`HostRun` only); the
reference composition needs `HLinked2.Adequate` and typed calls, as `HLinked2.sess_refToSpec`.

## Proved

* **Which host histories occur** (`HLinked2.realRun_of_hostRun`, `HLinked2.hostRun_scriptG`):
  the host calls answered by a typed host, from any state, form a `RealRun` from no refusals (a
  refusal keeps the host state, `HostAnswersS`, so a call refused since the last answered call is
  refused again; an import without typed results is never answered); conversely every `RealRun`
  from no refusals on IR arguments is answered by the scripted host `HLinked2.scriptG` of its
  answered calls, which is typed and whose states only grow. The inputs of the host are exactly
  its state, the host function and the reference images of the arguments
  (`map_toRefVal_inj` makes the images faithful).
* **The obstruction for the open object** (`HLinked2.not_hostRun_refuse_answer`,
  `HLinked2.not_realRun_refuse_answer`): no host refuses a call and then answers the same call
  with nothing answered in between, while both answers are legal moves of the open interface.
* **Reference sessions are realizable** (`HLinked2.sessObs_realizable`): every reference session
  observation under a typed host is a specification session whose host calls are a `RealRun`.
* **The triples** (`HLinked2.noPlainTrap_compTripleS`, `HLinked2.admissible_compTripleS`, and
  the same for the open triple): every trap keeps the state, and the triples are admissible
  (saturated) on the legal host interface `HLinked2.hostSig`, so the canonical play object
  `StratLegal.toDStratL` is injective on them.
* **Store determinism at `profile o`** (`HLinked2.storeDet_compTripleS`,
  `HLinked2.storeDet_compTripleO`): two `SessSpec` rounds from the same stores whose host calls
  agree on answers wherever they agree on calls make the same core and component import calls
  and end in the same outcome and stores (B's moves by `strategy_deterministic`, A's answers by
  `retAt_det`/`trapAt_det`); hence the triples are store-deterministic, the hypothesis of
  `StratSession.threadS_eq_iff` together with `NoPlainTrap`.
* **A refused host call ends the round in a trap** (`HLinked2.refuse_last`): the core import call
  is answered by a trap, the importer's thread resumes trapped, host-free steps keep it trapped
  (`trapped_step`), a trapped code has no callout and is a result only as a trap. So a refused
  host call is the last host call of its round and the outcome is a trap: hiding a forced refusal
  (`compFin`) loses no host call. A diverging round makes no refused host call
  (`HLinked2.roundDivC_no_refuse`: a trapped thread terminates and calls nothing), and every host
  call of host chatter is answered (`HLinked2.roundInfC_no_refuse`).

## Not claimed (what remains)

* **The injection.** `HLinked2.RefSessEquivFull (profile o) prof l l' ↔ ∃ h : SameTypes l l',
  compSession` equality after transport along `h.host` is the target and is **open**. Store
  determinism is proved; it still needs the bisimulation from scripted
  hosts (`scriptG` realizes every visible history; a probe answering one more call reveals each
  refused call), and the divergence, host-chatter and productive-stream clauses through
  `HLinked2.RefSessEquivFull.iff_spec`.
* **The open object** `compSessionO`: equality of open objects should imply `RefSessEquivFull`
  (soundness); it does not follow from it, since the open interface admits a refusal followed by
  an answer of the same call (`not_hostRun_refuse_answer`). The concrete pair of components
  separating them (an importer that answers differently when its previous call trapped in a host
  call it then repeats) is **not proved** here.
* Nondeterministic profiles; the relation to the generic `SessionLink.linkS` of the host calls,
  the exporter and the importer.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Component.Runtime (HostFuncId)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

namespace HLinked2

variable {l : HLinked2}

/-! ## Host-realizable histories -/

/-- **The host calls answered by a typed host are a realizable history** (proved, every host
state). -/
theorem realRun_of_hostRun {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) {s s' : σ} {c : List (Call (sigN l.host.length))}
    (h : HostRun g s c s') : ∃ R', RealRun l.host [] c R' :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.realRun_of_hostRun g hT h

/-- The host calls answered by a host are on IR arguments (proved). -/
theorem valsCalls_of_hostRun {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    {n : Nat} {s s' : σ} {c : List (Call (sigN n))} (h : HostRun g s c s') : ValsCalls c :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.valsCalls_of_hostRun g h

/-- **Every realizable history is answered by its scripted host** (proved): a `RealRun` from no
refusals on IR arguments is a `HostRun` of `scriptG` of its answered calls from `0`, and that host
is typed. -/
theorem hostRun_scriptG {R' : List (sigN l.host.length).Op} {c : List (Call (sigN l.host.length))}
    (hr : RealRun l.host [] c R') (hv : ValsCalls c) :
    l.HostTyped (scriptG (answered c)) ∧ HostRun (scriptG (answered c)) 0 c (answered c).length :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.hostRun_scriptG hr hv

/-- **No host refuses a call and then answers it** with nothing answered in between (proved). -/
theorem not_hostRun_refuse_answer {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) {n : Nat} {s s' : σ}
    {m : (sigN n).Op} {p : Payload} : ¬ HostRun g s [⟨m, none⟩, ⟨m, some p⟩] s' :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.not_hostRun_refuse_answer g

/-- **No realizable history refuses a call and then answers it** (proved). -/
theorem not_realRun_refuse_answer {h : Iface} {R R' : List (sigN h.length).Op}
    {m : (sigN h.length).Op} {p : Payload} : ¬ RealRun h R [⟨m, none⟩, ⟨m, some p⟩] R' :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.not_realRun_refuse_answer

/-- **Reference sessions are realizable** (proved, every profile and component choice profile,
`Adequate`, typed host, typed calls): every reference session observation is a specification
session whose host calls, answered by the logging host, are a realizable history. -/
theorem sessObs_realizable (P : Profile) (prof : ProfileKind) (hl : l.Adequate) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (hT : l.HostTyped g) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {o : List (Option (List RVal))} {st' : σ × List HostEvent}
    (ho : (o, st') ∈ sessObs P prof l g s₀ calls) :
    ∃ (Ie Ii : ScalarInstance) (outs : List (Option (List IVal)))
      (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload)))
      (u' π' : Silmaril.Wasm.Execution.Core.Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' ∧
      HostRun (logG g) (s₀, []) hs.flatten st' ∧ o = refOuts outs ∧
      ∃ R', RealRun l.host [] hs.flatten R' :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.sessObs_realizable P prof hl g hT s₀
    calls ht ho

/-! ## The triples -/

variable {P : Profile} {Ie Ii : ScalarInstance}

/-- **Every trap keeps the state** in the host-realizable triple (proved). -/
theorem noPlainTrap_compTripleS : StratSession.NoPlainTrap (compTripleS P l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.noPlainTrap_compTripleS

/-- **The host-realizable triple is admissible** on the legal host interface (proved). -/
theorem admissible_compTripleS : Admissible (compTripleS P l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.admissible_compTripleS

/-- **Every trap keeps the state** in the open triple (proved). -/
theorem noPlainTrap_compTripleO : StratSession.NoPlainTrap (compTripleO P l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.noPlainTrap_compTripleO

/-- **The open triple is admissible** on the legal host interface (proved). -/
theorem admissible_compTripleO : Admissible (compTripleO P l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.admissible_compTripleO

/-- **Store determinism** of the host-realizable triple (proved, `profile o`): one round, with its
host calls and their answers, is a function of the stores and the call; a round whose visible
host calls are `c` and one that hides a forced refusal after `c` cannot both exist. -/
theorem storeDet_compTripleS {o : GrowOracle} :
    StratThread.StoreDet (compTripleS (profile o) l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.storeDet_compTripleS

/-- **Store determinism** of the open triple (proved, `profile o`). -/
theorem storeDet_compTripleO {o : GrowOracle} :
    StratThread.StoreDet (compTripleO (profile o) l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.storeDet_compTripleO

/-- **A refused host call ends the round in a trap** (proved, every profile): in a one-round
`SessSpec`, a host call answered by a refusal is the last host call, and the outcome is a trap. -/
theorem refuse_last {u π u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {o : Option (List IVal)}
    {H : List (Call (sigN l.host.length))} (h : SessSpec P l Ie Ii u π [(j, vs)] [o] [H] u' π')
    {H₁ H₂ : List (Call (sigN l.host.length))} {m : (sigN l.host.length).Op}
    (hH : H = H₁ ++ ⟨m, none⟩ :: H₂) : H₂ = [] ∧ o = none :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.refuse_last h hH

/-- **A diverging round makes no refused host call** (proved, every profile): a refusal leaves
the importer trapped, and a trapped thread neither diverges host-free (`trapped_step_lt`) nor
calls an import. -/
theorem roundDivC_no_refuse {u π : Silmaril.Wasm.Execution.Core.Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {c : List (Call (sigN l.host.length))}
    (h : RoundDivC P l Ie Ii u π j vs c) {H₁ H₂ : List (Call (sigN l.host.length))}
    {m : (sigN l.host.length).Op} (hc : c = H₁ ++ ⟨m, none⟩ :: H₂) : False :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.roundDivC_no_refuse h hc

/-- **Every host call of host chatter is answered** (proved, every profile). -/
theorem roundInfC_no_refuse {u π : Silmaril.Wasm.Execution.Core.Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {ω : ℕ → Call (sigN l.host.length)}
    (h : RoundInfC P l Ie Ii u π j vs ω) (i : ℕ) : (ω i).2 ≠ none :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.roundInfC_no_refuse h i

end HLinked2

end Silmaril.Wasm.Component.Reference
