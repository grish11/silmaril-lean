module

public import Silmaril.Wasm.Component.Reference.LinkedSessionFwd.Thms
import Silmaril.Wasm.Component.Reference.LinkedSessionIR.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Linked
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Fixture

/-!
# Linked sessions, IR to specification: finite session adequacy

**Scope.** `Linked2` only: the import-free exporter A answering every import of the importer B
through the canonical ABI. Every profile `P` and component choice profile `prof`; the IR is
`l.toComp.den (impSem P)`, the reference component `l.toRef` on `core3P P` under
`linkHost impl`.

**Hypotheses.** `Linked2.Adequate l` only (exporter `Good` and `Inst`; importer `Good`, `Inst`,
`Arity` and `FloatFree`; `WireTy`, `NamesOk`, `WireNodup`, `SplitOk`). The read-back itself uses
the exporter's and the importer's `Good` and `WireTy`; the rest is what #705 and #712 need for
the reference side. No deterministic profile is assumed: the read-back is relational, every IR
play is read back, with whatever runs the profile allows. The calls are typed
(`SimpleI.TypedCalls`) and the outcome list has one outcome per call, as in
`Linked2.IRToSpec`.

* **IR to specification** (`Linked2.irToSpec : Linked2.IRToSpec P l`): every typed session play
  of `l.toComp.den (impSem P)` (`Linked2.sessMoves`, later calls continuing after traps) is the
  play of a `Linked2.SessSpec` session from the stores of the exporter's and the importer's
  instances. This discharges the named hypothesis of #712, which is no longer needed.
* **IR plays are specification sessions** (`Linked2.sessIR_iff`): with #705's
  `Linked2.sess_specToIR`, the session plays of typed calls are exactly the plays of
  specification sessions.
* **Finite session adequacy** (`Linked2.sess_complete`, `Linked2.sessAdequacy_full`): the
  reference session outcomes (`Linked2.sessObs`, `sessBehaviours` of `l.toRef`) of typed calls
  are exactly the reference images of the outcome lists whose session play is a play of
  `l.toComp.den (impSem P)`.
* **The fixture** `LinkedSession.linkedC`: its IR play `poke · trap · peek · 1` (#703's
  `linkedC_ir_session`) gives the reference session `poke, peek` with outcomes `trap, 1`
  (`linkedC_ref_session_of_ir`), and its finite session adequacy (`linkedC_sessAdequacy`).

**The read-back.** The plays of `l.toComp.den (impSem P)` are inverted layer by layer, with
general inversions of composition, handlers and pairing for rounds with lower calls
(`Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Games`: `serve_inv`, the converse
of `cplay_comp_serve`; `hc_inv`, `hb_inv`, the converses of `cplay_comp_ofHandler` and
`cplay_ofHandler_comp`; `cplay_of_pair_inr`). The linked environment is the importer's node
composed over the exporter's environment; its complete rounds are rounds of the importer whose
import calls, all together and in order, are complete rounds of the exporter (`serve_inv`).
The importer's side is read back through its node's wiring, its export handler, the import
mask, `splitH`, the `canon lower` wiring and `core3Sem` into rounds of its core instance whose
core import calls correspond to the component import calls (`ImpRel`; `imp_readback`). The
exporter's side is #676's read-back of the exporter's IR (`specRoundsT_of_chain`,
`sessRounds_of_specRoundsT`) through the exporter's node; its calls are typed (the lifted
arguments of B's `canon lower` at the import type, which `WireTy` makes the export type) and
wired, so the session is an `ExpRunT` with traps continuing. Splitting the instance's play
and the `ExpRunT` round by round gives the `SessSpec` session. The proof works with the plays
of `Strategy.comp` directly; it does not go through the H2 owner's `comp_threadS` (#706).

**Not claimed.**

* Divergence and host observations of linked sessions. They are the next step, through the
  divergence and infinite parts of #706's `comp_threadS` (`DivComp.comp`, `linkS`). They are
  not assumed vacuous: `SessCalls` records terminating outcomes only and `Comp.den` has finite
  plays; within `Linked2`, `l.toRef` has no host imports, while a parent passing host imports
  to B (as `linkedHRef`) lets B call the host.
* Ill-typed calls (`SimpleI.TypedCalls` fails): their IR plays answer a trap without running
  the importer and are not specification sessions; they are outside `Linked2.IRToSpec`.
* The parser from bytes to these components, and F6, are pending.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.{Games, Imp, Linked}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **IR session plays of a linked component are specification sessions** (proved, every
profile, under `Linked2.Adequate`): the hypothesis `Linked2.IRToSpec` of #712 holds. -/
theorem Linked2.irToSpec (P : Profile) (l : Linked2) (hl : l.Adequate) : Linked2.IRToSpec P l :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.linked2_irToSpec P l hl

/-- **The session plays of a linked component are exactly the specification sessions**
(proved, every profile, typed calls with one outcome per call). -/
theorem Linked2.sessIR_iff (P : Profile) (l : Linked2) (hl : l.Adequate)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) (calls : List (Fin l.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) (ht : SimpleI.TypedCalls l.imp calls)
    (hlen : calls.length = outs.length) :
    Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) ↔
      ∃ u' π' : Silmaril.Wasm.Execution.Core.Store Nat,
        Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' :=
  ⟨Linked2.irToSpec P l hl Ie Ii hIe hIi calls outs ht hlen,
    fun ⟨_, _, h⟩ => Linked2.sess_specToIR hl.expGood hl.impGood hIe hIi h⟩

/-- **IR session plays of a linked component are reference sessions** (proved, every profile and
component choice profile, typed calls). -/
theorem Linked2.sess_complete (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    (h : Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)) :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls :=
  Linked2.sess_complete_of P prof l hl (Linked2.irToSpec P l hl) impl h₀ calls outs ht hlen h

/-- **Finite session adequacy of a linked component** (proved, every profile and component
choice profile, under `Linked2.Adequate`): the reference session outcomes of typed calls are
exactly the reference images of the outcome lists whose session play, continuing after traps,
is a play of `l.toComp.den (impSem P)`. -/
theorem Linked2.sessAdequacy_full (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)} :=
  Linked2.sessAdequacy_of P prof l hl (Linked2.irToSpec P l hl) impl h₀ calls ht

namespace LinkedSession

/-- **The reference session `poke, peek` of `linkedC` from its IR play** (proved, every profile,
component choice profile and host functions): #703's IR play `poke · trap · peek · 1`
(`linkedC_ir_session`) read back by `Linked2.sess_complete`. -/
theorem linkedC_ref_session_of_ir (P : Profile) (prof : ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) :
    refOuts [none, some [.u32 1]] ∈
      Linked2.sessObs prof linkedC impl h₀ [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] :=
  Linked2.sess_complete P prof linkedC linkedC_adequate impl h₀ _ _
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linkedC_typed rfl
    (linkedC_ir_session P)

/-- **Finite session adequacy of `linkedC` for the session `poke, peek`** (proved, every
profile, component choice profile and host functions). -/
theorem linkedC_sessAdequacy (P : Profile) (prof : ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) :
    Linked2.sessObs prof linkedC impl h₀ [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] =
      {o | ∃ outs, o = refOuts outs ∧ 2 = outs.length ∧
        Linked2.sessMoves linkedC [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] outs ∈
          linkedC.toComp.den (impSem P)} :=
  Linked2.sessAdequacy_full P prof linkedC linkedC_adequate impl h₀ _
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linkedC_typed

end LinkedSession

end Silmaril.Wasm.Component.Reference
