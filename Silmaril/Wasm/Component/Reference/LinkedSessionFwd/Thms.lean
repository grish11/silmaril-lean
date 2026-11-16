module

public import Silmaril.Wasm.Component.Reference.LinkedSessionFwd.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Sess

/-!
# Linked sessions, specification to reference: theorems

**Scope.** `Linked2` only: the import-free exporter A answering every import of the importer B,
under `Linked2.Adequate` (exporter `Good` and `Inst`; importer `Good`, `Inst`, `Arity` and
`FloatFree`; `WireTy`, `NamesOk`, `WireNodup`, `SplitOk`). Every profile `P` and component choice
profile `prof`; the reference component is `l.toRef` on `core3P P` under `linkHost impl`.

This is the converse of #705's `Linked2.sess_refToSpec`:

* **Specification to reference** (`Linked2.sess_specToRef`): for the instances `Ie`, `Ii` of the
  two core modules, the reference images of the outcomes of every `Linked2.SessSpec` session
  from their stores are a resumable-session outcome list of `l.toRef` (`Linked2.sessObs`).
  Typing of the calls is not needed: `SessRound.Ok` checks the arguments.
* **Equality** (`Linked2.sessObs_eq`): with `Linked2.sess_refToSpec` and the uniqueness of core
  instances, the reference session outcomes of typed calls are exactly the reference images of
  the outcomes of specification sessions.
* **Finite session adequacy, the available direction** (`Linked2.sessAdequacy`): every
  specification session is a reference session and an IR play of `l.toComp.den (impSem P)`
  (`Linked2.sess_specToIR`). The converse, IR plays to specification sessions, waits on the H2
  owner's `comp_threadS`; it is the named hypothesis `Linked2.IRToSpec` (a `def`, not an axiom)
  of `Linked2.sess_complete_of` and `Linked2.sessAdequacy_of` (reference session outcomes =
  outcomes of IR session plays).
* **The fixture** `LinkedSession.linkedC`: its reference session `poke, peek` with outcomes
  `trap, 1` at `core3P P`, under any host functions, from the specification session
  `linkedC_spec_session` (`linkedC_ref_session_of_spec`).

**The forward runs.** A specification round is followed on the reference machine
(`Proofs.….LinkedSessionFwd`): the host's invocation and the deterministic prefix of the
importer's top-level call (`call_atLKTS`); the importer's core activation simulated step by step
from its part's runs (`LInv.reach_fwd`, by the forward link simulation `reach_link_fwd`, the
host code of the shared store unmapped along the trampolines, `internalP_unmapH`); at each import
call the nested `canon lower` and the exporter's `canon lift` (`nest_atTS`), the exporter's core
activation simulated from its specification run (`exp_fwd`, the relation re-established at the
exporter's own end store) and the return into the importer (`LInv.resume_fwd`); and the end: a
return, a trap of the importer, or a trap inside the nested call (the exporter's core trap, its
results not lifting, the callout's arguments not lifting; `LInv.expTrap_fwd`, `nest_trapCore`,
`nest_trapLift`, `nest_trapArgs`), after which the importer's round ends in the trap at the store
of the callout (`path_doomed`). `Calls` accepts a trap only without `internal` faults, so the
trapping runs of #705 (`TrapStore`) are restated with specification traps (`TrapsQS`,
`TrapsAtS`). The single call is `linkCall_fwd`, the session `sessL_fwd`.

**Not claimed.**

* The IR to specification direction (`Linked2.IRToSpec`), pending the H2 owner's `comp_threadS`.
* Divergence and host observations of linked sessions: a later step, not assumed vacuous.
  `SessCalls` records terminating outcomes only and `Comp.den` has finite plays; within `Linked2`
  `l.toRef` has no host imports, while a parent passing host imports to B (as `linkedHRef`) lets B
  call the host.
* The parser from bytes to these components, and F6, are pending.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.{Core, Nested, TrapS, Machine,
Round, Call, Sess}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **Specification sessions of a linked component are reference sessions** (proved, every
profile and component choice profile): the reference images of the outcomes of every
`Linked2.SessSpec` session from the stores of the exporter's and the importer's instances are a
resumable-session outcome list of `l.toRef`, under `linkHost impl` from any host state. -/
theorem Linked2.sess_specToRef (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List IVal)}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {outs : List (Option (List IVal))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.linked2_sess_specToRef P prof l hl
    impl h₀ hIe hIi h

/-- **Reference session outcomes are specification session outcomes** (proved, every profile and
component choice profile, typed calls). -/
theorem Linked2.sessObs_eq (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' π' : Silmaril.Wasm.Execution.Core.Store Nat),
        Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' ∧ o = refOuts outs} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.linked2_sessObs_eq P prof l hl impl
    h₀ calls ht hIe hIi

/-- **Finite session adequacy of a linked component, in the direction available** (proved):
every specification session from the instances' stores is a reference session behaviour of
`l.toRef` and its session play, continuing after traps, is a play of `l.toComp.den (impSem P)`.
The converse is `Linked2.sessAdequacy_of`, under `Linked2.IRToSpec`. -/
theorem Linked2.sessAdequacy (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List IVal)}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {outs : List (Option (List IVal))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls ∧
      Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.linked2_sessAdequacy P prof l hl impl
    h₀ hIe hIi h

/-- **IR session plays are reference sessions, given `Linked2.IRToSpec`** (proved from the named
hypothesis). -/
theorem Linked2.sess_complete_of (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) (hir : Linked2.IRToSpec P l) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    (h : Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)) :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.linked2_sess_complete_of P prof l hl
    hir impl h₀ calls outs ht hlen h

/-- **Finite session adequacy of a linked component, given `Linked2.IRToSpec`** (proved from the
named hypothesis): the reference session outcomes of typed calls are exactly the reference
images of the outcomes whose session play, continuing after traps, is a play of
`l.toComp.den (impSem P)`. -/
theorem Linked2.sessAdequacy_of (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) (hir : Linked2.IRToSpec P l) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.linked2_sessObs_eq_ir_of P prof l hl
    hir impl h₀ calls ht

namespace LinkedSession

/-- **The reference session `poke, peek` of `linkedC` answers `trap, 1`** (proved, every profile,
component choice profile and host functions), derived from the specification session
`linkedC_spec_session` by `Linked2.sess_specToRef`. As reference values the outcomes are
`[none, some [toRefVal (.u32 1)]]` (`linkedC_spec_outs`), #697's `linkedC_session`. -/
theorem linkedC_ref_session_of_spec (P : Profile) (prof : ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) :
    refOuts [none, some [.u32 1]] ∈
      Linked2.sessObs prof linkedC impl h₀ [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] := by
  obtain ⟨Ie, Ii, u', π', hIe, hIi, h⟩ := linkedC_spec_session P
  exact Linked2.sess_specToRef P prof linkedC linkedC_adequate impl h₀ hIe hIi h

end LinkedSession

end Silmaril.Wasm.Component.Reference
