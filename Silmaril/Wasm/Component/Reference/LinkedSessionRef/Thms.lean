module

public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Fixture

/-!
# The reference side of linked sessions: theorems

**Scope.** `Linked2` only: the import-free exporter A answering every import of the importer B.
The general linked composition, and with it linked adequacy for arbitrary component graphs,
waits on the composition closure of `DStrategy` (the H2 owner's part, asked on #207).

For every profile `P` and component choice profile `prof`, under `Linked2.Adequate` (the
hypotheses of `Linked2.sound`: exporter `Good` and `Inst`; importer `Good`, `Inst`, `Arity` and
`FloatFree`; `WireTy`, `NamesOk`, `WireNodup`, `SplitOk`):

* **Reference to specification** (`Linked2.sess_refToSpec`): every resumable-session outcome
  list of `l.toRef` for typed calls (`Linked2.sessObs`, i.e. `sessBehaviours`: a trapped call
  resumes from `resumeCfg`) is the reference image of the outcomes of a `Linked2.SessSpec`
  session from the instances' stores. B's store and A's store are threaded across the whole
  session: after A traps inside one of B's import calls (A's `TrapAt`, B's round answering
  `none`), after B traps by itself (a Core trap, or results the lift rejects), and after a
  callout whose arguments do not lift. This generalises `Linked2.sound` (single calls) and
  `Linked2.sound_seq` (resolved calls, then one last call) to sessions continuing after traps.
  The proof restates the trapping runs of a linked call with the core store of the trapped
  configuration (`TrapStore`, `Segs`), shows that the invariant between calls (`LReady`) holds
  at that store (`linkCallT`), and follows the session (`sessL_inv`).
* **Specification to IR** (`Linked2.sess_specToIR`): specification sessions are plays of
  `l.toComp.den (impSem P)` (`Linked2.sessMoves`), by #703's `Linked2.sessToIR`.
* **Reference to IR** (`Linked2.sess_sound`): every reference session behaviour of typed calls
  is an IR play, continuing after traps.
* **The fixture** `LinkedSession.linkedC` (#697, #703): it satisfies `Linked2.Adequate`
  (`linkedC_adequate`); its session `poke, peek` is a specification session with outcomes
  `trap, 1` (`linkedC_spec_session`); #703's IR play `poke · trap · peek · 1` follows from it
  through `Linked2.sess_specToIR` (`linkedC_ir_session_of_spec`, the same statement as
  `linkedC_ir_session`); and every reference session `poke, peek` of `linkedC.toRef` over
  `core3P P` is an IR play (`linkedC_sess_sound`).

**Consistency with #697's `linkedC_session`.** That theorem is a closed run over the executable
engine `core3 neverFail` with the embedder host `Host.ofEmbedder embCount`, with outcomes
`[none, some [1]]`. The theorems here are about `core3P P` under `linkHost impl`. `core3P P`
replaces `status` and `Internal` by the relational ones at `P`, so it is not definitionally
`core3 neverFail`, and `linkedC_session` is not an instance of `linkedC_sess_sound`. The outcome
lists agree: `refOuts [none, some [.u32 1]]`, the outcomes of `linkedC_spec_session`, is
`linkedC_session`'s `[none, some [toRefVal (.u32 1)]]`.

**Not claimed.**

* **Specification to reference** (`Linked2.sess_specToRef`, the converse of
  `Linked2.sess_refToSpec`). It needs forward runs of the linked reference machine: from a
  `SessSpec` round, a run of `l.toRef`'s top-level call through B's core code, each nested
  `canon lower`/`canon lift` call into A, and A's and B's traps, ending in the trapped or
  resolved configuration. #676 built these for `Simple` from #669's forward calls
  (`call_forward`, `CallAt`). For `Linked2` only the backward direction exists (`linkCallK`,
  `lsegs_inv`, `Linked2.sound`), so a forward linked call is still to be written.
* **IR to specification** (the converse of `Linked2.sess_specToIR`). It waits on the H2
  owner's `comp_threadS`, requested on #207 as
  `DivComp.comp (threadS tA sA) (threadS tB sB) = threadS (linkS tA tB) (sA, sB)`: the read-back
  of plays of `l.toComp.den (impSem P)` into importer rounds and an `ExpRunT` inverts the
  composition of the two threaded session strategies.
* **Divergence and host observations of linked sessions.** These are a later step and are not
  assumed vacuous. `SessCalls` records terminating outcomes only, and `Comp.den` has finite plays.
  Within `Linked2` every import of B is wired to A, so `l.toRef` has no host imports and
  `linkHost impl` is never called. In a parent that also passes host imports to B (as
  `linkedHRef`), B may call the host where `SimpleI` allows it.
* The parser from bytes to these components, and F6, are pending.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.{TrapStore, Segs, Call, IR,
Fixture}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **Reference sessions of a linked component are specification sessions** (proved, every
profile and component choice profile): every resumable-session outcome list of `l.toRef` for
typed calls, under `linkHost impl` from any host state, is the reference image of the outcomes
of a `Linked2.SessSpec` session from the stores of the exporter's and the importer's
instances. -/
theorem Linked2.sess_refToSpec (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls l.imp calls)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ Linked2.sessObs prof l impl h₀ calls) :
    ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal)))
      (u' π' : Silmaril.Wasm.Execution.Core.Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' ∧ o = refOuts outs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linked2_sess_refToSpec P prof l hl
    impl h₀ calls ht ho

/-- **Specification sessions of a linked component are IR plays** (proved, every profile). -/
theorem Linked2.sess_specToIR {P : Profile} {l : Linked2} (he : l.exp.Good) (hi : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linked2_sess_specToIR he hi hIe hIi h

/-- **Soundness of linked sessions** (proved, every profile and component choice profile):
every reference session behaviour of typed calls of `l.toRef` is the reference image of
outcomes whose session play, continuing after traps, is a play of `l.toComp.den (impSem P)`. -/
theorem Linked2.sess_sound (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ Linked2.sessObs prof l impl h₀ calls) :
    ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
      Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linked2_sess_sound P prof l hl impl
    h₀ calls ht ho

namespace LinkedSession

/-- **`linkedC` satisfies the adequacy hypotheses** (proved). -/
theorem linkedC_adequate : linkedC.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linkedC_adequate

/-- **The session `poke, peek` of `linkedC` in the specification** (proved, every profile):
`poke` answers a trap (A's `set` writes `g := 1` and traps inside B's import call; A's store
keeps the write), and `peek` then answers `1`. -/
theorem linkedC_spec_session (P : Profile) :
    ∃ (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (u' π' : Silmaril.Wasm.Execution.Core.Store Nat),
      linkedC.exp.mod.IsInst Ie ∧ linkedC.imp.mod.IsInst Ii ∧
      Linked2.SessSpec P linkedC Ie Ii Ii.store Ie.store
        [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] [none, some [.u32 1]] u' π' :=
  ⟨_, _, _, _, Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.sg_isInst,
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.pp_isInst,
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linkedC_sessSpec P⟩

/-- **#703's IR session of `linkedC` through the specification** (proved, every profile): the
statement of `linkedC_ir_session`, derived from `linkedC_spec_session` by
`Linked2.sess_specToIR`. -/
theorem linkedC_ir_session_of_spec (P : Profile) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) none),
      .inr (.ask (⟨1, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨1, by decide⟩, .vals [])) (some (.vals [.u32 1])))] :
      List (Silmaril.Games.Move linkedC.toComp.imports.sig
        (sigN linkedC.toComp.exports.length))) ∈
      linkedC.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linkedC_ir_session_of_spec P

/-- **The reference sessions `poke, peek` of `linkedC` are IR plays** (proved, every profile,
component choice profile and host functions): the instance of `Linked2.sess_sound`. -/
theorem linkedC_sess_sound (P : Profile) (prof : ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ Linked2.sessObs prof linkedC impl h₀ [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])]) :
    ∃ outs, o = refOuts outs ∧ 2 = outs.length ∧
      Linked2.sessMoves linkedC [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] outs ∈
        linkedC.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.linkedC_sess_sound P prof impl h₀ ho

/-- **The outcomes agree with #697's reference fixture**: the outcomes of
`linkedC_spec_session` are those of `linkedC_session` (proved). -/
theorem linkedC_spec_outs :
    refOuts [none, some [.u32 1]] = [none, some [toRefVal (.u32 1)]] := rfl

end LinkedSession

end Silmaril.Wasm.Component.Reference
