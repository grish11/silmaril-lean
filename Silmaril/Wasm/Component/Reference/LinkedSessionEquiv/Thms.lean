module

public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionAdeq.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Witness

/-!
# The resumable-session equivalence of linked components: theorems

**Scope.** `Linked2` only: the import-free exporter A answering every import of the importer B
through the canonical ABI. Every profile `P` and component choice profile `prof` (no
determinism is assumed); the IR is `l.toComp.den (impSem P)`, the reference component `l.toRef`
on `core3P P`.

**Hypotheses.** `Linked2.Adequate` for both components (exporter `Good` and `Inst`; importer
`Good`, `Inst`, `Arity` and `FloatFree`; `WireTy`, `NamesOk`, `WireNodup`; `SplitOk`). The
shape and ill-typed-call theorems need only the importer's `Good`.

* **The shape of linked plays** (`Linked2.den_shape`): every play of the linked denotation is
  complete export rounds, possibly followed by one pending export question (as #669's
  `den_shape` for `Simple`).
* **Ill-typed calls** (`Linked2.den_filter_iff`, `Linked2.den_answers`): the linked export
  handler passes every question to the importer, whose own export handler answers an ill-typed
  question (`Linked2.typedQ` fails: an index out of range, a flat payload, values of the wrong
  types) by a trap at once, without import calls and without touching either store. So complete
  rounds are a play exactly when the ill-typed ones answer a trap and the typed ones alone are a
  play; a typed round answers a trap or values. Whether a question is ill-typed depends only on
  the importer's export types.
* **Finite linked session adequacy** (`Linked2.sessEquiv_iff`): `Linked2.RefSessEquiv P prof l l'`
  (on the reference machine: the same export types, and for every typed call sequence the same
  resumable-session outcomes under every host) holds exactly when the export types are the same
  and the IR plays at the untyped export interface are the same:
  `pubPlays (l.toComp.den (impSem P)) = pubPlays (l'.toComp.den (impSem P))`. All plays, not only
  typed ones: the ill-typed rounds move between components with the same export types. The proof
  is #676's for `Simple`, with #724's `Linked2.sess_complete` and #705's `Linked2.sess_sound`.
* **A witness** (`LinkedSession.linkedC_refSessEquiv_linkedR`): `linkedR` is `linkedC` with the
  exporter's component exports renamed (`put`, `got` for `set`, `get`), so its reference component
  differs (the exporter's exports and the parent's aliases of them); the IR ignores the names
  (`LinkedSession.den_linkedR`), and the two are session-equivalent. A witness differing in core
  code (the exporter's state in another global, or `set` writing the global twice) needs a
  simulation of the two exporters' Core runs over all sessions and is not given.

**Not claimed.**

* Divergence (`Comp.den` has finite plays and `SessCalls` terminating outcomes; the definitions
  of linked divergence are in `LinkedSessionDiv.Defs`, the comparison is open) and productive
  (infinite) linked executions, the next step through `mem_inf_linkS_iff_of_det` (#706).
* Host observations: within `Linked2`, `l.toRef` has no host imports and `linkHost impl` is never
  called; a parent passing host imports to B (as `linkedHRef`) lets B call the host, which is not
  covered.
* Contextual full abstraction (the observer is a host calling exports in sequence).
* The parser from bytes to these components, and F6, are pending.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.{Filter, Main, Witness}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **Every play of a linked denotation is complete export rounds, possibly followed by one
pending export question** (proved). -/
theorem Linked2.den_shape (P : Profile) (l : Linked2)
    {p : List (Move (sigN 0) (sigN l.toComp.exports.length))} (hp : p ∈ l.toComp.den (impSem P)) :
    (∃ L, p = exportRounds L) ∨ ∃ L q, p = exportRounds L ++ [.inr (.ask q)] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.linked2_den_shape P l hp

/-- **Ill-typed calls of a linked component** (proved): complete rounds are a play exactly when
every ill-typed one answers a trap and the typed ones alone are a play. -/
theorem Linked2.den_filter_iff (P : Profile) {l : Linked2} (hi : l.imp.Good)
    (L : List (Σ q : (sigN l.toComp.exports.length).Op, (sigN l.toComp.exports.length).Ar q)) :
    exportRounds L ∈ l.toComp.den (impSem P) ↔
      (∀ x ∈ L, l.typedQ (x.1.1.val, x.1.2) = none → x.2 = none) ∧
      exportRounds (L.filter fun x => (l.typedQ (x.1.1.val, x.1.2)).isSome) ∈
        l.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.linked2_den_filter_iff P hi L

/-- **A typed round of a linked play answers a trap or values** (proved). -/
theorem Linked2.den_answers (P : Profile) {l : Linked2} (hi : l.imp.Good)
    {L : List (Σ q : (sigN l.toComp.exports.length).Op, (sigN l.toComp.exports.length).Ar q)}
    (h : exportRounds L ∈ l.toComp.den (impSem P)) :
    ∀ x ∈ L, (l.typedQ (x.1.1.val, x.1.2)).isSome = true →
      x.2 = none ∨ ∃ ws, x.2 = some (.vals ws) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.linked2_den_answers P hi h

/-- **Finite session adequacy of linked components, as an injection** (proved, every profile and
component choice profile): the resumable-session equivalence on the reference machine holds
exactly when the export types and the IR plays at the untyped export interface are the same.
Terminating outcomes and finite plays only; not contextual full abstraction. -/
theorem Linked2.sessEquiv_iff (P : Profile) (prof : ProfileKind) {l l' : Linked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquiv P prof l l' ↔ Linked2.SameTypes l l' ∧
      pubPlays (l.toComp.den (impSem P)) = pubPlays (l'.toComp.den (impSem P)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.linked2_sessEquiv_iff P prof hl hl'

namespace LinkedSession

/-- **`linkedR` satisfies the adequacy hypotheses** (proved). -/
theorem linkedR_adequate : linkedR.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.linkedR_adequate

/-- **Renaming the exporter's exports leaves the IR unchanged** (proved). -/
theorem den_linkedR (P : Profile) :
    linkedR.toComp.den (impSem P) = linkedC.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.den_linkedR P

/-- **`linkedC` and `linkedR` are session-equivalent on the reference machine** (proved, every
profile and component choice profile), by `Linked2.sessEquiv_iff` from `den_linkedR`. -/
theorem linkedC_refSessEquiv_linkedR (P : Profile) (prof : ProfileKind) :
    Linked2.RefSessEquiv P prof linkedC linkedR :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.linkedC_refSessEquiv P prof

end LinkedSession

end Silmaril.Wasm.Component.Reference
