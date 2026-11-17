module

public import Silmaril.Wasm.Component.Reference.LinkedGSession.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.Plays

/-!
# Ill-typed calls of linked components with an abstract exporter, and their finite plays

**Scope.** `g : LinkedG`, an abstract exporter `g.exp : ExpSpec` answering every import of the
importer `g.imp : SimpleI` through the canonical ABI; so also one more importer on a chain
(`⟨n.spec Ib Is, b, w⟩`). Every profile `P`; the IR is `g.toComp.den (impSem P)`. A question
`q : Nat × Payload` is typed when `(g.toExp Ii).TypedQ q` (`ExpSpec.TypedQ`, the predicate of
`LinkedGSession`'s session triple: an export in range, on values of its parameter types). It
reads only `g.toComp` (the exports of `g.imp`), so the instance `Ii` in the statements below is
arbitrary unless a hypothesis fixes it. Filtering by it uses classical decidability.

**Proved (public, below).**

1. **The shape of linked plays** (`LinkedG.den_shape`): every play of `g.toComp.den` is complete
   export rounds, possibly followed by one pending export question.
2. **Ill-typed calls** (`LinkedG.den_filter_iff`, `LinkedG.den_answers`), the `LinkedG` analogue
   of #726's `Linked2.den_filter_iff` and `Linked2.den_answers`, under the importer's `Good`
   only (nothing about the exporter): complete rounds are a play exactly when every ill-typed
   one answers a trap and the typed ones alone are a play; a typed round answers a trap or
   values. The linked export handler forwards every question to the importer's node, whose own
   export handler answers an ill-typed question by a trap at once, without import calls
   (`LinkedSessionEquiv.nodeI_inv`, `nodeI_of`, now stated for any importer node and shared with
   `Linked2`); the exporter appears only through its environment of lower calls.
3. **Finite agreement with the session object** (`LinkedG.pubPlays_compSession`, every profile),
   the analogue of #746's `Linked2.pubPlays_compSession`: for `g.exp.Adeq P`, `g.imp.Good`, `Ii`
   an instance of the importer's core module and `WireTy`, the plays of `g.toComp.den (impSem P)`
   at `sigU` are exactly the plays of `LinkedG.compSession P g` whose questions are in range,
   read at `sigU` (`sessMove`). Ill-typed rounds go through item 2 (they trap at once, the state
   unchanged, on both sides); typed rounds through `LinkedG.toExp_adeq`'s `fwd` and `bwd`.
   So equal session objects give the same IR plays (`LinkedG.compSession_eq_pubPlays`), and at
   `profile o`, for links meeting `ProfOk`, so does the full resumable-session equivalence
   (`LinkedG.pubPlays_of_refSessEquivFull`, through `LinkedG.compSession_inj_full`).

**Not claimed.**

* The converse of `LinkedG.pubPlays_of_refSessEquivFull` (the finite IR plays do not see
  divergence).
* Divergence and infinite plays of `g.toComp.denUD` outside typed calls (the ill-typed calls of
  `denUD`), so no equality of `LinkedG.compSession` with a whole IR `DStrategy`.
* The reference machine on ill-typed calls (`RefSessEquivFull` compares typed calls only).
* Nondeterministic profiles for the injection (`LinkedG.compSession_inj_full` is at
  `profile o`); host observations of parents passing host imports to the importer; the parser
  from bytes; F6.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.{Filter, Plays}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

namespace LinkedG

/-- **Every play of a linked denotation is complete export rounds, possibly followed by one
pending export question** (proved). -/
theorem den_shape (P : Profile) (g : LinkedG)
    {p : List (Move (sigN 0) (sigN g.toComp.exports.length))} (hp : p ∈ g.toComp.den (impSem P)) :
    (∃ L, p = exportRounds L) ∨ ∃ L q, p = exportRounds L ++ [.inr (.ask q)] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.linkedG_den_shape P g hp

open Classical in
/-- **Ill-typed calls of a linked component** (proved, importer `Good` only): complete rounds are
a play exactly when every ill-typed one answers a trap and the typed ones alone are a play. -/
theorem den_filter_iff (P : Profile) {g : LinkedG} (hi : g.imp.Good) (Ii : ScalarInstance)
    (L : List (Σ q : (sigN g.toComp.exports.length).Op, (sigN g.toComp.exports.length).Ar q)) :
    exportRounds L ∈ g.toComp.den (impSem P) ↔
      (∀ x ∈ L, ¬ (g.toExp Ii).TypedQ (x.1.1.val, x.1.2) → x.2 = none) ∧
      exportRounds (L.filter fun x => decide ((g.toExp Ii).TypedQ (x.1.1.val, x.1.2))) ∈
        g.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.linkedG_den_filter_iff P hi Ii L

/-- **A typed round of a linked play answers a trap or values** (proved, importer `Good`
only). -/
theorem den_answers (P : Profile) {g : LinkedG} (hi : g.imp.Good) (Ii : ScalarInstance)
    {L : List (Σ q : (sigN g.toComp.exports.length).Op, (sigN g.toComp.exports.length).Ar q)}
    (h : exportRounds L ∈ g.toComp.den (impSem P)) :
    ∀ x ∈ L, (g.toExp Ii).TypedQ (x.1.1.val, x.1.2) →
      x.2 = none ∨ ∃ ws, x.2 = some (.vals ws) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.linkedG_den_answers P hi Ii h

/-- **The IR plays are the in-range plays of the session object** (proved, every profile). -/
theorem pubPlays_compSession (P : Profile) {g : LinkedG} {Ii : ScalarInstance}
    (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy) :
    pubPlays (g.toComp.den (impSem P)) =
      {q | ∃ p ∈ (LinkedG.compSession P g).toStrategy, AskedIn g.imp.exports.length p ∧
        p.map sessMove = q} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.linkedG_pubPlays_compSession P he hi
    hIi hw

/-- Linked components with the same export count and equal session objects have the same IR
plays (proved, every profile). -/
theorem compSession_eq_pubPlays {P : Profile} {g g' : LinkedG} {Ii Ii' : ScalarInstance}
    (he : g.exp.Adeq P) (hi : g.imp.Good) (hIi : g.imp.mod.IsInst Ii) (hw : g.WireTy)
    (he' : g'.exp.Adeq P) (hi' : g'.imp.Good) (hIi' : g'.imp.mod.IsInst Ii') (hw' : g'.WireTy)
    (len : g.imp.exports.length = g'.imp.exports.length)
    (h : LinkedG.compSession P g = LinkedG.compSession P g') :
    pubPlays (g.toComp.den (impSem P)) = pubPlays (g'.toComp.den (impSem P)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.linkedG_compSession_eq_pubPlays he hi
    hIi hw he' hi' hIi' hw' len h

/-- **The full resumable-session equivalence gives the same IR plays** (proved, `profile o`,
every component choice profile), through `LinkedG.compSession_inj_full`. The converse is not
claimed: the IR plays are finite and say nothing of divergence. -/
theorem pubPlays_of_refSessEquivFull {o : GrowOracle} {prof : ProfileKind} {g g' : LinkedG}
    (hg : g.ProfOk o) (hg' : g'.ProfOk o) (h : LinkedG.RefSessEquivFull (profile o) prof g g') :
    pubPlays (g.toComp.den (impSem (profile o))) = pubPlays (g'.toComp.den (impSem (profile o))) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGFilter.linkedG_pubPlays_of_refSessEquivFull hg
    hg' h

end LinkedG

end Silmaril.Wasm.Component.Reference
