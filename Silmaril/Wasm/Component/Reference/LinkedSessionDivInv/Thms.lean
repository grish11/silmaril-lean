module

public import Silmaril.Wasm.Component.Reference.LinkedSessionDivInv.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.Main

/-!
# Diverging calls of linked sessions, both directions: theorems

**Scope.** `Linked2` only: the import-free exporter A (`l.exp`) answering every import of the
importer B (`l.imp`), under `Linked2.Adequate`, for typed calls (`SimpleI.TypedCalls` and a
typed last call). Every profile `P`, component choice profile `prof`, host implementation
`impl` and host state `h₀`; the reference component is `l.toRef` on `core3P P` under
`linkHost impl`. No determinism is assumed.

* **Reference divergence is specification divergence** (`Linked2.divRefToSpec`, proved):
  `Linked2.DivRefToSpec P prof l`, i.e. `refDivs ⊆ sessDivs`, the converse of #730's
  `Linked2.divSpecToRef`;
* **The two agree** (`Linked2.sessDivs_eq_refDivs`): the diverging session calls of the
  specification are those of the reference machine, under every host;
* **The equivalence** (`Linked2.RefSessEquivD.iff_sessDivs`): the reference-defined
  `RefSessEquivD` (the same terminating outcomes and the same quiet divergences on the
  reference machine) is `RefSessEquiv` together with the same specification divergences
  (`sessDivs`), as #680's `RefSessEquivD.iff_refDivs` for `Simple`.

**How a divergent linked call is classified.** The session prefix is inverted call by call
(#705's `linkCallK`, `linkCallT`, a trapped call resuming from `resumeCfg`). In the diverging
call, the host's invocation and the lowering before B's core activation are a finite
deterministic run (`call_atLK`), so the machine diverges from B's core activation. From there,
with `LInv` relating the shared thread to B's part and A's store, one round is one of:

* **(a) B diverges host-free** (`DivB`): B's core activation runs forever, and its infinite core
  run is the image of an infinite host-free run of B's part, step for step (`link_inf_back`,
  the backward counterpart of #730's `link_inf`);
* **(b) A diverges inside an import call** (`DivA`): B runs to a callout whose arguments lift,
  and the nested activation of A's export runs forever, the image of an infinite run of A from
  its store;
* **(c) one served import call**: the nested call returns values that lift, B resumes, and the
  machine still diverges.

The other ends do not diverge: lift and lower code is finite and deterministic, a callout whose
arguments do not lift, a trap of A, results of A that do not lift, a Core trap of B and results
of B that do not lift all trap and lock down, B's results that lift resolve the call and return
control to the host, and A never calls out. By classical case analysis, either a finite chain of
served calls reaches a round of (a) or (b) (the chain is the round's prefix `DivRound.cs`), or
every round is (c), and dependent choice builds the infinite sequence of served calls of
**chatter** (`Chatter`). No case is missing: the reference machine does not diverge in a way the
specification does not capture.

**Not claimed.**

* Host observations: within `Linked2`, `l.toRef` has no host imports; a parent passing host
  imports to B (`linkedHRef`) is not covered.
* Productive (infinite) linked executions come next, through `mem_inf_linkS_iff_of_det` (#706).
* The parser from bytes to these components, and F6, are pending.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.{Back, Round, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **Reference divergence of a linked session is specification divergence** (proved, every
profile and component choice profile, under every host): for an adequate linked component and
typed calls, every diverging session call of the reference machine (`refDivs`) is one of the
specification (`sessDivs`: B diverges host-free, A diverges inside an import call, or B makes
infinitely many served import calls). -/
theorem Linked2.divRefToSpec (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate) :
    Linked2.DivRefToSpec P prof l :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.linked2_divRefToSpec P prof l hl

/-- **The diverging session calls of a linked component**: those of the specification are those
of the reference machine (proved), for typed calls, under every host. -/
theorem Linked2.sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) :
    Linked2.sessDivs P l calls j vs = Linked2.refDivs P prof l impl h₀ calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.linked2_sessDivs_eq_refDivs P prof
    l hl calls j vs ht hvs impl h₀

/-- **`RefSessEquivD` with the divergence clause on the specification** (proved): for adequate
linked components, the reference-defined equivalence with quiet divergence is `RefSessEquiv`
together with the same specification divergences. -/
theorem Linked2.RefSessEquivD.iff_sessDivs {P : Profile} {prof : ProfileKind} {l l' : Linked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivD P prof l l' ↔ ∃ h : Linked2.RefSessEquiv P prof l l',
      ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
        (vs : List IVal), SimpleI.TypedCalls l.imp calls →
        ValTy.checkList l.imp.exports[j].ty.params vs = true →
        Linked2.sessDivs P l calls j vs =
          Linked2.sessDivs P l' (Linked2.castCalls h.len calls) (Fin.cast h.len j) vs :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv.linked2_refSessEquivD_iff hl hl'

end Silmaril.Wasm.Component.Reference
