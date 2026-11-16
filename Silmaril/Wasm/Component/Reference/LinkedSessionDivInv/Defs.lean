module

public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Defs

/-!
# Diverging calls of linked sessions, both directions: definitions

**Scope.** `Linked2` only: the import-free exporter A (`l.exp`) answering every import of the
importer B (`l.imp`) through the canonical ABI, under `Linked2.Adequate` for the theorems. The
divergence notions are #730's (`LinkedSessionDiv.Defs`): `Linked2.refDivs` on the reference
machine (`RefSessQuiet`: a resumable reference session of `l.toRef` under `linkHost impl`, then a
`CallDiverges`) and `Linked2.sessDivs` on the specification (a `SessSpec` session, then a round
that never answers, `RoundDiv`: B diverges host-free, A diverges inside an import call, or
chatter).

* `Linked2.DivRefToSpec P prof l`: the converse of #730's `DivSpecToRef`, every reference
  divergence is a specification one (`refDivs ⊆ sessDivs`), for typed calls, under every host;
* `Linked2.RefSessEquivD P prof l l'`: the resumable-session equivalence `RefSessEquiv` (#726)
  together with the same **quiet divergences**, both defined on the reference machine only:
  for typed calls, under every host, the diverging session calls (`refDivs`) are the same.

The theorems (`LinkedSessionDivInv.Thms`) prove `DivRefToSpec`, hence `sessDivs = refDivs`, and
that the divergence clause of `RefSessEquivD` may equally be stated on the specification
(`sessDivs`), as #680's `RefSessEquivD.iff_refDivs` for `Simple`.

**Not covered.** Host observations (within `Linked2`, `l.toRef` has no host imports; a parent
passing host imports to B, `linkedHRef`, is not covered). Productive (infinite) linked
executions come next, through `mem_inf_linkS_iff_of_det` (#706). The parser from bytes to these
components, and F6, are pending.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

/-- **Reference divergence is specification divergence** (a named proposition, proved for
adequate components by `Linked2.divRefToSpec`): for typed calls, every diverging session call of
the reference machine, under every host, is one of the specification. -/
def DivRefToSpec (P : Profile) (prof : ProfileKind) (l : Linked2) : Prop :=
  ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal), SimpleI.TypedCalls l.imp calls →
    ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      refDivs P prof l impl h₀ calls j vs ⊆ sessDivs P l calls j vs

/-- **The resumable-session equivalence with quiet divergence**, on the reference machine only:
`RefSessEquiv` (the same export types, and the same terminating session outcomes), and for every
typed sequence of calls followed by a typed call, the same outcomes after which that call
diverges (`refDivs`), under every host. -/
structure RefSessEquivD (P : Profile) (prof : ProfileKind) (l l' : Linked2) : Prop
    extends RefSessEquiv P prof l l' where
  div : ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
      (vs : List IVal), SimpleI.TypedCalls l.imp calls →
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      refDivs P prof l impl h₀ calls j vs =
        refDivs P prof l' impl h₀ (castCalls len calls) (Fin.cast len j) vs

end Linked2

end Silmaril.Wasm.Component.Reference
