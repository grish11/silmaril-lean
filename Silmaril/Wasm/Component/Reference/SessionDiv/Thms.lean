module

public import Silmaril.Wasm.Component.Reference.SessionDiv.Defs
import Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.Main

/-!
# Diverging session calls on the reference machine: theorems

`SessionStrat` (#680) states divergence on the specification's Core runs (`DivAt`, `sessDivs`),
since the library proved only one direction between the reference machine's `CallDiverges` and
Core divergence (`CallRun.diverges_spec`). This module proves both directions, for `Simple`
components in the adequate fragment (`Good ∧ FloatFree ∧ Inst ∧ Arity`), at every profile `P`
and component choice profile `prof` (no determinism is needed):

* **one call** (`Simple.divAt_iff_refDiv`): the lowered call of export `j` on `vs` from the
  instance's store runs forever host-free (`DivAt`) iff the first top-level call after
  instantiating `c.toRef` diverges on the reference machine (`[] ∈ refDivs P prof c [] j vs`,
  that is a `CallDiverges`, `sessDiv_nil_iff`);
* **inside sessions** (`Simple.sessDivs_eq_refDivs`): after returned and trapped calls (#676's
  resumable sessions, `resumeCfg` after a trap), the diverging session calls of the
  specification (`sessDivs`) are those of the reference machine (`refDivs`);
* **the equivalence** (`RefSessEquivD.iff_refDivs`): the divergence clause of `RefSessEquivD`
  may be stated on reference-machine runs.

No converse fails: the reference machine neither stutters forever nor deadlocks inside the core
activation of these calls. Each Core step is one machine step (`Step.coreInternal`), the
lowering before the core call is a finite live run, and after the core activation the call
returns control to the host or traps (it never calls out, the module having no imports).

Non-claims: as in `SessionAdequacy`, the session resumes after a trap (REF itself locks down);
not contextual full abstraction; the parser from bytes to `Comp` is separate.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.Main`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

section
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

/-- A session of no calls ending in a divergent call is a divergent call. -/
theorem sessDiv_nil_iff {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}
    {prof : ProfileKind} {h : Host E σ} {m : Machine.Config E σ} {k : Nat} {f : FuncId}
    {args : List Val} :
    SessDiv prof h m k [] [] f args ↔ CallDiverges prof h.hr h.dispatch m ⟨k⟩ f args :=
  ⟨fun hd => by cases hd; assumption, .div⟩

end

/-- **One call**: Core divergence of the lowered call from the instance's store is divergence
of the first call on the reference machine (proved). -/
theorem Simple.divAt_iff_refDiv (P : Profile) (prof : ProfileKind) (c : Simple)
    (hc : c.Adequate) {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    DivAt P I c.exports[j] vs I.store ↔ [] ∈ refDivs P prof c [] j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.divAt_iff_refDiv P prof c hc hI j vs hvs

/-- **Inside sessions**: the diverging session calls of the specification are those of the
reference machine (proved). -/
theorem Simple.sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) (c : Simple)
    (hc : c.Adequate) (calls : List (Fin c.exports.length × List IVal))
    (j : Fin c.exports.length) (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    sessDivs P c calls j vs = refDivs P prof c calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.sessDivs_eq_refDivs P prof c hc calls j vs
    ht hvs

/-- **`RefSessEquivD` on reference-machine runs** (proved): the terminating session outcomes and
the diverging session calls of the reference machine. -/
theorem RefSessEquivD.iff_refDivs {P : Profile} {prof : ProfileKind} {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) :
    RefSessEquivD P prof c c' ↔ ∃ h : RefSessEquiv P prof c c',
      ∀ (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
        (vs : List IVal), TypedCalls c calls → ValTy.checkList c.exports[j].ty.params vs = true →
        refDivs P prof c calls j vs =
          refDivs P prof c' (castCalls h.len calls) (Fin.cast h.len j) vs :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.refSessEquivD_iff hc hc'

end Silmaril.Wasm.Component.Reference
