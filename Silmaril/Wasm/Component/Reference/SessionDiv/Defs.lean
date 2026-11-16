module

public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs

/-!
# Diverging session calls on the reference machine: definitions

`SessionStrat` (#680) compares divergence through the canonical-ABI specification's Core runs
(`DivAt`, `sessDivs`). This module defines the same notion on **reference-machine runs**, so
that the two can be compared (`SessionDiv.Thms`):

* `SessDiv prof h m k calls outs f args`: from `m`, the resumable session of the top-level
  calls `calls` (numbered `k, k + 1, …`) has outcomes `outs` (as in #676's `SessCalls`: a
  resolved call continues from the configuration it ends in, a trapped call resumes from
  `resumeCfg`), and then the top-level call of `f` on `args` diverges (`CallDiverges`: the
  host's invocation, then an infinite run of machine-internal steps);
* `sessDivBehaviours`: instantiate the component from the empty store, run the session of the
  named calls, then diverge on the named last call;
* `refDivs P prof c calls j vs`: the IR session outcomes `outs` whose reference images are such
  a diverging session of `c.toRef` on the reference host `refHost P`. It is the
  reference-machine counterpart of `sessDivs P c calls j vs`.

Like `SessCalls`, this uses the session extension of REF (resume after a trap); REF itself locks
the store down after a trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

section Session

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- **A resumable session ending in a divergent call**: from `m`, the top-level calls
`k, k + 1, …` of `calls` have the outcomes `outs` (`some rs` resolved, `none` trapped and
resumed from `resumeCfg`), and then top-level call `k + calls.length` of `f` on `args`
diverges. -/
inductive SessDiv (prof : ProfileKind) (h : Host E σ) :
    Machine.Config E σ → Nat → List (FuncId × List Val) → List (Option (List Val)) →
    FuncId → List Val → Prop where
  | div {m : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List Val} :
      CallDiverges prof h.hr h.dispatch m ⟨k⟩ f args → SessDiv prof h m k [] [] f args
  | ret {m m₁ : Machine.Config E σ} {k : Nat} {g : FuncId} {gargs rs : List Val}
      {cs : List (FuncId × List Val)} {outs : List (Option (List Val))} {f : FuncId}
      {args : List Val} :
      Calls prof h.hr h.dispatch m ⟨k⟩ g gargs m₁ (.resolved (some rs)) →
      SessDiv prof h m₁ (k + 1) cs outs f args →
      SessDiv prof h m k ((g, gargs) :: cs) (some rs :: outs) f args
  | trap {m m₁ : Machine.Config E σ} {k : Nat} {g : FuncId} {gargs : List Val}
      {cs : List (FuncId × List Val)} {outs : List (Option (List Val))} {f : FuncId}
      {args : List Val} :
      Calls prof h.hr h.dispatch m ⟨k⟩ g gargs m₁ .trap →
      SessDiv prof h (resumeCfg m m₁) (k + 1) cs outs f args →
      SessDiv prof h m k ((g, gargs) :: cs) (none :: outs) f args

/-- **The diverging resumable sessions**: instantiate `c` from the empty store, call the
exports named in `calls` as a resumable session with outcomes `outs`, then the call of the
export named `last.1` on `last.2` diverges. -/
def sessDivBehaviours (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (calls : List (String × List Val)) (last : String × List Val) :
    Set (List (Option (List Val))) :=
  {outs | ∃ m₀ inst es fs f,
    InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) c [] ∧
    calls.mapM (fun q => es.lookup q.1) = some fs ∧ es.lookup last.1 = some f ∧
    SessDiv prof h m₀ 0 (fs.zip (calls.map Prod.snd)) outs f last.2}

end Session

/-- **The diverging session calls of the reference machine**: the IR outcomes `outs` of a
resumable reference session of the calls `calls` after which the call of export `j` on `vs`
diverges on the reference machine. -/
noncomputable def refDivs (P : Profile) (prof : ProfileKind) (c : Simple)
    (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
    (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | refOuts outs ∈ sessDivBehaviours prof (refHost P) () c.toRef
    (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal))
    (c.exports[j].name, vs.map toRefVal)}

end Silmaril.Wasm.Component.Reference
