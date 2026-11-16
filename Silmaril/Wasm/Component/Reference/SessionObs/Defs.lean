module

public import Silmaril.Wasm.Component.Reference.SessionDiv.Defs

/-!
# Reference session observations of infinite behaviour: definitions

#676 (`SessionAdequacy`) observes the terminating outcomes of resumable reference sessions
(`SessCalls`, `sessObs`), and `SessionDiv` the sessions ending in a divergent call (`SessDiv`,
`refDivs`). This module names the two infinite observations of a session on the **reference
machine**, with explicit witnesses. Neither is defined from `Comp.den`, from the session
strategies (`compSession`, `compTripleS`) or as a limit of finite prefixes; their relation to
those is proved in `SessionObs.Thms`.

* **Quiescent divergence** `RefSessQuiet P prof c calls outs j vs`: after instantiating
  `c.toRef`, the resumable reference session of `calls` has the outcomes `outs` (a resolved call
  continues from the configuration it ends in, a trapped one resumes from `resumeCfg`), and the
  next top-level call, export `j` on `vs`, diverges (`CallDiverges`: the host's invocation, then
  an infinite run of machine steps). It is the `SessDiv` witness of `refDivs`, spelled out.
* **Host divergence** (a call that keeps calling out to the host forever) is vacuous here:
  `Simple` components have no imports, so a session call never calls out to the host
  (`Simple.sess_no_callout`), and there is no productive run.
* **Productive execution** `RefSessProd P prof c a out`: an infinite session of the calls
  `a 0, a 1, …` with the outcomes `out 0, out 1, …`, given by an explicit stream of reference
  configurations `m : ℕ → Config` (`SessExec`): `m 0` is the configuration after instantiation,
  and for every `k` the top-level call `k` of `a k` runs from `m k` to the outcome `out k`, with
  `m (k + 1)` the configuration it ends in (`SessStep.ret`), or `resumeCfg` after a trap
  (`SessStep.trap`). The stream is a single coherent execution, not one session per prefix.

`RefSessEquivFull P prof c c'`: #676's `RefSessEquiv` (terminating outcomes), and the same
quiescent divergences and the same productive executions, all on reference-machine runs.

Scope (`SessionObs.Thms`): `Simple` components (the adequate fragment for the theorems),
finite and infinite behaviour; the converse facts and the injection need the deterministic
profiles `profile o`. Like `SessCalls`, a session resumes after a trap; REF itself locks the
store down. Not contextual full abstraction (the observer is a host calling exports in
sequence); the parser from bytes to `Comp` is out of scope; the native store-retaining closing
of `StratSession` belongs to its owner.
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

/-- **One call of a resumable session**: top-level call `k` of `f` on `args` from `m` resolves
with `rs` and ends in `m'` (outcome `some rs`), or traps, and the session resumes from
`m' = resumeCfg m mT` (outcome `none`). -/
inductive SessStep (prof : ProfileKind) (h : Host E σ) :
    Machine.Config E σ → Nat → FuncId → List Val → Option (List Val) → Machine.Config E σ →
    Prop where
  | ret {m m₁ : Machine.Config E σ} {k : Nat} {f : FuncId} {args rs : List Val} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ (.resolved (some rs)) →
      SessStep prof h m k f args (some rs) m₁
  | trap {m m₁ : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List Val} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ .trap →
      SessStep prof h m k f args none (resumeCfg m m₁)

/-- **A coherent infinite session execution**: the stream of configurations `m` starts at `m₀`
and call `k` (`a k`, outcome `out k`) runs from `m k` to `m (k + 1)`. -/
structure SessExec (prof : ProfileKind) (h : Host E σ) (m₀ : Machine.Config E σ)
    (a : ℕ → FuncId × List Val) (out : ℕ → Option (List Val)) (m : ℕ → Machine.Config E σ) :
    Prop where
  zero : m 0 = m₀
  step : ∀ k, SessStep prof h (m k) k (a k).1 (a k).2 (out k) (m (k + 1))

/-- **A productive session** from `m₀`: some coherent execution of the calls `a` with the
outcomes `out`. -/
def SessProd (prof : ProfileKind) (h : Host E σ) (m₀ : Machine.Config E σ)
    (a : ℕ → FuncId × List Val) (out : ℕ → Option (List Val)) : Prop :=
  ∃ m, SessExec prof h m₀ a out m

end Session

/-! ## Observations of a simple component -/

/-- **Quiescent divergence of a session**: after instantiating `c.toRef` on the reference host,
the resumable session of `calls` has the outcomes `outs`, and then the call of export `j` on
`vs` diverges on the reference machine (the `SessDiv` witness of `refDivs`). -/
def RefSessQuiet (P : Profile) (prof : ProfileKind) (c : Simple)
    (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (j : Fin c.exports.length) (vs : List IVal) : Prop :=
  ∃ m₀ inst es fs f,
    InstResult.instance m₀ inst es ∈
      instBehaviours prof (refHost P) (initConfig ()) c.toRef [] ∧
    (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).mapM
      (fun q => es.lookup q.1) = some fs ∧
    es.lookup c.exports[j].name = some f ∧
    SessDiv prof (refHost P) m₀ 0 (fs.zip (calls.map fun q => q.2.map toRefVal)) (refOuts outs)
      f (vs.map toRefVal)

/-- **A productive execution of a simple component**: after instantiating `c.toRef` on the
reference host, an explicit coherent stream of reference configurations running the export calls
`a 0, a 1, …` with the outcomes `out 0, out 1, …` (results, or `none` for a trap followed by
`resumeCfg`). -/
def RefSessProd (P : Profile) (prof : ProfileKind) (c : Simple)
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal)) : Prop :=
  ∃ m₀ inst es, ∃ fs : ℕ → Runtime.FuncId,
    InstResult.instance m₀ inst es ∈
      instBehaviours prof (refHost P) (initConfig ()) c.toRef [] ∧
    (∀ k, es.lookup c.exports[(a k).1].name = some (fs k)) ∧
    SessProd prof (refHost P) m₀ (fun k => (fs k, (a k).2.map toRefVal))
      (fun k => (out k).map (List.map toRefVal))

/-- A stream of export calls read at a component with the same number of exports. -/
def castStream {c c' : Simple} (h : c.exports.length = c'.exports.length)
    (a : ℕ → Fin c.exports.length × List IVal) : ℕ → Fin c'.exports.length × List IVal :=
  fun k => (Fin.cast h (a k).1, (a k).2)

/-- **The full resumable-session equivalence**, on reference-machine runs only: the same export
types and terminating session outcomes (`RefSessEquiv`), the same quiescent divergences after
every typed session, and the same productive executions of every typed stream of calls. -/
structure RefSessEquivFull (P : Profile) (prof : ProfileKind) (c c' : Simple) : Prop
    extends RefSessEquiv P prof c c' where
  quiet : ∀ (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (j : Fin c.exports.length) (vs : List IVal), TypedCalls c calls →
    ValTy.checkList c.exports[j].ty.params vs = true →
    (RefSessQuiet P prof c calls outs j vs ↔
      RefSessQuiet P prof c' (castCalls len calls) outs (Fin.cast len j) vs)
  prod : ∀ (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal)),
    (∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) →
    (RefSessProd P prof c a out ↔ RefSessProd P prof c' (castStream len a) out)

end Silmaril.Wasm.Component.Reference
