module

public import Silmaril.Wasm.Component.Reference.SessionObs.Defs
public import Silmaril.Wasm.Component.Reference.SessionDiv.Thms
public import Silmaril.Wasm.Component.Reference.SessionStrat.Thms
import Silmaril.Proofs.Wasm.Component.Reference.SessionObs.Main

/-!
# Reference session observations of infinite behaviour: theorems

For `Simple` components, on reference-machine runs (`SessionObs.Defs`), finite and infinite
behaviour:

* **prefix closure** (`SessExec.prefix`, every engine; `RefSessProd.prefix`, every profile): a
  coherent productive execution gives every finite prefix as a resumable session behaviour;
* **the converse** (`Simple.refSessProd_of_prefix_of_storeDet`; at `profile o`,
  `Simple.refSessProd_iff_prefix`): if every finite prefix of a typed stream of calls is a session
  behaviour, there is one coherent productive execution. The exact hypothesis is store
  determinism of the session triple (`StoreDet (compTripleS P c I)`, which holds at the
  deterministic profiles, `storeDet_compTripleS`): it makes the stores reached by the prefixes
  cohere (`infRounds_of_rounds`), and the reference configurations are then built forward, one
  call at a time, from the stores. Without determinism the converse can fail (König-style: each
  prefix may be reached by a different execution with no common infinite extension, as for
  `StratThread.not_coherent`); the reference machine itself is not shown deterministic, nor needs
  to be;
* **relation to the session object** (`Simple.refSessProd_iff_infRounds`,
  `Simple.refSessProd_iff_inf`, at `profile o`): a productive execution is a coherent infinite
  sequence of rounds of the triple (`InfRounds (compTripleS …)`) and an infinite play of
  `compSession`, through `mem_inf_compSession`, `StratSession.mem_inf_iff_of_storeDet` and
  `Simple.sessInf_iff`;
* **quiescent divergence** (`refSessQuiet_iff_refDivs`): it is `SessionDiv`'s `refDivs`; at
  `profile o` it excludes termination of the same call after the same session
  (`RefSessQuiet.not_terminates`);
* **host divergence is vacuous** (`Simple.sess_no_callout`, every profile): `Simple` components
  have no imports, and the lowered call of every session call never reaches a host call redex,
  so the reference machine's core activation never takes a callout step
  (`Step.coreCallout` needs a `callout` status) and there is no productive run;
* **the full injection** (`Simple.compSession_inj_full`, at `profile o`, every component choice
  profile):
  `RefSessEquivFull (profile o) prof c c' ↔ SameTypes c c' ∧ compSession (profile o) c = compSession (profile o) c'`.
  It goes through `RefSessEquivFull.iff_refSessEquivD`: at `profile o` the full equivalence is
  `RefSessEquivD`. The productive clause adds nothing there, since under store determinism a
  productive execution is determined by its finite prefixes, which `RefSessEquiv` compares; the
  quiescent clause is `RefSessEquivD`'s divergence clause (`RefSessEquivD.iff_refDivs`).

Non-claims: `Simple` (adequate) components only; deterministic profiles for the converse facts
and the injection; not contextual full abstraction (the observer is a host calling exports in
sequence); the parser from bytes to `Comp` is out of scope; the native store-retaining closing of
`StratSession` (closing a session object against its host) belongs to its owner and is separate.
The sessions resume after a trap (`resumeCfg`); REF itself locks the store down.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.SessionObs.Main`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratThread (StoreDet InfRounds)
open Silmaril.Games.Abstract.StratSession (sroundsPlay)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

section Machine

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

/-- **Prefix closure on the machine** (every engine): a coherent execution gives each finite
prefix as a resumable session. -/
theorem SessExec.prefix {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}
    {prof : ProfileKind} {h : Host E σ} {m₀ : Machine.Config E σ} {a : ℕ → FuncId × List Val}
    {out : ℕ → Option (List Val)} {m : ℕ → Machine.Config E σ}
    (hx : SessExec prof h m₀ a out m) (n : ℕ) :
    SessCalls prof h m₀ 0 (streamTake a n) (streamTake out n) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.SessExec.prefix hx n

end Machine

variable {P : Profile} {prof : ProfileKind} {c : Simple}

/-- **Quiescent divergence is `refDivs`.** -/
theorem refSessQuiet_iff_refDivs {calls : List (Fin c.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {j : Fin c.exports.length} {vs : List IVal} :
    RefSessQuiet P prof c calls outs j vs ↔ outs ∈ refDivs P prof c calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.refSessQuiet_iff

/-- **Prefix closure** (every profile): a productive execution gives every finite prefix as a
resumable reference session behaviour. -/
theorem RefSessProd.prefix {a : ℕ → Fin c.exports.length × List IVal}
    {out : ℕ → Option (List IVal)} (h : RefSessProd P prof c a out) (n : ℕ) :
    refOuts (streamTake out n) ∈ sessObs P prof c (streamTake a n) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.refSessProd_prefix h n

/-- **The converse of prefix closure, under store determinism**: if the session triple is
store-deterministic and every finite prefix of the typed calls `a` with outcomes `out` is a
session behaviour, there is a coherent productive execution. -/
theorem Simple.refSessProd_of_prefix_of_storeDet (hc : c.Adequate)
    (hdet : ∀ I, c.mod.IsInst I → StoreDet (compTripleS P c I))
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true)
    (h : ∀ k, refOuts (streamTake out k) ∈ sessObs P prof c (streamTake a k)) :
    RefSessProd P prof c a out :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.refSessProd_of_prefix prof hc hdet a out
    ht h

/-- **Productive executions are their finite prefixes** (deterministic profiles). -/
theorem Simple.refSessProd_iff_prefix (o : GrowOracle) (hc : c.Adequate)
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) :
    RefSessProd (profile o) prof c a out ↔
      ∀ k, refOuts (streamTake out k) ∈ sessObs (profile o) prof c (streamTake a k) :=
  ⟨RefSessProd.prefix, Simple.refSessProd_of_prefix_of_storeDet hc
    (fun _ _ => storeDet_compTripleS o) a out ht⟩

/-- **Productive executions are coherent rounds of the session triple** (deterministic
profiles). -/
theorem Simple.refSessProd_iff_infRounds (o : GrowOracle) (hc : c.Adequate)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) :
    RefSessProd (profile o) prof c a out ↔
      ∃ s, InfRounds (compTripleS (profile o) c I) I.store
        (fun k => (((a k).1 : Nat), Payload.vals (a k).2)) (fun k => ([], outAns (out k))) s := by
  rw [Simple.refSessProd_iff_prefix o hc a out ht]
  exact ⟨Silmaril.Proofs.Wasm.Component.Reference.SessionObs.infRounds_of_prefix prof hc hI
    (storeDet_compTripleS o) a out ht, fun ⟨_, hs⟩ => (Simple.sessInf_iff o prof hc a out ht).mp
      (compSession_eq hI ▸ StratSession.InfRounds.mem_sinf hs)⟩

/-- **Productive executions are infinite plays of the session object** (deterministic
profiles). -/
theorem Simple.refSessProd_iff_inf (o : GrowOracle) (hc : c.Adequate)
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) :
    RefSessProd (profile o) prof c a out ↔
      sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (compSession (profile o) c).inf :=
  (Simple.refSessProd_iff_prefix o hc a out ht).trans (Simple.sessInf_iff o prof hc a out ht).symm

/-- **Quiescent divergence excludes termination of the same call** (deterministic profiles):
after a session in which the call of export `j` on `vs` diverges, no session with the same
earlier outcomes ends that call with results or a trap. -/
theorem RefSessQuiet.not_terminates (o : GrowOracle) (hc : c.Adequate)
    {calls : List (Fin c.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {j : Fin c.exports.length} {vs : List IVal} (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (hq : RefSessQuiet (profile o) prof c calls outs j vs)
    (r : Option (List Silmaril.Wasm.Component.Reference.Val)) :
    refOuts outs ++ [r] ∉ sessObs (profile o) prof c (calls ++ [(j, vs)]) :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.quiet_not_terminates o prof hc ht hvs hq r

/-- **No host callout in a session call** (every profile): after a session of the
specification from the instance's store, the lowered call of a typed export never reaches a host
call. Host divergence is vacuous for `Simple` components. -/
theorem Simple.sess_no_callout (hc : c.Adequate) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) {calls : List (Fin c.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {s : Silmaril.Wasm.Execution.Core.Store Nat}
    (hs : SessSpec P c I I.store (specCalls c calls) outs s) (j : Fin c.exports.length)
    {vs : List IVal} (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {s' : Silmaril.Wasm.Execution.Core.Store Nat} {t' : Silmaril.Wasm.SingleThreaded.Thread}
    (run : Silmaril.Wasm.Game.Reach P
      (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
        (lowerArgs c.exports[j].ty.params vs)) (s', t')) :
    ∀ hh args, ¬ Silmaril.Wasm.Game.CalloutAt s' t' hh args :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.sess_no_callout hc hI hs j hvs run

/-- **At the deterministic profiles the full equivalence is `RefSessEquivD`** (proved): the
productive clause follows from the terminating outcomes of the prefixes. -/
theorem RefSessEquivFull.iff_refSessEquivD (o : GrowOracle) {c c' : Simple} (hc : c.Adequate)
    (hc' : c'.Adequate) :
    RefSessEquivFull (profile o) prof c c' ↔ RefSessEquivD (profile o) prof c c' :=
  Silmaril.Proofs.Wasm.Component.Reference.SessionObs.refSessEquivFull_iff o prof hc hc'

/-- **The full-strategy injection** (deterministic profiles, every component choice profile):
for adequate simple components, the full reference-session equivalence (terminating outcomes,
quiescent divergence and productive executions, all on reference-machine runs) is equality of
export types and of session objects. -/
theorem Simple.compSession_inj_full (o : GrowOracle) {c c' : Simple} (hc : c.Adequate)
    (hc' : c'.Adequate) :
    RefSessEquivFull (profile o) prof c c' ↔
      SameTypes c c' ∧ compSession (profile o) c = compSession (profile o) c' :=
  (RefSessEquivFull.iff_refSessEquivD o hc hc').trans (Simple.compSession_inj o prof hc hc')

end Silmaril.Wasm.Component.Reference
