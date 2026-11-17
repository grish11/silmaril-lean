module

public import Silmaril.Wasm.Component.Reference.LinkedGInf.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.Main

/-!
# Infinite plays and the full injection of linked components and chains: theorems

**Scope.** `LinkedG` with an exporter `ExpSpec` and a simple importer, in particular one more
importer `b` on a chain `n` with a simple base (`⟨n.spec Ib Is, b, w⟩`, under `LinkedN.ExtOk`);
the IR `g.toComp.denUD (impSemD P)` over `sigU`; the reference machine over `core3P P` under
`linkHost impl`, every host and every component choice profile; typed calls and typed call
streams. The iffs are at the deterministic profiles `profile o`, for links meeting
`LinkedG.ProfOk o`. This mirrors `Linked2` (#746 `LinkedSessionObs`, #833 `LinkedSessionDAdeq`).

**Proved (public, below).**

1. **Productive executions** (`LinkedG.RefSessProd`):
   * prefix closure, every profile (`LinkedG.RefSessProd.prefix`);
   * a run of rounds of `g.toExp Ii` from its initial state is a productive execution, every
     profile (`LinkedG.refSessProd_of_run`): one linked call at a time from between calls;
   * conversely, for a deterministic `g.toExp Ii`, the finite prefixes of typed calls, as session
     behaviours, are read back along one run (`LinkedG.run_of_prefix`), so
     `LinkedG.refSessProd_iff_run` and `LinkedG.refSessProd_iff_prefix` at `profile o`.
2. **Infinite plays** (`ExpSpec.inf_iff_run`, for a deterministic exporter meeting `Adeq` and
   `AdeqI`: `AdeqI` one way, the runs of the finite prefixes cohering the other, the converse of
   `AdeqI` as `ExpSpec.AdeqIC` does it); `LinkedG.inf_iff_run` and
   **`LinkedG.inf_iff_profile`**: the infinite IR play of a typed call stream (`sessInfU`) is an
   infinite play of `g.toComp.denUD (impSemD (profile o))` iff it is a productive execution on
   the reference machine. For chains: `LinkedN.ExtOk.profOk`, **`LinkedN.inf_iff_profile`**.
3. **The full injection** (**`LinkedG.refSessEquivFull_iff`**, **`LinkedN.refSessEquivFull_iff`**):
   the reference-defined `LinkedG.RefSessEquivFull` (terminating outcomes, quiescent divergences,
   productive executions, every host) is the same export types and the same typed finite plays,
   divergences and infinite plays of the IR (`IRFinEq`, `IRDivEq`, `IRInfEq`), from
   `LinkedG.sessObs_eq_ir` (finite), `LinkedG.quiet_iff` (`LinkedG.sessDivs_eq_refDivs`,
   `LinkedG.div_iff_sessDivs`, `LinkedG.toExp_adeqD_profile`) and `LinkedG.inf_iff_profile`.

**Deviations from #833.**

* The finite plays are compared on typed complete sessions (`IRFinEq`), not as whole strategies
  (`pubPlays`): the exporter interface `ExpSpec.Adeq` says nothing about ill-typed calls of a
  linked component (for `Linked2` they trap at once, `Linked2.den_filter_iff`; that is not
  proved for `LinkedG`).
* The hypotheses are bundled: `LinkedG.ProfOk o g` (the exporter's IR and reference interfaces,
  determinism and `LinkOk`) and `LinkedN.ExtOk n Ib Is b w` (the hypotheses of
  `LinkedN.sessDivs_eq_refDivs`). For a chain the component compared is the link
  `⟨n.spec Ib Is, b, w⟩`, whose IR component is `linkComp n.toComp b w`
  (`LinkedN.spec_comp`; `LinkedN.toComp_extend`).

**Not proved.**

* The canonical session object of a chain (`compSession` through `threadS`) and its injection
  (#746's `Linked2.compSession_inj_full`).
* Nondeterministic profiles: the converse of prefix closure and the read-back of infinite plays
  use the determinism of `g.toExp Ii` (`ExpSpec.Det`); the divergence iff needs the read-back of
  chatter (`LinkedG.Task.ChatterReadBack`), open there.
* Ill-typed calls and the finite plays outside typed complete sessions.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.{Ref, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Wasm.Component.Canon (HostImpl)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## An exporter -/

/-- **The infinite IR plays of a typed stream of rounds are its runs** (proved, every profile),
for a deterministic exporter meeting `Adeq` and `AdeqI`. -/
theorem ExpSpec.inf_iff_run {P : Profile} {e : ExpSpec} (he : e.Adeq P) (hI : e.AdeqI P)
    (hd : e.Det P) (r : ℕ → URound) (ht : ∀ k, e.Typed (r k)) :
    Chain.lim (fun n => uMoves (streamTake r n)) ∈ (e.comp.denUD (impSemD P)).inf ↔
      ∃ S : ℕ → e.St, S 0 = e.init ∧ ∀ k, e.Step P (S k) (r k) (S (k + 1)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.inf_iff_stream he hI hd r ht

namespace LinkedG

/-! ## Productive executions -/

section Prod

variable {P : Profile} {prof : ProfileKind} {g : LinkedG}

/-- **Prefix closure** (proved, every profile): a productive execution gives every finite prefix
as a resumable reference session behaviour. -/
theorem RefSessProd.prefix {σ : Type} {impl : HostImpl (core3P P) σ} {h₀ : σ}
    {a : ℕ → Fin g.imp.exports.length × List IVal} {out : ℕ → Option (List IVal)}
    (h : LinkedG.RefSessProd P prof g impl h₀ a out) (n : ℕ) :
    refOuts (streamTake out n) ∈ LinkedG.sessObs prof g impl h₀ (streamTake a n) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.refSessProd_prefixG h n

/-- **A run of rounds is a productive execution** (proved, every profile and component choice
profile, under every host): a stream of calls served along one run of `g.toExp Ii` from its
initial state. -/
theorem refSessProd_of_run (he : g.exp.RefAdeqUX P) (hl : g.LinkOk) {Ii : ScalarInstance}
    (hI : g.imp.mod.IsInst Ii) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    {S : ℕ → (g.toExp Ii).St} (h0 : S 0 = (g.toExp Ii).init)
    (hS : ∀ k, (g.toExp Ii).Step P (S k) (g.roundU a out k) (S (k + 1))) :
    LinkedG.RefSessProd P prof g impl h₀ a out :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.refSessProd_of_run he hl hI impl h₀ a out
    h0 hS

/-- **Finite prefixes read back along one run** (proved, every profile and component choice
profile, under every host, typed calls): for a deterministic `g.toExp Ii`, if every finite
prefix is a session behaviour, one run of `g.toExp Ii` serves the whole stream. -/
theorem run_of_prefix (he : g.exp.RefAdeqUX P) (hl : g.LinkOk) {Ii : ScalarInstance}
    (hI : g.imp.mod.IsInst Ii) (hd : (g.toExp Ii).Det P)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (h : ∀ n, refOuts (streamTake out n) ∈ LinkedG.sessObs prof g impl h₀ (streamTake a n)) :
    ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
      ∀ k, (g.toExp Ii).Step P (S k) (g.roundU a out k) (S (k + 1)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.run_of_prefix he hl hI hd a out ht impl h₀ h

end Prod

section Profile

variable {o : GrowOracle} {prof : ProfileKind} {g : LinkedG}

/-- **Productive executions are runs of the linked specification** (proved, `profile o`, every
component choice profile, under every host, typed calls). -/
theorem refSessProd_iff_run (hg : g.ProfOk o) {Ii : ScalarInstance} (hI : g.imp.mod.IsInst Ii)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    LinkedG.RefSessProd (profile o) prof g impl h₀ a out ↔
      ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
        ∀ k, (g.toExp Ii).Step (profile o) (S k) (g.roundU a out k) (S (k + 1)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.refSessProd_iff_runG hg hI a out ht impl h₀

/-- **Productive executions are their finite prefixes** (proved, `profile o`, every component
choice profile, under every host, typed calls). -/
theorem refSessProd_iff_prefix (hg : g.ProfOk o) (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    LinkedG.RefSessProd (profile o) prof g impl h₀ a out ↔
      ∀ n, refOuts (streamTake out n) ∈ LinkedG.sessObs prof g impl h₀ (streamTake a n) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.refSessProd_iff_prefixG hg a out ht impl h₀

/-! ## Infinite plays -/

/-- **The infinite IR plays of typed call streams are the runs of the linked specification**
(proved, `profile o`). -/
theorem inf_iff_run (hg : g.ProfOk o) {Ii : ScalarInstance} (hI : g.imp.mod.IsInst Ii)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) :
    g.sessInfU a out ∈ (g.toComp.denUD (impSemD (profile o))).inf ↔
      ∃ S : ℕ → (g.toExp Ii).St, S 0 = (g.toExp Ii).init ∧
        ∀ k, (g.toExp Ii).Step (profile o) (S k) (g.roundU a out k) (S (k + 1)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.inf_iff_runG hg hI a out ht

/-- **The infinite IR plays of typed call streams are the productive executions** (proved,
`profile o`, every component choice profile, under every host, typed calls). -/
theorem inf_iff_profile (hg : g.ProfOk o) (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    g.sessInfU a out ∈ (g.toComp.denUD (impSemD (profile o))).inf ↔
      LinkedG.RefSessProd (profile o) prof g impl h₀ a out :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.inf_iff_profileG hg a out ht impl h₀

/-! ## The full injection -/

/-- **The terminating session outcomes are the typed finite IR plays** (proved, `profile o`,
every component choice profile, under every host, typed calls). -/
theorem sessObs_eq_ir (hg : g.ProfOk o) {σ : Type} (impl : HostImpl (core3P (profile o)) σ)
    (h₀ : σ) (calls : List (Fin g.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls g.imp calls) :
    LinkedG.sessObs prof g impl h₀ calls =
      {x | ∃ outs, x = refOuts outs ∧ calls.length = outs.length ∧
        uMoves (g.sessU calls outs) ∈ (g.toComp.denUD (impSemD (profile o))).toStrategy} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.sessObs_eq_irG hg impl h₀ calls ht

/-- **The quiescent divergences are the IR divergences after typed sessions** (proved,
`profile o`, every component choice profile, under every host, typed calls and a typed pending
call). -/
theorem quiet_iff (hg : g.ProfOk o) {σ : Type} (impl : HostImpl (core3P (profile o)) σ)
    (h₀ : σ) (calls : List (Fin g.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) (j : Fin g.imp.exports.length) (vs : List IVal)
    (ht : SimpleI.TypedCalls g.imp calls)
    (hvs : ValTy.checkList g.imp.exports[j].ty.params vs = true) :
    LinkedG.RefSessQuiet (profile o) prof g impl h₀ calls outs j vs ↔
      calls.length = outs.length ∧ uMoves (g.sessU calls outs) ++ [.inr (.ask (j.val, .vals vs))] ∈
        (g.toComp.denUD (impSemD (profile o))).div :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.quiet_iffG hg impl h₀ calls outs j vs ht hvs

/-- **The full injection of the IR** (proved, `profile o`, every component choice profile): for
links meeting `ProfOk`, the full resumable-session equivalence on the reference machine
(terminating outcomes, quiescent divergences and productive executions, every host) is the same
export types and the same typed finite plays, divergences and infinite plays of
`g.toComp.denUD (impSemD (profile o))` and of `g'`'s. -/
theorem refSessEquivFull_iff {g' : LinkedG} (hg : g.ProfOk o) (hg' : g'.ProfOk o) :
    LinkedG.RefSessEquivFull (profile o) prof g g' ↔ LinkedG.SameTypes g g' ∧
      LinkedG.IRFinEq (profile o) g g' ∧ LinkedG.IRDivEq (profile o) g g' ∧
      LinkedG.IRInfEq (profile o) g g' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.refSessEquivFull_iffG hg hg'

end Profile

end LinkedG

/-! ## Chains -/

namespace LinkedN

variable {o : GrowOracle} {prof : ProfileKind} {n : LinkedN} {Ib : ScalarInstance}
  {Is : List ScalarInstance} {b : SimpleI} {w : List Nat}

/-- **One more importer on a chain with a simple base meets `ProfOk`** (proved). -/
theorem ExtOk.profOk (o : GrowOracle) (h : n.ExtOk Ib Is b w) :
    (LinkedG.mk (n.spec Ib Is) b w).ProfOk o :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInf.extOk_profOk o h

/-- **The infinite plays of one more importer on a chain are its productive executions**
(proved, `profile o`, every component choice profile, under every host, typed calls): the
infinite play of a typed call stream is one of the IR `linkComp n.toComp b w` iff it is a
productive execution on the reference machine. -/
theorem inf_iff_profile (h : n.ExtOk Ib Is b w)
    (a : ℕ → Fin b.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList b.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    (LinkedG.mk (n.spec Ib Is) b w).sessInfU a out ∈
        ((linkComp n.toComp b w).denUD (impSemD (profile o))).inf ↔
      LinkedG.RefSessProd (profile o) prof ⟨n.spec Ib Is, b, w⟩ impl h₀ a out := by
  rw [← spec_comp h.chain.chainOk]
  exact LinkedG.inf_iff_profile (h.profOk o) a out ht impl h₀

/-- **The full injection for chains** (proved, `profile o`, every component choice profile):
for one more importer on each of two chains with simple bases, the full resumable-session
equivalence on the reference machine is the same export types and the same typed finite plays,
divergences and infinite plays of their IR denotations. -/
theorem refSessEquivFull_iff {n' : LinkedN} {Ib' : ScalarInstance} {Is' : List ScalarInstance}
    {b' : SimpleI} {w' : List Nat} (h : n.ExtOk Ib Is b w) (h' : n'.ExtOk Ib' Is' b' w') :
    LinkedG.RefSessEquivFull (profile o) prof ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ ↔
      LinkedG.SameTypes ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ ∧
      LinkedG.IRFinEq (profile o) ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ ∧
      LinkedG.IRDivEq (profile o) ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ ∧
      LinkedG.IRInfEq (profile o) ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ :=
  LinkedG.refSessEquivFull_iff (h.profOk o) (h'.profOk o)

end LinkedN

end Silmaril.Wasm.Component.Reference
