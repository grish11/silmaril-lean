module

public import Silmaril.Wasm.Abstract.PubModule.Defs

/-!
# The public interaction of an export through a store view: definitions

The public strategy `pubStrat P host Ok s a` of `Silmaril.Wasm.Abstract.PubModule` plays on the
host interface `wasmHostSig H`, whose calls and answers carry whole stores, function code
included. So two exports whose stores differ anywhere, even in code that is never run, are never
identified (`pubStrat_eq_iff`, `PubEquiv`). This module coarsens the observation through a
**store view** `π : Store H → O`: what the observer may inspect of a store.

**The view interface.** `viewSig H O` is `wasmHostSig H` with every store replaced by its view:
a host call is a host function, a viewed store and arguments, answered by a viewed store and a
result. `viewCall π` and `viewOp π` map host calls and host call operations to it, and
`viewTriple π T` is the image of a public observation triple `T` (of `pubTriple`) under them:
logs pointwise, pending operations, productive streams pointwise, and the final store of a
returning end. `viewStrat π P host Ok s a` is the canonical play object `StratObs.toDStrat` of
the image of the Core public triple.

**`PubEquivV π P host Ok s a s' a'`** is stated from Core runs only, in the style of `PubEquiv`:
for every argument list `vs` and every viewed log `l`, on the invocations admitted by `Ok`, the
two exports have the same

* returns: a run to the values `ws` in the empty frame, with a log viewed as `l` and a final
  store viewed as `o`;
* traps after a log viewed as `l`;
* pending callouts after a log viewed as `l`: a reached host call `hh` with arguments `us` in a
  store viewed as `o` that the host leaves pending (`HostPends`: no outcome, or divergence).
  Blocked and host-divergent callouts are one clause: two stores with the same view may be one
  blocked and one host-divergent, and the view triple does not tell them apart;
* host-free divergence after a log viewed as `l`;
* productive runs viewed as `ω'`.

**`HostView π host`**: whether `host` leaves a call pending depends only on the view of its
store. It is the restriction under which the view strategy is injective modulo `PubEquivV`.

**Scope.** This is the observation through the view `π` against one fixed host, with that
host's answers. An answer store is shown only through `π`, so different continuations behind
the same viewed answer are merged: it is a coarsening of `PubEquiv`, not a statement about
other hosts, and not contextual full abstraction. Native stores, no exceptions, as in
`PubModule`. That a concrete view identifies exports with different internal code (an export
with an internal helper and the export with the helper inlined) is not proved here.

Theorems in `Silmaril.Wasm.Abstract.PubView.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H O : Type}

/-- The host interface through a store view: a call is a host function, a viewed store and
arguments, answered by a viewed store and a result. -/
abbrev viewSig (H O : Type) : Sig.{0} := ⟨H × O × List Val, fun _ => O × Result⟩

/-- A host call operation through the view `π`. -/
def viewOp (π : Store H → O) (m : (wasmHostSig H).Op) : (viewSig H O).Op := (m.1, π m.2.1, m.2.2)

/-- An answered host call through the view `π`: both stores are viewed. -/
def viewCall (π : Store H → O) (e : Call (wasmHostSig H)) : Call (viewSig H O) :=
  ⟨viewOp π e.1, (π e.2.1, e.2.2)⟩

/-- The public interface through a store view: an answer is a result with its viewed final
store, or a trap. -/
abbrev viewSigPub (O : Type) : Sig.{0} := funSig PUnit (List Val) ((List Val ⊕ Nat) × O)

/-- A public end through the view `π`: the final store of a return is viewed. -/
def viewEnd {B : Type} (π : Store H → O) : End PUnit (B × Store H) → End PUnit (B × O)
  | .ret (b, s) u => .ret (b, π s) u
  | .trap => .trap
  | .div => .div

/-- **The view of a public triple**: the image of `T` under the view `π` of logs, pending
operations, productive streams and final stores. -/
def viewTriple (π : Store H → O)
    (T : ObsTriple (wasmHostSig H) PUnit (List Val) ((List Val ⊕ Nat) × Store H)) :
    ObsTriple (viewSig H O) PUnit (List Val) ((List Val ⊕ Nat) × O) :=
  (fun u vs => (fun x => (x.1.map (viewCall π), viewEnd π x.2)) '' T.1 u vs,
    fun u vs => (fun x => (x.1.map (viewCall π), viewOp π x.2)) '' T.2.1 u vs,
    fun u vs => (fun ω => viewCall π ∘ ω) '' T.2.2 u vs)

/-- **The view strategy** of the export `(s, a)` through `π`, from Core runs. -/
def viewStrat (π : Store H → O) (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) :
    DStrategy (viewSig H O) (viewSigPub O) :=
  StratObs.toDStrat (viewTriple π (pubTriple (coreTriple P host Ok) s a))

/-- **The public interaction equivalence through the view `π`** of two exports `(s, a)` and
`(s', a')` against `host` at the profile `P`, on the invocations admitted by `Ok`: for every
argument list `vs` and viewed log `l`, the same returns with viewed final store, the same traps,
the same pending callouts in a viewed store, the same host-free divergence, and the same viewed
productive runs. -/
def PubEquivV (π : Store H → O) (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) (s' : Store H) (a' : Nat) :
    Prop :=
  ∀ vs : List Val,
    (∀ (l : List (Call (viewSig H O))) (ws : List Val) (o : O),
      (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
          EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ ∧ cs.map (viewCall π) = l ∧
          π s₂ = o) ↔
        (Ok s' (a', vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
          EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, vals ws⟩ ∧ cs.map (viewCall π) = l ∧
          π s₂ = o)) ∧
    (∀ l : List (Call (viewSig H O)),
      (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
          EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ ∧ cs.map (viewCall π) = l) ↔
        (Ok s' (a', vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
          EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, [.trap]⟩ ∧ cs.map (viewCall π) = l)) ∧
    (∀ (l : List (Call (viewSig H O))) (hh : H) (o : O) (us : List Val),
      (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (c : Config H)
          (E : SingleThreaded.Ctx) (b : Nat),
          EvRun P host (invoke s a vs) cs c ∧
          SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧
          cs.map (viewCall π) = l ∧ π c.store = o ∧ HostPends host (hh, c.store, us)) ↔
        (Ok s' (a', vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (c : Config H)
          (E : SingleThreaded.Ctx) (b : Nat),
          EvRun P host (invoke s' a' vs) cs c ∧
          SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧
          cs.map (viewCall π) = l ∧ π c.store = o ∧ HostPends host (hh, c.store, us))) ∧
    (∀ l : List (Call (viewSig H O)),
      (Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (c : Config H),
          EvRun P host (invoke s a vs) cs c ∧ Diverges P (fun _ _ _ _ => False) c ∧
          cs.map (viewCall π) = l) ↔
        (Ok s' (a', vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (c : Config H),
          EvRun P host (invoke s' a' vs) cs c ∧ Diverges P (fun _ _ _ _ => False) c ∧
          cs.map (viewCall π) = l)) ∧
    ∀ ω' : Nat → Call (viewSig H O),
      (Ok s (a, vs) ∧ ∃ ω : Nat → Call (wasmHostSig H),
          CoreInf P host (invoke s a vs) ω ∧ viewCall π ∘ ω = ω') ↔
        (Ok s' (a', vs) ∧ ∃ ω : Nat → Call (wasmHostSig H),
          CoreInf P host (invoke s' a' vs) ω ∧ viewCall π ∘ ω = ω')

/-- **A host whose pending behaviour factors through the view `π`**: whether it leaves a call
pending depends on the store only through its view. -/
def HostView (π : Store H → O) (host : HostSemantics H) : Prop :=
  ∀ (hh : H) (s₁ s₂ : Store H) (us : List Val), π s₁ = π s₂ →
    (HostPends host (hh, s₁, us) ↔ HostPends host (hh, s₂, us))

end Silmaril.Wasm.Abstract
