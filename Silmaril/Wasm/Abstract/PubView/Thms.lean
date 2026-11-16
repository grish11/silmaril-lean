module

public import Silmaril.Wasm.Abstract.PubView.Defs
public import Silmaril.Wasm.Abstract.PubModule.Thms
import Silmaril.Proofs.Wasm.Abstract.PubView.Basic

/-!
# The public interaction of an export through a store view: theorems

**`PubEquivV` is the agreement of the viewed observations.** Two exports are `PubEquivV π`
exactly when the views of their Core public triples are equal (`pubEquivV_iff_viewTriple`).

**The view injection.** For a host whose pending behaviour factors through the view
(`HostView π host`), the view strategies of two exports are equal iff the exports are
`PubEquivV π` (`viewStrat_eq_iff`). The pending calls of the Core triple are its call prefixes
left pending by the host (`coreTriple_pending_eq`); call prefixes commute with the view, and
under `HostView` the viewed pending calls are the viewed call prefixes left pending at some store
with that view. So the view triple is determined by its saturation, which `StratObs.toDStrat`
sees. Without `HostView` a viewed call prefix may be pending for one export and answered for the
other at stores with the same view, and the strategy only sees the call prefix.

**Coarsening.** `PubEquiv` implies `PubEquivV π` for every view, and equal public strategies have
equal view strategies (`pubEquivV_of_pubEquiv`, `pubStrat_eq_viewStrat_eq`), with no hypothesis
on the host. For an injective view nothing is lost: `PubEquivV π` is `PubEquiv`
(`pubEquivV_iff_of_injective`, `pubEquivV_id_iff`), every host factors through it
(`hostView_of_injective`), and the view strategies are equal iff the public strategies are
(`viewStrat_eq_iff_pubStrat_eq`).

**Reading back.** A completed view round with values is a Core run to those values whose log and
final store have those views (`viewStrat_mem_ret`); a one-round infinite view play is the view of
a productive Core run (`viewStrat_mem_inf`).

**Scope.** One fixed host, observed through `π`; the view merges continuations behind equal
viewed answers, so this is a coarsening, not a statement about all hosts and not contextual full
abstraction. Native stores, no exceptions. No concrete view is shown here to identify exports
with different internal code.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.PubView.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H O : Type} {π : Store H → O} {P : Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop} {s s' : Store H} {a a' : Nat}

/-- **`PubEquivV` is the equality of the viewed Core public triples.** -/
theorem pubEquivV_iff_viewTriple :
    PubEquivV π P host Ok s a s' a' ↔
      viewTriple π (pubTriple (coreTriple P host Ok) s a) =
        viewTriple π (pubTriple (coreTriple P host Ok) s' a') :=
  Silmaril.Proofs.Wasm.Abstract.PubView.viewTriple_eq_iff.symm

/-- **The view injection**: for a host whose pending behaviour factors through `π`, two exports
have the same view strategy iff they are publicly equivalent through `π`. -/
theorem viewStrat_eq_iff (hV : HostView π host) :
    viewStrat π P host Ok s a = viewStrat π P host Ok s' a' ↔ PubEquivV π P host Ok s a s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubView.viewStrat_eq_iff hV

/-! ## Coarsening -/

/-- **`PubEquiv` implies `PubEquivV π`** for every view. -/
theorem pubEquivV_of_pubEquiv (h : PubEquiv P host Ok s a s' a') :
    PubEquivV π P host Ok s a s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubView.pubEquivV_of_pubEquiv h

/-- **Equal public strategies have equal view strategies**, for every view and host. -/
theorem pubStrat_eq_viewStrat_eq (h : pubStrat P host Ok s a = pubStrat P host Ok s' a') :
    viewStrat π P host Ok s a = viewStrat π P host Ok s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubView.pubStrat_eq_viewStrat_eq h

/-! ## Injective views -/

/-- Every host factors through an injective view. -/
theorem hostView_of_injective (hπ : Function.Injective π) : HostView π host :=
  fun _ _ _ _ h => by rw [hπ h]

/-- **Through an injective view, `PubEquivV` is `PubEquiv`.** -/
theorem pubEquivV_iff_of_injective (hπ : Function.Injective π) :
    PubEquivV π P host Ok s a s' a' ↔ PubEquiv P host Ok s a s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubView.pubEquivV_iff_of_injective hπ

/-- Through the identity view, `PubEquivV` is `PubEquiv`. -/
theorem pubEquivV_id_iff :
    PubEquivV (id : Store H → Store H) P host Ok s a s' a' ↔ PubEquiv P host Ok s a s' a' :=
  pubEquivV_iff_of_injective Function.injective_id

/-- Through an injective view, the view strategies are equal iff the public strategies are. -/
theorem viewStrat_eq_iff_pubStrat_eq (hπ : Function.Injective π) :
    viewStrat π P host Ok s a = viewStrat π P host Ok s' a' ↔
      pubStrat P host Ok s a = pubStrat P host Ok s' a' :=
  ((viewStrat_eq_iff (hostView_of_injective hπ)).trans (pubEquivV_iff_of_injective hπ)).trans
    pubStrat_eq_iff.symm

/-! ## Reading back the view strategy -/

/-- **A completed view round with values** is a Core run to those values whose log is viewed as
`l` and whose final store is viewed as `o`. -/
theorem viewStrat_mem_ret (vs : List Val) (l : List (Call (viewSig H O))) (ws : List Val)
    (o : O) :
    (.inr (.ask (PUnit.unit, vs)) :: (StratObs.callMoves l ++
        [.inr (.ans (PUnit.unit, vs) (.inl (((.inl ws : List Val ⊕ Nat), o), PUnit.unit)))]) :
        List (Move (viewSig H O) (viewSigPub O))) ∈ (viewStrat π P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
        EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ ∧ cs.map (viewCall π) = l ∧
        π s₂ = o :=
  Silmaril.Proofs.Wasm.Abstract.PubView.viewStrat_mem_ret vs l ws o

/-- **A one-round infinite view play** is the view of a productive Core run. -/
theorem viewStrat_mem_inf (vs : List Val) (ω' : Nat → Call (viewSig H O)) :
    StratObs.streamPlay [] (PUnit.unit, vs) ω' ∈ (viewStrat π P host Ok s a).inf ↔
      Ok s (a, vs) ∧ ∃ ω : Nat → Call (wasmHostSig H),
        CoreInf P host (invoke s a vs) ω ∧ viewCall π ∘ ω = ω' :=
  Silmaril.Proofs.Wasm.Abstract.PubView.viewStrat_mem_inf vs ω'

end Silmaril.Wasm.Abstract
