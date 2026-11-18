module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Defs
public import Silmaril.Games.Abstract.StratLegal.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Host
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# The session triples of a linked component with host imports: basic facts

* both triples have no plain traps (every trap keeps the state);
* both are admissible (saturated) on the legal host interface;
* every reference session observation under a typed host is a specification session whose host
  calls are a realizable history.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

variable {P : Profile} {l : HLinked2} {Ie Ii : ScalarInstance}

theorem noPlainTrap_compTripleS : StratSession.NoPlainTrap (HLinked2.compTripleS P l Ie Ii) := by
  intro s q c hm
  change (c.map StratLegal.liftCall, End.trap) ∈ HLinked2.compFin P l Ie Ii s q at hm
  simp only [HLinked2.compFin] at hm
  split at hm
  · simp at hm
  · rcases hm with ⟨_, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he

theorem admissible_compTripleS : Admissible (HLinked2.compTripleS P l Ie Ii) :=
  StratLegal.restrict_admissible admissible_sat

theorem noPlainTrap_compTripleO : StratSession.NoPlainTrap (HLinked2.compTripleO P l Ie Ii) := by
  intro s q c hm
  change (c.map StratLegal.liftCall, End.trap) ∈ HLinked2.compFinO P l Ie Ii s q at hm
  simp only [HLinked2.compFinO] at hm
  split at hm
  · simp at hm
  · rcases hm with ⟨_, _, _, _, he⟩ | ⟨_, he⟩ <;> cases he

theorem admissible_compTripleO : Admissible (HLinked2.compTripleO P l Ie Ii) :=
  StratLegal.restrict_admissible admissible_sat

/-- Every reference session observation under a typed host is a specification session whose
host calls are a realizable history. -/
theorem sessObs_realizable (P : Profile) (prof : ProfileKind) (hl : l.Adequate) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (hT : l.HostTyped g) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    {o : List (Option (List RVal))} {st' : σ × List HLinked2.HostEvent}
    (ho : (o, st') ∈ HLinked2.sessObs P prof l g s₀ calls) :
    ∃ (Ie Ii : ScalarInstance) (outs : List (Option (List IVal)))
      (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload)))
      (u' π' : Silmaril.Wasm.Execution.Core.Store Nat),
      l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
      HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π' ∧
      HostRun (HLinked2.logG g) (s₀, []) hs.flatten st' ∧ o = refOuts outs ∧
      ∃ R', HLinked2.RealRun l.host [] hs.flatten R' := by
  obtain ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hS, hr, rfl⟩ :=
    HLinked2.sess_refToSpec P prof hl g hT s₀ calls ht ho
  exact ⟨Ie, Ii, outs, hs, u', π', hIe, hIi, hS, hr, rfl,
    realRun_of_hostRun _ (Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.HostTyped.logG hT)
      hr⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
