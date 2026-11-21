module

public import Silmaril.Proofs.Wasm.Component.InstEngine.Converse
public import Silmaril.Proofs.Wasm.Component.Core3G.Lawful
public import Silmaril.Wasm.Game.Machine.Thms

/-!
# Start runs of Core 3.0 at a deterministic profile

At a deterministic profile `profile o`, host-free Core 3.0 runs reach at most one normal form
(`Silmaril.Wasm.Game.reach_normal_unique`); callouts and returned threads are normal forms. So a
start run (`StartRunI`) is determined by the import calls and the answers it receives
(`startRunI_unique`), and the export phase after `[inst] ++ cs ++ [ready]` is `engineStrategy`
from the one store that run returns at (`core3_after_start_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstEngine

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game (liftMove)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

variable {o : GrowOracle}

/-- A Core 3.0 configuration at a callout or returned has no internal step. -/
theorem core3_noStep {P : Silmaril.Wasm.Numerics.Profile}
    {c : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
    (h : (∃ hc args, (core3P P).status c.1 c.2 = .callout hc args) ∨
      ∃ r, (core3P P).status c.1 c.2 = .returned r) :
    ∀ y, ¬ Silmaril.Wasm.Game.InternalP P c y := by
  rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, hst⟩ := Silmaril.Proofs.Wasm.Component.Core3G.flatStatus_eq_callout h
    exact Silmaril.Proofs.Wasm.Component.Core3G.statusP_callout_no_step hst
  · rcases Silmaril.Proofs.Wasm.Component.Core3G.flatStatus_eq_returned h with ⟨_, hst⟩ | hst
    · exact Silmaril.Proofs.Wasm.Component.Core3G.statusP_returned_no_step hst
    · exact Silmaril.Proofs.Wasm.Component.Core3G.statusP_returned_no_step hst

/-- **Start runs are determined by their import calls**, at a deterministic profile: two start
runs from the same configuration with the same calls (and answers) that both return end at the
same configuration. -/
theorem startRunI_unique {imps : CoreIface} :
    ∀ {c c₁ c₂ : (core3P (profile o)).Config Nat}
      {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)},
    StartRunI (core3P (profile o)) imps c cs c₁ → StartRunI (core3P (profile o)) imps c cs c₂ →
    (∃ r, (core3P (profile o)).status c₁.1 c₁.2 = .returned r) →
    (∃ r, (core3P (profile o)).status c₂.1 c₂.2 = .returned r) → c₁ = c₂
  | _, _, _, _, .nil run₁, h₂, hf₁, hf₂ => by
    cases h₂ with
    | nil run₂ =>
      exact Silmaril.Wasm.Game.reach_normal_unique run₁ run₂ (core3_noStep (.inr hf₁))
        (core3_noStep (.inr hf₂))
  | _, _, _, _, .call run₁ callout₁ _ _ rest₁, h₂, hf₁, hf₂ => by
    cases h₂ with
    | call run₂ callout₂ _ _ rest₂ =>
      have he := Silmaril.Wasm.Game.reach_normal_unique run₁ run₂
        (core3_noStep (.inl ⟨_, _, callout₁⟩)) (core3_noStep (.inl ⟨_, _, callout₂⟩))
      cases he
      exact startRunI_unique rest₁ rest₂ hf₁ hf₂

/-- **The export phase of a Core 3.0 instance after its start function**, at a deterministic
profile: after `[inst] ++ cs ++ [ready]`, exactly the plays of `engineStrategy` from the store
the start run with the calls `cs` returns at. -/
theorem core3_after_start_iff {imps exps : CoreIface}
    {I : Option (IInstance (core3P (profile o)))} {J : IInstance (core3P (profile o))}
    {a : Nat} (hI : I = some J) (ha : J.start = some a)
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : (core3P (profile o)).Config Nat}
    (hr : StartRunI (core3P (profile o)) imps (J.store, (core3P (profile o)).invoke a []) cs c')
    {ys : List Flat} (hf : (core3P (profile o)).status c'.1 c'.2 = .returned (.values ys))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈
        engineStrategyI (core3P (profile o)) I imps exps ↔
      p ∈ engineStrategy (core3P (profile o)) ⟨c'.1, J.addrs⟩ imps exps :=
  engine_after_start_iff_of_unique hI ha
    (fun _ _ hr' hf' => by rw [startRunI_unique hr' hr ⟨_, hf'⟩ ⟨_, hf⟩])
    ⟨c', ys, hr, hf⟩ p

end Silmaril.Proofs.Wasm.Component.InstEngine
