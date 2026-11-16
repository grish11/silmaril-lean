module

public import Silmaril.Proofs.Wasm.Abstract.NodeTrap.Basic
public import Silmaril.Proofs.Wasm.Abstract.NodeTrap.Relay
public import Silmaril.Wasm.Abstract.InstSessionD.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Games.Abstract.SessionTrap.Thms
public import Silmaril.Wasm.Component.OutOfRange.Defs

/-!
# Core 3.0 nodes propagate traps (proofs)

The strategy of a core node `Node.denD (core3SemD P) e (.core m args)` is, at the level of finite
plays, the instance strategy `m.inst.strategy P m.inst.store` between four one-shot handlers:
`implsN` and `importH` below, `exportH` and `widenH` above.

* The instance strategy ends its round at an import trap (`endsBelow_strategy`), from
  `instTripleS_trapAbortsRound` through the session `instSession` (`threadS_trapAbortsBelow`)
  and its relabelling (`map_srelabel_mem`).
* `importH` relays the IR trap `none` as the import trap `Answer.trap` (`payloadAnswer`), and
  `implsN` relays `none` as `none` (`oneShot_runChain`: a chain of adapters calls its target at
  most once, and `Option.bind` keeps `none`). `exportH` and `widenH` are one-shot.
* `endsBelow_comp_lower`/`endsBelow_comp_upper` carry the property through the four layers.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeTrap

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionTrap
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Abstract.InstSession
open Silmaril.Wasm.Abstract.NodeTrap
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

/-! ## The instance strategy -/

/-- **The instance strategy ends its round at an import trap.** -/
theorem endsBelow_strategy (I : ScalarInstance) (P : Profile) (s : Store Nat) :
    EndsBelow IsTrapA (I.strategy P s) := by
  intro p m n y hT hp
  have h := (map_srelabel_mem (I := I) (P := P) (s := s)).2 hp
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  obtain ⟨a, hy⟩ := threadS_trapAbortsBelow instTripleS_trapAbortsRound s _ m n _ hT h
  rcases y with e | g
  · simp [srelabel] at hy
  · exact ⟨g, rfl⟩

/-! ## The handlers -/

theorem oneShot_importH (m : NumInstance) :
    OneShot (fun _ r => r = none) IsTrapA (importH m) := fun _ =>
  Or.inr ⟨_, _, rfl, fun n => ⟨_, rfl, fun hn => by subst hn; rfl⟩⟩

theorem oneShot_exportH (m : NumInstance) :
    OneShot (fun _ _ => True) (fun _ _ => True) (exportH m) := by
  intro q
  unfold exportH
  dsimp only
  split
  · split
    · exact Or.inr ⟨_, _, rfl, fun _ => ⟨_, rfl, fun _ => trivial⟩⟩
    · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

theorem oneShot_widenH (n : Nat) :
    OneShot (fun _ _ => True) (fun _ _ => True) (widenH n) := by
  intro q
  unfold widenH
  split
  · exact Or.inr ⟨_, _, rfl, fun _ => ⟨_, rfl, fun _ => trivial⟩⟩
  · exact Or.inl ⟨_, rfl⟩

/-- The shape of a one-shot program on `sigU` keeping `none`. -/
def ShotU (x : Prog sigU (Option Payload)) : Prop :=
  (∃ r, x = .pure r) ∨
    ∃ m k, x = .call m k ∧ ∀ n, ∃ r, k n = .pure r ∧ (n = none → r = none)

theorem shotU_target (e : Nat) (t : Target) (a : Payload) : ShotU (t.prog e a) := by
  cases t with
  | call r =>
    by_cases h : r < e
    · rw [Target.prog, ite_eq_left h]
      exact Or.inr ⟨_, _, rfl, fun n => ⟨n, rfl, id⟩⟩
    · rw [Target.prog, ite_eq_right h]
      exact Or.inl ⟨_, rfl⟩
  | const res => exact Or.inl ⟨_, rfl⟩

/-- **A chain of adapters calls its target at most once**, and keeps a trap. -/
theorem oneShot_runChain (c : List Adapter) (k : Payload → Prog sigU (Option Payload))
    (hk : ∀ a, ShotU (k a)) (a : Payload) : ShotU (runChain c k a) := by
  induction c generalizing a with
  | nil => exact hk a
  | cons ad c ih =>
    unfold runChain
    split
    · exact Or.inl ⟨_, rfl⟩
    · rename_i a' _
      rcases ih a' with ⟨r, hr⟩ | ⟨m, κ, hm, hκ⟩
      · rw [hr]
        exact Or.inl ⟨_, rfl⟩
      · rw [hm]
        refine Or.inr ⟨m, _, rfl, fun n => ?_⟩
        obtain ⟨r, hr, hn⟩ := hκ n
        refine ⟨r.bind ad.up, by rw [hr]; rfl, fun h => ?_⟩
        rw [hn h]
        rfl

theorem oneShot_implsN (e : Nat) (ims : List Impl) (t : Nat) :
    OneShot (fun _ r => r = none) (fun _ r => r = none) (implsN e ims t) := by
  intro q
  have h : ShotU (implsN e ims t q) := by
    unfold implsN implsH
    split
    · exact oneShot_runChain _ _ (shotU_target e _) _
    · exact Or.inl ⟨_, rfl⟩
  exact h

/-! ## The node -/

/-- **A Core 3.0 core node propagates traps**, at the level of its finite plays. -/
theorem endsBelow_core3SemD (P : Profile) (e : Nat) (m : NumInstance) (args : List Impl) :
    EndsBelow (fun _ r => r = none) (Node.denD (core3SemD P) e (.core m args)).toStrategy := by
  simp only [Node.denD]
  show EndsBelow _ ((Strategy.ofHandler (implsN e args m.imports.length)).comp
    (((Strategy.ofHandler (importH m)).comp
      ((spullD (instSession m.inst P m.inst.store)).toStrategy.comp
        (Strategy.ofHandler (exportH m)))).comp (Strategy.ofHandler (widenH m.exports.length))))
  rw [toStrategy_spullD_instSession]
  refine endsBelow_comp_lower (relays_ofHandler (oneShot_implsN _ _ _)) ?_
  refine endsBelow_comp_upper ?_ (relays_ofHandler (oneShot_widenH _))
  refine endsBelow_comp_lower (relays_ofHandler (oneShot_importH m)) ?_
  exact endsBelow_comp_upper (endsBelow_strategy _ _ _) (relays_ofHandler (oneShot_exportH m))

theorem trapPropagating_core3SemD (P : Profile) (e : Nat) (m : NumInstance)
    (args : List Impl) : TrapPropagating (Node.denD (core3SemD P) e (.core m args)) :=
  fun s q y hp => endsBelow_core3SemD P e m args s q none y rfl hp

end Silmaril.Proofs.Wasm.Abstract.NodeTrap
