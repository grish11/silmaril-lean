module

public import Silmaril.Wasm.Abstract.AcceptWasm.Defs
public import Silmaril.Wasm.Abstract.Accept.Thms
public import Silmaril.Wasm.Abstract.Function.Thms
public import Silmaril.Wasm.Abstract.Instance.Thms
public import Silmaril.Games.Abstract.SigBridge.Thms

/-! # Concrete → abstract → acceptor = concrete → acceptor, for Wasm

The diagrams commute **exactly** (equalities, so both inclusions) for the abstraction maps that
exist on main:

* **Functions** (`wasmFun`, `Silmaril.Wasm.Abstract.Function`): the endings of the abstract
  function map onto the concrete behaviours (`endToBehaviour '' endRun … = behRun …`,
  `endRun_wasmFun`, from `image_wasmFun`). So for every verdict whose accepting and rejecting
  sets are behaviours (`accB`, `rejB : Set (Behaviour Val)`), the abstract verdict on the
  preimages is the concrete verdict (`retAcceptsSome_wasmFun`, `retNeverRejects_wasmFun`,
  `retAcceptsSafely_wasmFun`). Verdicts that read the final store are not of this form:
  `Behaviour` forgets the store, and no inclusion is claimed for them here.
* **Scalar instances** (`machine`, `Silmaril.Wasm.Abstract.Instance`): for observations of
  Proponent moves (import calls, export answers), the concrete strategy and the abstract machine
  accept the same values (`strategy_accepted_eq`), from `strategyIso_strategy` and
  `tmAccepted_denote`. Likewise for the runner, hence all verdicts (`strategy_tmRun_eq`).
* **Untyped (store-carrying) instances** (`uMachine`): the same, from `strategyIso_ofLTS`
  (`uStrategy_accepted_eq`).

What is **not** related here: the spec-instantiated sessions of `Silmaril.Wasm.Game.Accept`
(`Callouts`) and these instance strategies. Relating them needs the adequacy of the instance
game against `UStep` sessions (`Silmaril.Wasm.Game.Untyped` has `uAdequacy` for behaviours, not
for reachable callouts), which is not proved for callout sets.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.Accept

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Functions -/

/-- **The abstract endings map onto the concrete behaviours.** -/
theorem endRun_wasmFun (P : Profile) (host : HostSemantics H) (D : Set (Store H)) (a : Nat)
    (vs : List Val) :
    endToBehaviour '' endRun (wasmFun P host a) D vs = behRun P host D a vs := by
  ext b
  constructor
  · rintro ⟨_, ⟨s, hs, x, hx, rfl⟩, rfl⟩
    exact ⟨s, hs, (image_wasmFun P host a s vs) ▸ ⟨x, hx, rfl⟩⟩
  · rintro ⟨s, hs, hb⟩
    rw [← image_wasmFun P host a s vs] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact ⟨x.2, ⟨s, hs, x, hx, rfl⟩, rfl⟩

/-- **Export acceptance commutes**: some call returns an accepting behaviour. -/
theorem retAcceptsSome_wasmFun (P : Profile) (host : HostSemantics H) (D : Set (Store H))
    (a : Nat) (accB : Set (Behaviour Val)) :
    retAcceptsSome (wasmFun P host a) D (endToBehaviour ⁻¹' accB) =
      Silmaril.Accept.acceptsSome (behRun P host D a) accB := by
  unfold retAcceptsSome
  rw [← acceptsSome_image]
  congr 1
  funext vs
  exact endRun_wasmFun P host D a vs

/-- **Never-rejection commutes**: no call returns a rejecting behaviour. -/
theorem retNeverRejects_wasmFun (P : Profile) (host : HostSemantics H) (D : Set (Store H))
    (a : Nat) (rejB : Set (Behaviour Val)) :
    retNeverRejects (wasmFun P host a) D (endToBehaviour ⁻¹' rejB) =
      Silmaril.Accept.neverRejects (behRun P host D a) rejB := by
  unfold retNeverRejects
  rw [← neverRejects_image]
  congr 1
  funext vs
  exact endRun_wasmFun P host D a vs

/-- **The combined verdict commutes**, with one runner on each side. -/
theorem retAcceptsSafely_wasmFun (P : Profile) (host : HostSemantics H) (D : Set (Store H))
    (a : Nat) (accB rejB : Set (Behaviour Val)) :
    retAcceptsSafely (wasmFun P host a) D (endToBehaviour ⁻¹' accB) (endToBehaviour ⁻¹' rejB) =
      Silmaril.Accept.acceptsSafely (behRun P host D a) accB rejB := by
  unfold retAcceptsSafely
  rw [← acceptsSafely_image]
  exact acceptsSafely_congr (fun vs => endRun_wasmFun P host D a vs) _ _

/-! ## Instances -/

/-- A strategy and its trace model accept the same (they have the same plays). -/
theorem strategy_accepted_eq_tmAccepted {E F : Sig} {α : Type} (σ : Strategy E F)
    (obs : Move E F → Option α) :
    σ.accepted obs = tmAccepted (SigBridge.strategyIso σ) obs := rfl

/-- **Scalar instances: the concrete strategy and the abstract machine accept the same**, for
observations of Proponent moves. -/
theorem strategy_accepted_eq (I : Silmaril.Wasm.Game.ScalarInstance) (P : Profile)
    (s : Store Nat) {α : Type} (obs : Move I.E I.F → Option α)
    (hP : ∀ m a, obs m = some a → ¬ m.IsO) :
    (I.strategy P s).accepted obs = mAccepted (machine I P s) obs := by
  rw [strategy_accepted_eq_tmAccepted, strategyIso_strategy]
  exact tmAccepted_denote hP

/-- The runner too, hence every verdict. -/
theorem strategy_tmRun_eq (I : Silmaril.Wasm.Game.ScalarInstance) (P : Profile)
    (s : Store Nat) {α : Type} (val : Move I.E I.F → Option α)
    (hP : ∀ m a, val m = some a → ¬ m.IsO) (a : α) :
    tmRun (SigBridge.strategyIso (I.strategy P s)) val a =
      {m | (∃ t ∈ (machine I P s).traces ∩ (sigGame I.E I.F).Legal, m ∈ t) ∧ val m = some a} := by
  rw [strategyIso_strategy]
  exact tmRun_denote hP a

/-- **Untyped instances: the concrete strategy and the abstract machine accept the same.** -/
theorem uStrategy_accepted_eq (U : Silmaril.Wasm.Game.UInstance) (P : Profile) {α : Type}
    (obs : Move U.E U.F → Option α) (hP : ∀ m a, obs m = some a → ¬ m.IsO) :
    (U.strategy P).accepted obs = mAccepted (uMachine U P) obs := by
  rw [strategy_accepted_eq_tmAccepted]
  show tmAccepted (SigBridge.strategyIso (Strategy.ofLTS (U.lts P))) obs = _
  rw [SigBridge.strategyIso_ofLTS]
  exact tmAccepted_denote hP

end Silmaril.Wasm.Abstract.Accept
