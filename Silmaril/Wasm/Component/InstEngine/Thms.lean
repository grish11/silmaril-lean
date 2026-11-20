module

public import Silmaril.Wasm.Component.InstEngine.Defs
import Silmaril.Proofs.Wasm.Component.InstEngine.Basic
import Silmaril.Proofs.Wasm.Component.InstEngine.Core3Det
public import Silmaril.Wasm.SingleThreaded.Interface

/-!
# The engine semantics with an instantiation phase: theorems

All proved, for an arbitrary engine `E`; proofs in
`Silmaril.Proofs.Wasm.Component.InstEngine.Basic`. `[inst] ++ cs ++ [a]` stands for the play
`instPlay cs a`: `askInst`, then `ask q, ans q r` for each import call `⟨q, r⟩` of
`cs`, then `ansInst a`.

**Instantiation.** For an instance `J` (`I = some J`) whose start function is at `a`:

* `engineStrategyI_inst_ready`: if the start phase (`StartRunI`) makes the import calls `cs` and
  returns values, then `[inst] ++ cs ++ [ready]` is a play;
* `engineStrategyI_inst_fail`: if it makes the calls `cs` and traps, then
  `[inst] ++ cs ++ [fail ()]` is a play;
* `engineStrategyI_noStart`: without a start function `[inst, ready]` is a play.

**The export phase is `engineStrategy`.**

* `engineStrategyI_after_start`: after a start phase returning at store `s'`, every play of
  `engineStrategy E ⟨s', J.addrs⟩` (lifted) follows the instantiation play;
* `engineSemI_after_ready`: for a module whose instance has no start function, every play of the
  start-free `engineSem` follows `[inst, ready]` in `engineSemI`.

**The export phase exactly** (the converse; proofs in
`Silmaril.Proofs.Wasm.Component.InstEngine.Converse`). For an instance `J` whose start function
is at `a`:

* `engineStrategyI_after_start_iff`: `[inst] ++ cs ++ [ready] ++ p` (`p` lifted) is a play iff
  **some** start run with the import calls `cs` returns values at a configuration `c'` and `p`
  is a play of `engineStrategy E ⟨c'.1, J.addrs⟩`. No determinism is assumed: a
  nondeterministic engine may leave several stores, and the export phase is their union;
* `engineStrategyI_after_start_iff_of_unique`: when every such start run returns at the same
  store `s'` (hypothesis stated in full) and one exists, the plays after it are exactly those of
  `engineStrategy E ⟨s', J.addrs⟩`;
* `core3_after_start_iff`: for Core 3.0 at a **deterministic profile** `profile o` the
  uniqueness holds (`core3_startRunI_unique`, from the uniqueness of normal forms), so after the
  instantiation play of a start run returning at `c'` the plays are exactly those of
  `engineStrategy (core3P (profile o)) ⟨c'.1, J.addrs⟩`;
* `engineStrategyI_after_noStart_iff`: without a start function, a successful instantiation makes
  no import call and is followed exactly by the plays of `engineStrategy E J.toE`;
* `engineStrategyI_noInst_not_ready`: without an instance, instantiation never succeeds.

What is not observed: a start function that diverges, or a start thread that is stuck, has no
`ready` and no `fail` (no move); these theorems are about plays that reached `ready`.
-/

public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Game (liftMove)

variable {E : Engine} {I : Option (IInstance E)} {imps exps : CoreIface}

/-- **A start phase returning values: instantiation succeeds**, its import calls as moves. -/
theorem engineStrategyI_inst_ready {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c') {ys : List Flat}
    (hf : E.status c'.1 c'.2 = .returned (.values ys)) :
    instPlay (F := sigN exps.length) cs .ready ∈ engineStrategyI E I imps exps := by
  rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
  exact Silmaril.Proofs.Wasm.Component.InstEngine.engine_inst_ready hI ha hr hf

/-- **A start phase trapping: instantiation fails**, its import calls as moves. -/
theorem engineStrategyI_inst_fail {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c')
    (hf : E.status c'.1 c'.2 = .returned .trap) :
    instPlay (F := sigN exps.length) cs (.fail ()) ∈ engineStrategyI E I imps exps := by
  rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
  exact Silmaril.Proofs.Wasm.Component.InstEngine.engine_inst_fail hI ha hr hf

/-- **Without a start function the instance is ready at once.** -/
theorem engineStrategyI_noStart {J : IInstance E} (hI : I = some J) (ha : J.start = none) :
    [askInst, ansInst .ready] ∈ engineStrategyI E I imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engine_noStart_ready hI ha

/-- **After a successful start phase, the exports are served as `engineStrategy` serves them
from the store the start function left.** -/
theorem engineStrategyI_after_start {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c') {ys : List Flat}
    (hf : E.status c'.1 c'.2 = .returned (.values ys))
    {p : List (Move (sigN imps.length) (sigN exps.length))}
    (hp : p ∈ engineStrategy E ⟨c'.1, J.addrs⟩ imps exps) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈
      engineStrategyI E I imps exps := by
  rw [Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq]
  exact Silmaril.Proofs.Wasm.Component.InstEngine.engine_after_start hI ha hr hf hp

/-- **On start-free modules `engineSemI` extends `engineSem`**: after `[inst, ready]`, every play
of the start-free engine semantics is a play. -/
theorem engineSemI_after_ready {M : Type} [CoreModule M] {emb : M → E.Module} {m : M}
    {J : IInstance E}
    (h : instOfI E (emb m) (CoreModule.imports m) (CoreModule.exports m) = some J)
    (hs : J.start = none) {p : List (Move (sigN (CoreModule.imports m).length)
      (sigN (CoreModule.exports m).length))} (hp : p ∈ (engineSem E M emb).sem m) :
    askInst :: ansInst .ready :: p.map liftMove ∈ (engineSemI E M emb).sem m :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engineSem_le_after h hs hp

/-! ## The export phase exactly -/

/-- **After a successful start phase, exactly the plays of `engineStrategy`** from a store some
start run with the same import calls returns at. -/
theorem engineStrategyI_after_start_iff {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈ engineStrategyI E I imps exps ↔
      ∃ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (J.store, E.invoke a []) cs c' ∧
        E.status c'.1 c'.2 = .returned (.values ys) ∧
        p ∈ engineStrategy E ⟨c'.1, J.addrs⟩ imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engine_after_start_iff hI ha cs p

/-- **The export phase from a unique post-start store**: if every start run with the calls `cs`
that returns values returns at the store `s'`, and one does, the plays after
`[inst] ++ cs ++ [ready]` are exactly those of `engineStrategy` from `s'`. -/
theorem engineStrategyI_after_start_iff_of_unique {J : IInstance E} {a : E.FuncAddr}
    (hI : I = some J) (ha : J.start = some a)
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)} {s' : E.Store Nat}
    (hu : ∀ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (J.store, E.invoke a []) cs c' →
      E.status c'.1 c'.2 = .returned (.values ys) → c'.1 = s')
    (hex : ∃ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (J.store, E.invoke a []) cs c' ∧
      E.status c'.1 c'.2 = .returned (.values ys))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈ engineStrategyI E I imps exps ↔
      p ∈ engineStrategy E ⟨s', J.addrs⟩ imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engine_after_start_iff_of_unique hI ha hu hex p

/-- **Without a start function, a successful instantiation is `[inst, ready]`**, followed
exactly by the plays of `engineStrategy`. -/
theorem engineStrategyI_after_noStart_iff {J : IInstance E} (hI : I = some J)
    (ha : J.start = none) (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈ engineStrategyI E I imps exps ↔
      cs = [] ∧ p ∈ engineStrategy E J.toE imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engine_after_noStart_iff hI ha cs p

/-- **Without an instance, instantiation never succeeds.** -/
theorem engineStrategyI_noInst_not_ready (hI : I = none)
    (cs : List (Σ _ : (sigN imps.length).Op, Option Payload))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∉ engineStrategyI E I imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.engine_noInst_not_ready hI cs p

section Core3

open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle}

/-- **Core 3.0 start runs are determined by their import calls** at a deterministic profile:
two start runs from the same configuration with the same calls and answers that both return
end at the same configuration. -/
theorem core3_startRunI_unique {imps : CoreIface} {c c₁ c₂ : (core3P (profile o)).Config Nat}
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    (h₁ : StartRunI (core3P (profile o)) imps c cs c₁)
    (h₂ : StartRunI (core3P (profile o)) imps c cs c₂)
    (hf₁ : ∃ r, (core3P (profile o)).status c₁.1 c₁.2 = .returned r)
    (hf₂ : ∃ r, (core3P (profile o)).status c₂.1 c₂.2 = .returned r) : c₁ = c₂ :=
  Silmaril.Proofs.Wasm.Component.InstEngine.startRunI_unique h₁ h₂ hf₁ hf₂

/-- **The export phase of a Core 3.0 instance after its start function**, at a deterministic
profile: after the instantiation play of a start run with calls `cs` returning at `c'`, the plays
are exactly those of `engineStrategy` from `c'.1`. -/
theorem core3_after_start_iff {I : Option (IInstance (core3P (profile o)))}
    {J : IInstance (core3P (profile o))} {a : Nat} (hI : I = some J) (ha : J.start = some a)
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : (core3P (profile o)).Config Nat}
    (hr : StartRunI (core3P (profile o)) imps (J.store, (core3P (profile o)).invoke a []) cs c')
    {ys : List Flat} (hf : (core3P (profile o)).status c'.1 c'.2 = .returned (.values ys))
    (p : List (Move (sigN imps.length) (sigN exps.length))) :
    instPlay (F := sigN exps.length) cs .ready ++ p.map liftMove ∈
        engineStrategyI (core3P (profile o)) I imps exps ↔
      p ∈ engineStrategy (core3P (profile o)) ⟨c'.1, J.addrs⟩ imps exps :=
  Silmaril.Proofs.Wasm.Component.InstEngine.core3_after_start_iff hI ha hr hf p

end Core3

end Silmaril.Wasm.Component.Param
