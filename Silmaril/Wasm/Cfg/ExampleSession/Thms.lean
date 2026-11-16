module

public import Silmaril.Wasm.Cfg.ExampleSession.Defs
public import Silmaril.Wasm.Cfg.Session.Thms
import Silmaril.Proofs.Wasm.Cfg.ExampleSession

@[expose] public section

/-!
# The CFG session of a host-free instance: regression fixtures

`sesInst` has **no imports**, and its session still has **infinite plays**: an empty import
interface rules out host calls inside an activation, not infinitely many export rounds.

* `ses_hfOk`: the instance is in the host-free fragment (`Session.HFOk`) at its store: well
  formed, only Wasm functions with function types, `tExt`-checked.
* `trap_round`, `val_round`: on the CFG machine, export `0` traps (`unreachable`) keeping the
  store, and export `1` answers `7` from the exit stack.
* `trap_forever`: repeating the trap is an infinite play of the CFG session: each round resumes
  from the store the trap left. `alt_forever`: so is alternating the trap with the answer `7`
  (`StratThread.InfRounds` with trap-resume rounds).
* `trap_forever_inst`, `alt_forever_inst`: the same plays are infinite plays of the instance
  session `InstSession.instSession` (`Session.cfgSession_eq_instSession`).
-/

namespace Silmaril.Wasm.Cfg.ExampleSession

open Silmaril.Games.Abstract
open Silmaril.Wasm.Cfg.Session
open Silmaril.Wasm.Abstract.InstSession (instSession)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **The instance is in the host-free fragment.** -/
theorem ses_hfOk : HFOk sesInst sesStore := Proofs.ExampleSession.ses_hfOk

/-- **Export `0` traps on the CFG machine**, keeping the store. -/
theorem trap_round (o : GrowOracle) :
    ([], .ret (.inr ()) sesStore) ∈ cfgFinS sesInst o sesStore trapQ :=
  Proofs.ExampleSession.trap_round o

/-- **Export `1` answers `7` on the CFG machine**, keeping the store. -/
theorem val_round (o : GrowOracle) :
    ([], .ret (.inl ⟨valQ, .inl seven⟩) sesStore) ∈ cfgFinS sesInst o sesStore valQ :=
  Proofs.ExampleSession.val_round o

/-- **The CFG session traps forever**, resuming from the trap store at each round. -/
theorem trap_forever (o : GrowOracle) :
    StratSession.sroundsPlay (fun _ => trapQ) (fun _ => ([], .inr ())) ∈
      (cfgSession sesInst o sesStore).inf :=
  Proofs.ExampleSession.trap_forever o

/-- **The CFG session alternates traps and answers forever.** -/
theorem alt_forever (o : GrowOracle) :
    StratSession.sroundsPlay altQ altR ∈ (cfgSession sesInst o sesStore).inf :=
  Proofs.ExampleSession.alt_forever o

/-- The instance session traps forever. -/
theorem trap_forever_inst (o : GrowOracle) :
    StratSession.sroundsPlay (fun _ => trapQ) (fun _ => ([], .inr ())) ∈
      (instSession sesInst (profile o) sesStore).inf := by
  rw [← cfgSession_eq_instSession ses_hfOk]
  exact trap_forever o

/-- The instance session alternates traps and answers forever. -/
theorem alt_forever_inst (o : GrowOracle) :
    StratSession.sroundsPlay altQ altR ∈ (instSession sesInst (profile o) sesStore).inf := by
  rw [← cfgSession_eq_instSession ses_hfOk]
  exact alt_forever o

end Silmaril.Wasm.Cfg.ExampleSession
