module

public import Silmaril.Proofs.Wasm.Component.InstTests.Transfer
public import Silmaril.Proofs.Wasm.Component.InstTests.Det

/-!
# Component test binaries: the statements about the lowered binaries

The plays of `startsC`, `trapLC` over `core3SemI` (`Pos`, `Det`), moved to the lowered binaries
`startsComp`, `trapComp` over `Binary.coreModSemI` (`Transfer`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstTests

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests
open Silmaril.Proofs.Wasm.Component.InstSem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

theorem starts_inst_bin (P : Profile) :
    instPlay (F := sigU) startsTrace .ready ++ [askEx getV, ansEx getV v42] ∈
      startsComp.denI (Binary.coreModSemI P) := by
  rw [startsComp_denI, instPlay_eq]
  exact starts_play P

theorem starts_denX_bin (P : Profile) :
    ([.inr (.ask getV), .inr (.ans getV v42)] : List (Move sigU sigU)) ∈
      startsComp.denX (Binary.coreModSemI P) :=
  Strategy.subset_generate ⟨startsTrace, starts_inst_bin P⟩
    ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩

theorem starts_asks_bin {o : GrowOracle} {p : List (Move sigU sigUI)}
    (hp : p ∈ startsComp.denI (Binary.coreModSemI (profile o))) :
    lowerAsks p <+: startsTrace.map Sigma.fst := by
  rw [startsComp_denI] at hp
  exact starts_asks hp

theorem starts_complete_bin {o : GrowOracle} {cs : List (Σ _ : sigU.Op, Option Payload)}
    {a : InstAns Unit}
    (hp : instPlay (F := sigU) cs a ∈ startsComp.denI (Binary.coreModSemI (profile o)))
    (hc : ∀ x ∈ cs, x.2 = unitHost x.1) : cs = startsTrace ∧ a = .ready := by
  rw [startsComp_denI] at hp
  exact starts_complete hp hc

theorem starts_get_bin {o : GrowOracle} {p : List (Move sigU sigUI)}
    (hp : p ∈ startsComp.denI (Binary.coreModSemI (profile o))) {r : Option Payload}
    (hr : ansEx getV r ∈ p) : r = v42 := by
  rw [startsComp_denI] at hp
  exact starts_get hp hr

theorem trap_inst_bin (P : Profile) :
    instPlay (F := sigU) ([] : List (Σ _ : sigU.Op, Option Payload)) (.fail ()) ∈
      trapComp.denI (Binary.coreModSemI P) := by
  rw [trapComp_denI, instPlay_eq]
  exact trap_play P

theorem trap_moves_bin {o : GrowOracle} {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) :
    ∀ y ∈ p, y = askInst ∨ y = ansInst (.fail ()) ∨ y.IsO := by
  rw [trapComp_denI] at hp
  exact trap_moves hp

theorem trap_plays_bin {o : GrowOracle} {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) :
    p <+: [askInst, ansInst (.fail ())] ∨
      ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: [askInst, ansInst (.fail ())] ∧ x.IsO := by
  rw [trapComp_denI] at hp
  exact trap_plays hp

theorem trap_asks_bin {o : GrowOracle} {p : List (Move sigU sigUI)}
    (hp : p ∈ trapComp.denI (Binary.coreModSemI (profile o))) : lowerAsks p = [] := by
  have h := trap_moves_bin hp
  clear hp
  induction p with
  | nil => rfl
  | cons y p ih =>
    have ih' := ih fun z hz => h z (.tail _ hz)
    rcases h y (.head _) with rfl | rfl | hy
    · exact ih'
    · exact ih'
    · rcases y with (_ | _) | (_ | _)
      · exact hy.elim
      · exact ih'
      · exact ih'
      · exact ih'

theorem trap_denX_bin {o : GrowOracle} : trapComp.denX (Binary.coreModSemI (profile o)) = ⊥ := by
  rw [Strategy.bot_eq_generate, Comp.denX, exportPhase]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro cs h
  have hr : ansInst .ready ∈ instPlay (F := sigU) cs (InstAns.ready (R := Unit)) ++
      p.map Silmaril.Wasm.Game.liftMove := by simp [instPlay]
  rcases trap_moves_bin h _ hr with h | h | h
  · cases h
  · cases h
  · exact h

end Silmaril.Proofs.Wasm.Component.InstTests
