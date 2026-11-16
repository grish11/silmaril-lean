module

public import Silmaril.Sim.Reduce.Toy.Defs
public import Silmaril.Sim.Reduce.Thms

/-!
# The toy reduction problem: composition

`isa_of_pieces`: for any sound simulator `K` of `Open9.isa` into which every entry state can be
loaded, the three per-function Wasm pieces (`piece K Init g`, each about one function with its
callees assumed) solve the three ISA problems. `decomp` is the same as a `Decomp` value. PROVED;
the pieces, `K`'s soundness and `Encodes` are the open leaves of the problem DAG
(`examples/wasm-sim/reduce/toy/out/dag.json`).
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Toy

open Silmaril.X86 (MState)
open Silmaril.Machine.X86 (Open9.isa)

theorem ranked : Ranked callees rank := by
  intro i j hj
  cases i <;> simp [callees] at hj
  rcases hj with rfl | rfl <;> decide

variable {W : Type}

/-- **The toy's composition theorem.** -/
theorem isa_of_pieces (K : SoundSim MState W) (hstep : K.step = Open9.isa.step)
    (Init : W → Prop) (henc : ∀ g base, Encodes K Init (specPre Open9.isa (spec g base)))
    (h : ∀ g, piece K Init g) : ∀ g, isaGoal g := fun g base =>
  (specReduction Open9.isa (spec g base) K hstep Init (henc g base)).sound
    (ag_compose ranked h g base)

/-- The toy as a decomposition: goal `∀ g, isaGoal g`, three pieces. -/
def decomp (K : SoundSim MState W) (hstep : K.step = Open9.isa.step) (Init : W → Prop)
    (henc : ∀ g base, Encodes K Init (specPre Open9.isa (spec g base))) : Decomp where
  goal := ∀ g, isaGoal g
  pieces := [piece K Init .sumTo, piece K Init .dbl, piece K Init .f]
  compose hp := isa_of_pieces K hstep Init henc fun g => by
    cases g
    · exact hp _ (by simp)
    · exact hp _ (by simp)
    · exact hp _ (by simp)

end Silmaril.Sim.Reduce.Toy

/-- info: 'Silmaril.Sim.Reduce.Toy.isa_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.Reduce.Toy.isa_of_pieces
