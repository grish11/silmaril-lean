module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Closed

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params carried results : List (Ty Data)} {n : Nat}
variable {g : Graph P params results n 1} {m : Interpretation.{u,v,w} P}

theorem Accepted.demandWellFounded (a : Accepted g carried) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.rank a.ranked

/-- A successful run certifies the least pass and its ordered readouts,
including when the pass count is absent from the returned tuple. -/
theorem Accepted.firstExit_and_observe_of_exec (a : Accepted g carried) (laws : a.Laws m)
    (input : Tuple m.Value params) (idx : Index 1) {output : Tuple m.Value results}
    (ran : Exec m a.revert input (some output)) :
    (∃ k, a.FirstExit m (g.denote m input a.demandWellFounded) idx k) ∧
      g.observe m (g.denote m input a.demandWellFounded) idx = output.map (fun _ => some) :=
  Proofs.firstExit_and_observe_of_exec a laws (g.denote_solves m input a.demandWellFounded) idx ran

/-- Every finite successful emitted run gives the original ordered
observation. The trace identifies one least pass count, and every eval
uses the same exit and the defined prefix of its carried slot. -/
theorem Accepted.observe_of_exec (a : Accepted g carried) (laws : a.Laws m) (input : Tuple m.Value params) (idx : Index 1)
    {output : Tuple m.Value results} (ran : Exec m a.revert input (some output)) :
    g.observe m (g.denote m input a.demandWellFounded) idx = output.map (fun _ => some) :=
  (a.firstExit_and_observe_of_exec laws input idx ran).2

theorem Accepted.exec_of_runFuel (a : Accepted g carried) (fuel : Nat) (input : Tuple m.Value params)
    {output : Tuple m.Value results} (ran : a.runFuel m fuel input = some output) :
    Exec m a.revert input (some output) :=
  Proofs.exec_of_runFuel a fuel ran

/-- Total primitives suffice for all four primitive-only schedules. -/
theorem Accepted.total_of_primitives (a : Accepted g carried)
    (total : ∀ {ins out} (op : P ins out) args, ∃ val, m.run op args = some val) : a.Total m :=
  Proofs.total_of_primitives a total

/-- The shared first pass alone gives a successful bounded run when
the full scheduled slices are total, including unobserved carried slots. -/
theorem Accepted.runFuel_exists_of_firstExit (a : Accepted g carried) (laws : a.Laws m)
    (total : a.Total m) (input : Tuple m.Value params) (idx : Index 1) (k : Nat)
    (pass : a.FirstExit m (g.denote m input a.demandWellFounded) idx k) :
    ∃ output, a.runFuel m k input = some output :=
  Proofs.runFuel_exists_of_firstExit a laws total
    (g.denote_solves m input a.demandWellFounded) idx k pass

/-- Run the emitted code with fuel equal to the PEG first exit. The
observed tuple fixes the return, including its order and repetitions. -/
theorem Accepted.runFuel_of_firstExit (a : Accepted g carried) (laws : a.Laws m)
    (total : a.Total m) (input : Tuple m.Value params) (idx : Index 1) (k : Nat)
    {output : Tuple m.Value results}
    (pass : a.FirstExit m (g.denote m input a.demandWellFounded) idx k)
    (observed : g.observe m (g.denote m input a.demandWellFounded) idx = output.map (fun _ => some)) :
    a.runFuel m k input = some output :=
  Proofs.runFuel_of_firstExit a laws total
    (g.denote_solves m input a.demandWellFounded) idx k pass observed

/-- Ordered finite return correspondence at a defined shared first exit.
Only the PEG-to-SIMPLE direction uses the slice totality premises. -/
theorem Accepted.exec_iff_firstExit (a : Accepted g carried) (laws : a.Laws m)
    (total : a.Total m) (input : Tuple m.Value params) (idx : Index 1)
    (output : Tuple m.Value results) :
    Exec m a.revert input (some output) ↔
      (∃ k, a.FirstExit m (g.denote m input a.demandWellFounded) idx k) ∧
      g.observe m (g.denote m input a.demandWellFounded) idx = output.map (fun _ => some) :=
  ⟨Proofs.firstExit_and_observe_of_exec a laws (g.denote_solves m input a.demandWellFounded) idx,
    fun ⟨⟨k, pass⟩, observed⟩ =>
      a.exec_of_runFuel k input (a.runFuel_of_firstExit laws total input idx k pass observed)⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed
