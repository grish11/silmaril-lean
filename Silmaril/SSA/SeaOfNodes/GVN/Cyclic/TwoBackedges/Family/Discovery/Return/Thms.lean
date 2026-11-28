module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return

open Diamond (ValueSort)
open FixedPoint (Refines)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open TwoBackedges (redirect)

variable {regs : List (ValueSort Unit)}
variable (p : Program Opcode regs word)

theorem returnedLane?_eq_none_iff : returnedLane? p = none ↔ returnOrigin p ≠ .arg p.result :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.returned_none p

theorem returnedLane?_sound {original : Lane regs} (found : returnedLane? p = some original) :
    slot original = p.result ∧ returnOrigin p = .arg (slot original) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.returned_some p found

theorem returnedLane?_reads {original : Lane regs} (found : returnedLane? p = some original)
    (old : Bank (regs := regs) model) : (p.header.eval model old).get p.result = old.get (slot original) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.returned_reads p found old

/-- Choose the least original register index in the same class whose
completed-header read has the actual return key. -/
theorem best_is_least (classes : Classes regs) {original : Lane regs} (found : returnedLane? p = some original) :
    Eligible p classes original (best p classes original) ∧
      ∀ candidate, Eligible p classes original candidate →
        (slot (best p classes original)).index ≤ (slot candidate).index := by
  have chosen := Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.best_spec p classes
    (returnedLane?_sound p found).1
  exact ⟨chosen.1, fun _ fits =>
    Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.slot_index_order.monotone (chosen.2 _ fits)⟩

/-- Coarseness preserves any distinct structural partner of the returned lane. -/
theorem class_nontrivial_of_stable_pair {candidate : Classes regs} {original other : Lane regs}
    (found : returnedLane? p = some original) (stable : Stable p candidate)
    (entry : Refines candidate (initial p)) (paired : candidate original = candidate other)
    (distinct : slot other ≠ p.result) :
    ∃ peer : Lane regs, slot peer ≠ slot original ∧ normalize p original = normalize p peer :=
  ⟨other, (returnedLane?_sound p found).1.symm ▸ distinct, normalize_coarsest p stable entry _ _ paired⟩

theorem best_rewrite {original : Lane regs} (found : returnedLane? p = some original) :
    Discovery.rewrite? p (slot (best p (normalize p) original)) =
      some (redirect p (slot (best p (normalize p) original))) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.best_rewrite p found

theorem optimize_of_carried {original : Lane regs} (found : returnedLane? p = some original) :
    optimize p = redirect p (slot (best p (normalize p) original)) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.optimize_carried p found

theorem optimize_of_noncarried (produced : returnOrigin p ≠ .arg p.result) : optimize p = p := by
  simp only [optimize, (returnedLane?_eq_none_iff p).mpr produced]

/-- A carried return stays unchanged exactly when it is already the
first exit-compatible member of its class. -/
theorem optimize_eq_iff_canonical {original : Lane regs} (found : returnedLane? p = some original) :
    optimize p = p ↔ ∀ candidate, Eligible p (normalize p) original candidate → original ≤ candidate :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.optimize_canonical p found

theorem optimize_of_singleton {original : Lane regs} (found : returnedLane? p = some original)
    (alone : ∀ candidate, normalize p original = normalize p candidate → candidate = original) :
    optimize p = p :=
  (optimize_eq_iff_canonical p found).mpr (fun candidate fits => le_of_eq (alone candidate fits.1).symm)

/-- Preserve the actual selected feedback occurrence and its full bank, or the returned word. -/
theorem optimize_step_of_arrives {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : (optimize p).step model old = p.step model old :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.optimize_step p arrived

/-- Both programs reach exactly the same labelled header arrivals with the same complete packets. -/
theorem optimize_arrives_iff (input old : Bank (regs := regs) model) (via : Incoming) (count : Nat) :
    (optimize p).Arrives model input via count old ↔ p.Arrives model input via count old :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.optimize_arrives p input old via count

theorem optimize_run_eq (fuel : Nat) (input : Bank (regs := regs) model) :
    (optimize p).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.optimize_run p fuel input

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return
