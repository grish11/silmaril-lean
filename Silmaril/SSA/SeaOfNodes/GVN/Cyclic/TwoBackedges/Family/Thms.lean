module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family

open Diamond (ValueSort dataPorts)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)
open TwoBackedges (Invariant WordSlot redirect redirect_step_eq)

variable {regs : List (ValueSort Unit)}
variable {p target : Program Opcode regs word} {equations : Equations regs} {replacement : WordSlot regs}

/-- Every nominated pair has the same key in the common seed, including overlapping pairs. -/
theorem seed_matches (equations : Equations regs) : matchesAll equations (seed equations) = true :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.seed_matches equations

/-- A family seed preserves an interpretation of its original argument leaves
whenever that interpretation already satisfies every nominated equality. -/
theorem seed_interprets {A : Type*} (equations : Equations regs)
    (interpret : WordNumber.Key (dataPorts regs) → A) (values : WordSlot regs → A)
    (arguments : ∀ port : WordSlot regs, interpret (.argument port) = values port)
    (holds : ∀ eq ∈ equations, values eq.representative = values eq.member) :
    ∀ port : WordSlot regs, interpret ((seed equations).get port) = values port :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.seed_interprets equations interpret values arguments holds

theorem certify?_isSome_iff :
    (certify? p equations replacement).isSome = true ↔
      entryMatches p equations = true ∧ feedbackMatches p equations true = true ∧
        feedbackMatches p equations false = true ∧ exitMatches p equations replacement = true := by
  rw [← check_eq_true_iff]
  by_cases accepted : check p equations replacement = true <;> simp [certify?, accepted]

theorem rewrite?_eq_some_iff :
    rewrite? p equations replacement = some target ↔
      (certify? p equations replacement).isSome = true ∧ target = redirect p replacement := by
  cases fit : certify? p equations replacement <;> simp [rewrite?, fit, eq_comm]

/-- The checked family establishes one inductive invariant over the whole native bank. -/
theorem Certificate.invariant (cert : Certificate p equations replacement) : Invariant p (Holds equations) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.certificate_invariant cert

theorem Certificate.arrives (cert : Certificate p equations replacement)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : Holds equations old :=
  cert.invariant.arrives arrived

theorem Certificate.observes (cert : Certificate p equations replacement)
    (old : Bank (regs := regs) model) (assumes : Holds equations old) :
    (p.header.eval model old).get p.result = (p.header.eval model old).get replacement :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.certificate_observes cert old assumes

/-- The full native step agrees, including the selected edge and every field of its feedback bank. -/
theorem rewrite_step_eq (accepted : rewrite? p equations replacement = some target)
    {old : Bank (regs := regs) model} (assumes : Holds equations old) :
    target.step model old = p.step model old := by
  obtain ⟨cert, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact redirect_step_eq (cert.observes old assumes)

theorem rewrite_step_of_arrives (accepted : rewrite? p equations replacement = some target)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) :
    target.step model old = p.step model old := by
  obtain ⟨cert, _, _⟩ := Option.map_eq_some_iff.mp accepted
  exact rewrite_step_eq accepted (cert.arrives arrived)

/-- The rewritten source agrees at every common block budget, starting from the original typed entry bank. -/
theorem rewrite_run_eq (accepted : rewrite? p equations replacement = some target)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input := by
  obtain ⟨cert, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact cert.invariant.redirect_run_eq cert.observes fuel input

theorem rewrite_returns_iff (accepted : rewrite? p equations replacement = some target)
    (input : Bank (regs := regs) model) (bits : BitVec 64) :
    (∃ fuel, target.source.runFrom model fuel 0 input = some bits) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some bits := by
  simp only [rewrite_run_eq accepted]

theorem rewrite_absence_iff (accepted : rewrite? p equations replacement = some target)
    (input : Bank (regs := regs) model) :
    (∀ fuel, target.source.runFrom model fuel 0 input = none) ↔
      ∀ fuel, p.source.runFrom model fuel 0 input = none := by
  simp only [rewrite_run_eq accepted]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
