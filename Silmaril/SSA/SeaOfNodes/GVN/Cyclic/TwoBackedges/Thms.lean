module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges

open Diamond (ValueSort)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)

variable {regs : List (ValueSort Unit)}
variable {p target : Program Opcode regs word} {representative member replacement : WordSlot regs}

/-- Check both feedback occurrences independently, including the false arm. -/
theorem check_eq_true_iff :
    check p representative member replacement = true ↔
      entryMatches p representative member = true ∧
      feedbackMatches p representative member true = true ∧
      feedbackMatches p representative member false = true ∧
      exitMatches p representative member replacement = true := by
  simp only [check, Bool.and_eq_true, and_assoc]

theorem rewrite?_eq_some_iff :
    rewrite? p representative member replacement = some target ↔
      check p representative member replacement = true ∧ target = {p with result := replacement} := by
  refine ⟨Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.rewrite_exact, ?_⟩
  rintro ⟨accepted, rfl⟩
  simp only [rewrite?, accepted, ite_true]

/-- The independent preheader computations establish the carried equality on entry. -/
theorem entry_eq (accepted : entryMatches p representative member = true)
    (input : Bank (regs := regs) model) :
    (p.preheader.eval model input).get representative = (p.preheader.eval model input).get member :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.entry_eq accepted input

/-- A checked occurrence preserves the equality across its actual ordered header and feedback assignments. -/
theorem feedback_eq (side : Bool) (accepted : feedbackMatches p representative member side = true)
    {old : Bank (regs := regs) model} (same : old.get representative = old.get member) :
    ((p.feedback side).eval model (p.header.eval model old)).get representative =
      ((p.feedback side).eval model (p.header.eval model old)).get member :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.feedback_eq side accepted same

/-- At every actual header arrival, the two nominated carried slots agree. -/
theorem arrives_eq (accepted : check p representative member replacement = true)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) :
    old.get representative = old.get member :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.arrives_eq accepted arrived

/-- Keep the selected occurrence and its full packet, or return the same word. -/
theorem rewrite_step_eq (accepted : rewrite? p representative member replacement = some target)
    {old : Bank (regs := regs) model} (same : old.get representative = old.get member) :
    target.step model old = p.step model old :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.rewrite_step_eq accepted same

/-- Preserve native block-budget observations from the original typed input bank. -/
theorem rewrite_run_eq (accepted : rewrite? p representative member replacement = some target)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.rewrite_run_eq accepted fuel input

theorem rewrite_returns_iff (accepted : rewrite? p representative member replacement = some target)
    (input : Bank (regs := regs) model) (result : BitVec 64) :
    (∃ fuel, target.source.runFrom model fuel 0 input = some result) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some result := by
  simp only [rewrite_run_eq accepted]

theorem rewrite_absence_iff (accepted : rewrite? p representative member replacement = some target)
    (input : Bank (regs := regs) model) :
    (∀ fuel, target.source.runFrom model fuel 0 input = none) ↔
      ∀ fuel, p.source.runFrom model fuel 0 input = none := by
  simp only [rewrite_run_eq accepted]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges
