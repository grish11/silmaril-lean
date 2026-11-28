module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

open Diamond (Ty Val ValueSort dataPorts)
open ConstantFold
open GVN (Producer)
open GVN.Cyclic.Deletion (Route)
open SubZero (model word)
open RVSDG (Tuple)
open scoped WordNormalize

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}
variable {block : Block inputs ports} {candidate : Producer block.flow word} {edit : Edit block}

/-- A hit is the existing ordered add decision restricted to the supported rules. -/
theorem add?_checked (accepted : add? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      addRule? applied.rule = some edit.rule ∧ edit.state = fromRewrite block applied.rewrite :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.add?_checked accepted

/-- A right-zero hit is certified by the existing source-ordered checker. -/
theorem rightZero?_checked (accepted : rightZero? block candidate = some edit) :
    ∃ applied, AddIdealize.step ⟨fun _ => none⟩ block.program candidate = .ok (some applied) ∧
      applied.rule = .rightZero ∧ edit.rule = .rightZero ∧ edit.state = fromRewrite block applied.rewrite :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.rightZero?_checked accepted

/-- An admitted unused-producer deletion always passes the progress check. -/
theorem unused?_eq_none_iff : unused? block candidate = none ↔ Deletion.delete? candidate block.packet = none :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.unused?_eq_none_iff

/-- A literal fold keeps the binding count and reduces the number of adds. -/
theorem Edit.literal_progress (selected : edit.rule = .literal) :
    edit.state.block.sigs.length = block.sigs.length ∧ addCount edit.state.block < addCount block := by
  have count := edit.bindingCount
  have drop := edit.progress
  simp [selected, Rule.erases] at count
  exact ⟨count, by simpa [Progress, selected, primaryWeight, count] using drop⟩

/-- An admitted swap keeps both primary counts and lowers literal-left occurrences. -/
theorem Edit.literalRight_progress (selected : edit.rule = .literalRight) :
    edit.state.block.sigs.length = block.sigs.length ∧
      addCount edit.state.block = addCount block ∧ leftLiteralCount edit.state.block < leftLiteralCount block :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.literalRight_progress selected

/-- The reused add goes through the existing exact-key representative and erasure checks. -/
theorem reuseAdd?_checked (accepted : reuseAdd? block candidate = some edit) :
    ∃ rewrite, isAdd candidate.key.opcode = true ∧ GVN.Pass.eliminateCandidate? candidate = some rewrite ∧
      edit.rule = .reuseAdd ∧ edit.state = fromRewrite block rewrite :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.reuseAdd?_checked accepted

/-- An add is reusable exactly when the current table has a checker-accepted earlier representative. -/
theorem reuseAdd?_eq_none_iff : reuseAdd? block candidate = none ↔
    isAdd candidate.key.opcode = false ∨
      ∀ representative : Producer block.flow word, GVN.checkRepresentative candidate representative = false :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.reuseAdd?_eq_none_iff

/-- Every hit comes from a checked nomination in the current table. -/
theorem step?_checked (accepted : step? block = some edit) :
    ∃ candidate : Producer block.flow word,
      add? block candidate = some edit ∨ reuseAdd? block candidate = some edit ∨ unused? block candidate = some edit :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.step?_checked accepted

/-- A failed scan excludes eligible edits at every current producer. -/
theorem step?_eq_none_iff (block : Block inputs ports) : step? block = none ↔ NoEligible block :=
  Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.step?_eq_none_iff block

/-- Count erasures separately from size-neutral edits. The
initial weight bounds all accepted steps. -/
theorem normalize_count (block : Block inputs ports) :
    let final := normalize block
    final.state.block.sigs.length + final.rules.countP Rule.erases = block.sigs.length ∧
      weight final.state.block + final.rules.length ≤ weight block :=
  let spec := Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize_spec block
  ⟨spec.1.1, spec.1.2.1⟩

/-- Termination exhausts the supported add and unused-producer checks on the final table. -/
theorem normalize_noEligible (block : Block inputs ports) : NoEligible (normalize block).state.block :=
  (Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize_spec block).1.2.2

/-- Re-running discovery on its output makes no further edit. -/
theorem normalize_stable (block : Block inputs ports) :
    (normalize (normalize block).state.block).rules = [] := by
  have stopped := (step?_eq_none_iff _).mpr (normalize_noEligible block)
  generalize (normalize block).state.block = final at stopped ⊢
  simp [normalize, run, stopped]

/-- Composed routes preserve mapped reads and route the complete packet. -/
theorem normalize_agrees (block : Block inputs ports) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Agrees block (normalize block).state entry :=
  (Proofs.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize_spec block).2 entry

theorem normalize_packet_eq (block : Block inputs ports) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    let final := (normalize block).state.block
    final.packet.read entry (final.flow.eval model entry PUnit.unit) =
      block.packet.read entry (block.flow.eval model entry PUnit.unit) :=
  let agree := normalize_agrees block entry
  (Route.wires_read model entry agree.1 block.packet agree.2).symm

theorem normalize_eval_eq (block : Block inputs ports) (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (normalize block).state.block.program.eval model entry = block.program.eval model entry := by
  rw [Block.program_eval, Block.program_eval, normalize_packet_eq]

end Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery
