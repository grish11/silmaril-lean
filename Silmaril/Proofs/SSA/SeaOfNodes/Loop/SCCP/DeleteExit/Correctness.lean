module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Proofs

open Diamond (Dataflow dataPorts)
open Diamond.SCCP (TupleCovers)
open RVSDG (extend)
open SeaOfNodes.MLIR (sourceInputs)
open SeaOfNodes.MLIR.Lowering (Scope lowerCode)
open Loop.MLIR.CF (TargetOp entryScope evalOp model opcode)
open Loop.MLIR.CF.Bank (Label bankOperands headerScope lower)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame Terminator)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width}

private theorem restrictTerm_eval {Δ : List Width} {term : Terminator (Label carried result) [result] Δ}
    {restricted : Terminator (HeaderLabel carried) [result] Δ}
    (ok : restrictTerm term = some restricted) (env : Env Δ) :
    term.eval env = (restricted.eval env).map embedFrame id := by
  cases term with
  | br edge =>
    rcases edge with ⟨label, operands⟩
    cases label with
    | header => cases ok; rfl
    | exit => cases ok
  | condBr => cases ok
  | ret => cases ok

theorem restrictBlock_eval {Δ : List Width} {block : Block TargetOp (Label carried result) Δ [result]}
    {restricted : Block TargetOp (HeaderLabel carried) Δ [result]}
    (ok : restrictBlock block = some restricted) (env : Env Δ) :
    block.eval evalOp (fun term scope => Terminator.eval scope term) env =
      (restricted.eval evalOp (fun term scope => Terminator.eval scope term) env).map embedFrame id := by
  induction block with
  | terminator term =>
    obtain ⟨kept, h, rfl⟩ := Option.map_eq_some_iff.mp ok
    exact restrictTerm_eval h env
  | letOp op operands rest ih =>
    obtain ⟨kept, h, rfl⟩ := Option.map_eq_some_iff.mp ok
    exact ih h _

theorem delete_blocks {cfg : FullCfg Γ carried result} {clean : HeaderCfg Γ carried result}
    (deleted : delete cfg = some clean) :
    restrictBlock cfg.entry = some clean.entry ∧
      restrictBlock (cfg.block .header) = some (clean.block .header) := by
  unfold delete at deleted
  cases hEntry : restrictBlock cfg.entry with
  | none => simp [hEntry] at deleted
  | some entry =>
    cases hHeader : restrictBlock (cfg.block .header) with
    | none => simp [hEntry, hHeader] at deleted
    | some header =>
      simp [hEntry, hHeader] at deleted
      subst clean
      exact ⟨rfl, rfl⟩

theorem runFrom_eq {cfg : FullCfg Γ carried result} {clean : HeaderCfg Γ carried result}
    (deleted : delete cfg = some clean) (fuel : Nat) (input : Env Γ) (frame : Frame (HeaderLabel carried)) :
    clean.runFrom evalOp fuel input frame = cfg.runFrom evalOp fuel input (embedFrame frame) := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
    rcases frame with ⟨label, args⟩
    cases label
    have same := restrictBlock_eval (delete_blocks deleted).2 (args.append input)
    change clean.runBlock evalOp input (fuel + 1) (clean.block .header) (args.append input) =
      cfg.runBlock evalOp input (fuel + 1) (cfg.block .header) (args.append input)
    rw [Cfg.runBlock, Cfg.runBlock, same]
    cases eval : (clean.block .header).eval evalOp (fun term scope => Terminator.eval scope term) (args.append input) with
    | inl next => exact ih next
    | inr value => rfl

theorem run_eq {cfg : FullCfg Γ carried result} {clean : HeaderCfg Γ carried result}
    (deleted : delete cfg = some clean) (fuel : Nat) (input : Env Γ) :
    clean.run evalOp fuel input = cfg.run evalOp fuel input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have same := restrictBlock_eval (delete_blocks deleted).1 input
    unfold Cfg.run
    rw [Cfg.runBlock, Cfg.runBlock, same]
    cases eval : clean.entry.eval evalOp (fun term scope => Terminator.eval scope term) input with
    | inl next => exact runFrom_eq deleted fuel input next
    | inr value => rfl

theorem denotePart_eq {cfg : FullCfg Γ carried result} {clean : HeaderCfg Γ carried result}
    (deleted : delete cfg = some clean) (input : Env Γ) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed clean).denotePart evalOp input = (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff,
    Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, run_eq deleted]

private theorem restrict_lowerCode {args : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}
    (flow : Dataflow Loop.MLIR.CF.Op args past sigs) (scope : Scope args past Γ)
    (full : ∀ {Δ}, Scope args (extend past sigs) Δ → Terminator (Label carried result) [result] Δ)
    (clean : ∀ {Δ}, Scope args (extend past sigs) Δ → Terminator (HeaderLabel carried) [result] Δ)
    (ok : ∀ {Δ} (final : Scope args (extend past sigs) Δ), restrictTerm (full final) = some (clean final)) :
    restrictBlock (lowerCode opcode flow scope full) = some (lowerCode opcode flow scope clean) := by
  induction flow generalizing Γ with
  | nil =>
    simp only [lowerCode, restrictBlock]
    rw [ok scope]
    rfl
  | cons op operands rest ih =>
    simp only [lowerCode, restrictBlock]
    rw [ih _ (fun final => full final) (fun final => clean final) (fun final => ok final)]
    rfl

variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs)

theorem delete_feedback :
    delete (PruneInfeasibleExit.directFeedback g) =
      some { entry := lowerCode opcode g.preheader (entryScope Γ)
               (fun scope => .br ⟨.header, bankOperands scope (g.phiInputs .entry)⟩)
             block := fun
               | .header => lowerCode opcode g.header (headerScope Γ carried)
                   (fun scope => .br ⟨.header, bankOperands scope (g.phiInputs .backedge)⟩) } := by
  unfold delete
  rw [PruneInfeasibleExit.entry_eq, PruneInfeasibleExit.header_shape]
  change (restrictBlock (lowerCode opcode g.preheader (entryScope Γ) _)).bind _ = _
  erw [restrict_lowerCode g.preheader _ _ _ (fun _ => rfl)]
  erw [restrict_lowerCode g.header _ _ _ (fun _ => rfl)]
  rfl

private theorem restrict_lowerCode_exit {args : List (Diamond.Ty Width)}
    {past sigs : List (List (Diamond.Ty Width))} (flow : Dataflow Loop.MLIR.CF.Op args past sigs)
    (scope : Scope args past Γ) (finish : ∀ {Δ}, Scope args (extend past sigs) Δ →
      Terminator (Label carried result) [result] Δ)
    (refused : ∀ {Δ} (final : Scope args (extend past sigs) Δ), restrictTerm (finish final) = none) :
    restrictBlock (lowerCode opcode flow scope finish) = none := by
  induction flow generalizing Γ with
  | nil =>
    simp only [lowerCode, restrictBlock]
    rw [refused scope]
    rfl
  | cons op operands rest ih =>
    simp only [lowerCode, restrictBlock]
    rw [ih _ (fun final => finish final) (fun final => refused final)]
    rfl

theorem delete_exitBranch : delete (PruneExit.Bank.directExit g) = none := by
  unfold delete
  rw [PruneExit.Bank.header_shape]
  rw [restrict_lowerCode_exit g.header _ _ (fun _ => rfl)]
  cases restrictBlock (PruneExit.Bank.directExit g).entry <;> rfl

variable {g} {facts : PruneExit.InputFacts Γ} {cfg : FullCfg Γ carried result}
variable {clean : HeaderCfg Γ carried result}

theorem rewrite_eq_kept_iff :
    rewrite g facts = some (.kept cfg) ↔ PruneExit.Bank.rewrite g facts = some cfg := by
  unfold rewrite
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨pruned, success, h⟩
    rcases Prune.rewrite_eq_some_iff.mp success with exits | feedback
    · obtain ⟨_, rfl⟩ := PruneExit.Bank.rewrite_eq_some_iff.mp exits
      simp only [delete_exitBranch, Output.kept.injEq] at h
      exact h ▸ exits
    · obtain ⟨_, rfl⟩ := PruneInfeasibleExit.rewrite_eq_some_iff.mp feedback
      simp only [delete_feedback] at h
      cases h
  · intro exits
    refine ⟨cfg, Prune.rewrite_eq_some_iff.mpr (.inl exits), ?_⟩
    obtain ⟨_, rfl⟩ := PruneExit.Bank.rewrite_eq_some_iff.mp exits
    rw [delete_exitBranch]

theorem rewrite_eq_deleted_iff :
    rewrite g facts = some (.deleted clean) ↔
      ∃ cfg, PruneInfeasibleExit.rewrite g facts = some cfg ∧ delete cfg = some clean := by
  unfold rewrite
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨cfg, success, h⟩
    rcases Prune.rewrite_eq_some_iff.mp success with exits | feedback
    · obtain ⟨_, rfl⟩ := PruneExit.Bank.rewrite_eq_some_iff.mp exits
      simp only [delete_exitBranch] at h
      cases h
    · refine ⟨cfg, feedback, ?_⟩
      cases restricted : delete cfg with
      | none => rw [restricted] at h; cases h
      | some next => rw [restricted] at h; cases h; rfl
  · rintro ⟨cfg, feedback, deleted⟩
    exact ⟨cfg, Prune.rewrite_eq_some_iff.mpr (.inr feedback), by rw [deleted]⟩

variable {output : Output Γ carried result} {input : Env Γ}

theorem rewrite_run_eq (rewritten : rewrite g facts = some output)
    (covered : TupleCovers facts (sourceInputs input)) (fuel : Nat) :
    output.run fuel input = (lower g).run evalOp fuel input := by
  cases output with
  | kept cfg => exact PruneExit.Bank.run_eq (rewrite_eq_kept_iff.mp rewritten) covered fuel
  | deleted clean =>
    obtain ⟨cfg, feedback, deleted⟩ := rewrite_eq_deleted_iff.mp rewritten
    exact (run_eq deleted fuel input).trans (PruneInfeasibleExit.run_eq feedback covered fuel)

theorem rewrite_denotePart_eq (rewritten : rewrite g facts = some output)
    (covered : TupleCovers facts (sourceInputs input)) :
    output.denotePart input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) := by
  cases output with
  | kept cfg => exact PruneExit.Bank.denotePart_eq (rewrite_eq_kept_iff.mp rewritten) covered
  | deleted clean =>
    obtain ⟨cfg, feedback, deleted⟩ := rewrite_eq_deleted_iff.mp rewritten
    exact (denotePart_eq deleted input).trans (PruneInfeasibleExit.denotePart_eq feedback covered)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Proofs
