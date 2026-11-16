module

public import Silmaril.Wasm.Cfg.BlockTyping.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Thms
import Silmaril.Proofs.Wasm.Cfg.BlockTyping

@[expose] public section

/-!
# Typed basic blocks: theorems

`bodyIfaces_typed`: every interface `bodyIfaces` records is an `Instrs_ok` derivation of its
instructions under its static context (`BlockIface.Typed`). This is the validator's typing
judgement, the specification's `Instrs_ok`, so it is a fact about the block's instructions, not
about a run of them.

`bodyIfaces_lookup`: each recorded interface's instructions are the segment `lookup` names for
its identity, so an interface is the typing of that block of the body.

`bodyIfaces_complete`: when the validator's expression checker accepts the body (`exprC`, as
`funcCheck` runs it), every block `lookup` names gets an interface.

Together: for a body that validates, the interfaces are exactly one typed interface per block.
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Wasm.Validation

/-- **Every recorded block interface is typed** (`Instrs_ok`). -/
theorem bodyIfaces_typed (C : Context) (body : Expr) : ∀ x ∈ bodyIfaces C body, x.Typed :=
  Proofs.BlockTyping.typeWalk_typed [] 0 ⟨C, [], false⟩ [] body

/-- **A recorded interface is about the block `lookup` names**: its instructions are that
block's segment. -/
theorem bodyIfaces_lookup (C : Context) (body : Expr) :
    ∀ x ∈ bodyIfaces C body, ∃ seg, lookup body x.id = some seg ∧ x.instrs = seg.instrs := by
  intro x hx
  obtain ⟨seg, h1, h2⟩ := Proofs.BlockTyping.typeWalk_mem [] 0 ⟨C, [], false⟩ [] body x hx
  exact ⟨seg, (mem_blocks body x.id seg).1 h1, h2⟩

/-- **Every block of a validated body gets a typed interface**. The hypothesis is the expression
check that `funcCheck` performs on a function body. -/
theorem bodyIfaces_complete (C : Context) (body : Expr) (rs : List CValType)
    (h : exprC C body rs = true) :
    ∀ b seg, lookup body b = some seg → ∃ x ∈ bodyIfaces C body, x.id = b := by
  intro b seg hb
  have hc : ∃ r, checkSeq atomC tyOkC C [] false (some rs) body = some r := by
    simp only [exprC, checkExpr?, Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · exact ⟨_, by assumption⟩
    · cases h
  obtain ⟨r, hc⟩ := hc
  obtain ⟨r', hn⟩ := Proofs.BlockTyping.checkSeq_goal_none _ _ _ _ _ _ hc
  obtain ⟨st', hrun⟩ := Proofs.BlockTyping.checkSeq_run _ _ _ _ _ hn
  have hmem : (b, seg) ∈ walk [] 0 [] body := (mem_blocks body b seg).2 hb
  exact Proofs.BlockTyping.typeWalk_complete [] 0 ⟨C, [], false⟩ [] body ⟨st', by simpa using hrun⟩
    (by simp [resOk]) _ hmem

end Silmaril.Wasm.Cfg
