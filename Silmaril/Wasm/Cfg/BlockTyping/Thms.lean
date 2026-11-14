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

Open: that the walk records every block of a valid body (completeness).
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Wasm.Validation

/-- **Every recorded block interface is typed** (`Instrs_ok`). -/
theorem bodyIfaces_typed (C : Context) (body : Expr) : ∀ x ∈ bodyIfaces C body, x.Typed :=
  Proofs.BlockTyping.typeWalk_typed [] 0 C [] false [] body

/-- **A recorded interface is about the block `lookup` names**: its instructions are that
block's segment. -/
theorem bodyIfaces_lookup (C : Context) (body : Expr) :
    ∀ x ∈ bodyIfaces C body, ∃ seg, lookup body x.id = some seg ∧ x.instrs = seg.instrs := by
  intro x hx
  obtain ⟨seg, h1, h2⟩ := Proofs.BlockTyping.typeWalk_mem [] 0 C [] false [] body x hx
  exact ⟨seg, (mem_blocks body x.id seg).1 h1, h2⟩

end Silmaril.Wasm.Cfg
