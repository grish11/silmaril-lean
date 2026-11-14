module

public import Silmaril.Wasm.Cfg.BlockTyping.Defs
import Silmaril.Proofs.Wasm.Cfg.BlockTyping

@[expose] public section

/-!
# Typed basic blocks: theorems

`bodyIfaces_typed`: every interface `bodyIfaces` records is an `Instrs_ok` derivation of its
instructions under its static context (`BlockIface.Typed`). This is the validator's typing
judgement, the specification's `Instrs_ok`, so it is a fact about the block's instructions, not
about a run of them.

Open:
- that the recorded instructions are the segment `lookup` names for the same identity (the
  explorer checks this at build time);
- that the walk records every block of a valid body.
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Wasm.Validation

/-- **Every recorded block interface is typed** (`Instrs_ok`). -/
theorem bodyIfaces_typed (C : Context) (body : Expr) : ∀ x ∈ bodyIfaces C body, x.Typed :=
  Proofs.BlockTyping.typeWalk_typed [] 0 C [] false [] body

end Silmaril.Wasm.Cfg
