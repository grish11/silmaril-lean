module

public import Silmaril.SSA.PEG.Reindex.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic.Defs

/-! # Checked numbering for two-level reversion

The caller supplies maps from the proposed compiler numbering to input
addresses. The automatic checker verifies the reindexed table and
retains its certificate. Use `checkFinEquiv` to construct the finite
equivalences from untrusted forward and inverse maps. -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l k : Nat}

/-- The existing recognizer checks all mapped rows, operands, loop parents,
and roots in the proposed numbering. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] n l) (rows : Fin k ≃ Fin n) (loops : Fin k ≃ Fin l) :
    Option (Automatic.Accepted (g.reindex rows loops)) :=
  Automatic.extract (g.reindex rows loops)

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed
