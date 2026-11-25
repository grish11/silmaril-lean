module

public import Silmaril.SSA.MLIR.SMT.Defs
import Silmaril.Proofs.SSA.MLIR.SMT.Correspondence

@[expose] public section

namespace Silmaril.MLIR.SMT

open Silmaril.Logic.Smt.Uflia

/-- Translation preserves the value of each typed block for every assignment
of its free SSA values. -/
theorem Block.eval_toSmt {Γ : Context} {s : Ty} (block : Block Γ s) (env : Env Γ) :
    Quantified.eval model env.toSmt block.toSmt = block.eval env :=
  Proofs.eval_block block env

/-- A Boolean block's translation holds exactly when the source yields true. -/
theorem Block.toFormula_holds_iff {Γ : Context} (block : Block Γ .bool) (env : Env Γ) :
    Quantified.Formula.Holds block.toFormula model env.toSmt ↔
      block.eval env = true := by
  exact (congrArg (· = true) (block.eval_toSmt env)).to_iff

end Silmaril.MLIR.SMT
