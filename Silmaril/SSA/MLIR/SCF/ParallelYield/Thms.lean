module

public import Silmaril.SSA.MLIR.SCF.ParallelYield.Defs
public import Silmaril.SSA.MLIR.SCF.Parallel.Thms
import Silmaril.Proofs.SSA.MLIR.SCF.ParallelYield.Correctness

public section

namespace Silmaril.MLIR.SCF.ParallelYield

open Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

variable {Op : OpSignature} {Args Captures Result Slots : List Width}

/-- Observing the structural yield gives the same tuple as a fragment return. -/
theorem YieldRegion.asReturn_eval (region : YieldRegion Op Args Captures Result) (evalOp : Eval Op)
    (args : Env Args) (captures : Env Captures) :
    region.asReturn.eval evalOp Return.eval (args.append captures) =
      region.run evalOp args captures :=
  Proofs.asReturn_eval region evalOp args captures

/-- Slotwise laws give associativity and commutativity on the whole typed tuple. -/
theorem Combiners.tuple_laws (combiners : Combiners Op Captures Slots) (evalOp : Eval Op)
    (captures : Env Captures) (laws : combiners.Laws evalOp captures) :
    Std.Associative (combiners.eval evalOp captures) ∧
      Std.Commutative (combiners.eval evalOp captures) :=
  Proofs.combiner_laws combiners evalOp captures laws

theorem Program.bounds_fit (program : Program Op Captures Result) :
    program.space.lower < 2 ^ program.indexWidth.val ∧
      program.space.upper < 2 ^ program.indexWidth.val :=
  ⟨Nat.lt_of_le_of_lt (Nat.le_add_right _ _) program.exitFits,
    Nat.lt_of_le_of_lt program.space.upper_le_exitIndex program.exitFits⟩

/-- Each admitted trip reaches the body without truncating its mathematical induction value. -/
theorem Program.indexValue_exact (program : Program Op Captures Result) (trip : program.space.Trip) :
    (program.indexValue (program.space.index trip)).toNat = program.space.index trip := by
  rw [Program.indexValue, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (program.space.index_lt_upper trip) program.bounds_fit.2)

theorem Program.returns_denote (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) : program.Returns evalOp captures (program.denote evalOp captures) :=
  Proofs.returns_denote program evalOp captures

/-- The enclosing yield observes one result under the slotwise laws, over the
reduction trees admitted by the local pure model. -/
theorem Program.returns_iff_eq_denote (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (result : Env Result)
    (laws : program.combiners.Laws evalOp captures) :
    program.Returns evalOp captures result ↔ result = program.denote evalOp captures :=
  Proofs.returns_iff_eq_denote program evalOp captures result laws

theorem Program.denote_of_empty (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (empty : program.space.upper ≤ program.space.lower) :
    program.denote evalOp captures =
      program.continuation.run evalOp (program.initial.eval captures) captures :=
  Proofs.denote_of_empty program evalOp captures empty

/-- With no trips the enclosing region still runs, receiving the initial tuple. -/
theorem Program.returns_iff_of_empty (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (result : Env Result)
    (empty : program.space.upper ≤ program.space.lower) :
    program.Returns evalOp captures result ↔
      result = program.continuation.run evalOp (program.initial.eval captures) captures :=
  Proofs.returns_iff_of_empty program evalOp captures result empty

end Silmaril.MLIR.SCF.ParallelYield
