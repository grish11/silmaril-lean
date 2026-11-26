module

import Silmaril.SSA.MLIR.SCF.Parallel.Thms
public import Silmaril.SSA.MLIR.SCF.ParallelYield.Defs

public section

namespace Silmaril.MLIR.SCF.ParallelYield.Proofs

open Arith (Width Env)
open Silmaril.MLIR.Pure (Code Eval OpSignature)

variable {Op : OpSignature} {Args Captures Result Slots : List Width}

private theorem eval_map_yield (evalOp : Eval Op) {Γ : List Width}
    (code : Code Op (Yield Result) Γ) (env : Env Γ) :
    (code.mapTerm (fun | .yield values => .ret values)).eval evalOp Return.eval env =
      code.eval evalOp Yield.eval env := by
  induction code with
  | terminator term =>
    cases term
    rfl
  | letOp op operands rest ih =>
    exact ih (.cons (evalOp op (operands.eval env)) env)

theorem asReturn_eval (region : YieldRegion Op Args Captures Result) (evalOp : Eval Op)
    (args : Env Args) (captures : Env Captures) :
    region.asReturn.eval evalOp Return.eval (args.append captures) =
      region.run evalOp args captures :=
  eval_map_yield evalOp region (args.append captures)

theorem combiner_laws (combiners : Combiners Op Captures Slots) (evalOp : Eval Op)
    (captures : Env Captures) (laws : combiners.Laws evalOp captures) :
    Std.Associative (combiners.eval evalOp captures) ∧
      Std.Commutative (combiners.eval evalOp captures) := by
  induction combiners with
  | nil =>
    constructor
    · constructor
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      rfl
    · constructor
      rintro ⟨⟩ ⟨⟩
      rfl
  | cons head tail ih =>
    obtain ⟨headAssoc, headComm, tailLaws⟩ := laws
    obtain ⟨tailAssoc, tailComm⟩ := ih tailLaws
    constructor
    · constructor
      rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
      simp only [Combiners.eval, headAssoc.assoc, tailAssoc.assoc]
    · constructor
      rintro ⟨_, _⟩ ⟨_, _⟩
      simp only [Combiners.eval]
      congr 1
      · exact headComm.comm _ _
      · exact tailComm.comm _ _

theorem returns_denote (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) : program.Returns evalOp captures (program.denote evalOp captures) :=
  ⟨_, (program.reduction evalOp captures).returns_denote program.space, rfl⟩

theorem returns_iff_eq_denote (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (result : Env Result)
    (laws : program.combiners.Laws evalOp captures) :
    program.Returns evalOp captures result ↔ result = program.denote evalOp captures := by
  obtain ⟨assoc, comm⟩ := combiner_laws program.combiners evalOp captures laws
  constructor
  · rintro ⟨values, reachable, rfl⟩
    have unique := ((program.reduction evalOp captures).returns_iff_eq_denote
      program.space values assoc comm).mp reachable
    simp only [Program.denote, unique]
  · rintro rfl
    exact returns_denote program evalOp captures

theorem denote_of_empty (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (empty : program.space.upper ≤ program.space.lower) :
    program.denote evalOp captures =
      program.continuation.run evalOp (program.initial.eval captures) captures :=
  congrArg (fun values => program.continuation.run evalOp values captures)
    ((program.reduction evalOp captures).denote_of_empty program.space empty)

theorem returns_iff_of_empty (program : Program Op Captures Result) (evalOp : Eval Op)
    (captures : Env Captures) (result : Env Result)
    (empty : program.space.upper ≤ program.space.lower) :
    program.Returns evalOp captures result ↔
      result = program.continuation.run evalOp (program.initial.eval captures) captures := by
  constructor
  · rintro ⟨values, ⟨tree, valid, rfl⟩, rfl⟩
    exact congrArg (fun values => program.continuation.run evalOp values captures)
      ((program.reduction evalOp captures).eval_of_empty program.space tree valid empty)
  · intro equal
    rw [equal, ← denote_of_empty program evalOp captures empty]
    exact returns_denote program evalOp captures

end Silmaril.MLIR.SCF.ParallelYield.Proofs
