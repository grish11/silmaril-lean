module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Compile
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification

open CategoryTheory
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.Loop.MLIR.CF (Op)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation generatedRoom)
open Example (old new identify aliasesWrite lhs rhs output original originalProgram conflicting changesAdmission input refusal run)

#guard run true == some (some 99, some 99, some 99)
#guard run false == some (some 14, some 14, some 14)
#guard refusal identify conflicting == some .incompatibleFacts
#guard refusal aliasesWrite original == some .aliasedWrite
#guard refusal identify changesAdmission == some (.checker .neitherMarked)

example : slot lhs ≠ slot rhs := by decide

example (values : Valuation new) : (reduct identify values).get lhs = (reduct identify values).get rhs :=
  reduct_identifies identify values lhs rhs rfl

example : (program identify originalProgram).preheader =
    ([⟨_, _, identify _ output, .arithmetic (.binary .addi),
      .cons (identify _ lhs) (.cons (identify _ lhs) .nil)⟩] : List (Quad Op new.regs)) := rfl

private def unequalEntry : Valuation old :=
  .cons ⟨true⟩ (.cons ⟨false⟩ (.cons (7 : Word width) (.cons (8 : Word width) (.cons (0 : Word width) .nil))))

example (values : Valuation new) : reduct identify values ≠ unequalEntry := by
  intro same
  have equalCaptures := reduct_identifies identify values lhs rhs rfl
  rw [same] at equalCaptures
  change (7 : Word width) = (8 : Word width) at equalCaptures
  exact (show (7 : Word width) ≠ (8 : Word width) by decide) equalCaptures

example (backend : Backend) (p : AdmittedAt old width) (accepted : original = .ok p)
    (target : Generated new width) (ok : compile identify p = .ok target) :
    backend.Returns target.artifacts (input 7 false) (14 : Word width) := by
  refine (compile_returns_iff identify p ok backend _ _).mpr ⟨5, ?_⟩
  rw [(Proofs.admit_fields originalProgram _ p accepted).1]
  rfl

example (backend : Backend) (values : Valuation new) (sentence : Sentence (Compiled identify width)) :
    (generatedRoom width backend new).Sat (Discrete.mk values) (sentence.map Compiled.target) ↔
      (checkedSourceRoom identify width).Sat (Discrete.mk (reduct identify values)) sentence :=
  (corridor identify width backend).sat _ _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification
