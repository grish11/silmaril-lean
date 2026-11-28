module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.InstructionMap.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut

universe u v
variable {V K : Type u} {F G : Type v} (f : F → G) (isExit : K → Bool) (fields : K → List V)

private theorem term_mapOp (a : Term V K F) :
    attachTerm isExit fields (a.mapOp f) = (attachTerm isExit fields a).mapOp f := by
  induction a <;> simp_all only [attachTerm, Term.mapOp]

private theorem body_mapOp (b : Body V K F) :
    attachBody isExit fields (b.mapOp f) = (attachBody isExit fields b).mapOp f := by
  induction b <;> simp_all only [attachBody, Body.mapOp, term_mapOp]

theorem attach_mapOp [DecidableEq K] (g : CFG V K F) :
    attach fields (g.mapOp f) = (attach fields g).mapOp f := by
  have isExit : (fun k => ((g.mapOp f).blocks.lookup k).isNone) =
      fun k => (g.blocks.lookup k).isNone := by
    funext k
    change ((g.blocks.map (fun item => (item.1, item.2.mapOp f))).lookup k).isNone = _
    rw [lookup_mapOp, Option.isNone_map]
  unfold attach
  rw [isExit]
  simp only [CFG.mapOp, body_mapOp, List.map_map, Function.comp_def, Block.mapOp]

theorem project_reduct {M : Type u → Type u} {α : Type u} (model : Model G M α)
    (out : Transfer V K α) :
    project (model.reduct f) fields out = project model fields out := by
  have pack (regs : List V) :
      Version.packVal (model.reduct f) out.2.2 regs = Version.packVal model out.2.2 regs := by
    induction regs <;> simp_all only [Version.packVal, Model.reduct]
  simp only [project, pack]
  rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut
