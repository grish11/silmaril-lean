module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.RegisterRename

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Cyclic.RoundTrip (renameGraph renameBody renameTerm PacketClosed PacketClosedTable)

universe v w
variable {V W K : Type w} {F : Type v}

private theorem lookup_map (rename : V → W) [DecidableEq K]
    (blocks : List (K × Block V K F)) (label : K) :
    ((blocks.map fun (k, b) => (k, Block.mk (rename b.param) (renameBody rename b.body))).lookup label).isNone =
      (blocks.lookup label).isNone := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨k, block⟩
    by_cases same : label == k <;> simp [List.lookup, same] at ih ⊢
    exact ih

private theorem reads_rename (rename : V → W) (fields : List V) :
    (LiveOut.reads fields).rename rename = LiveOut.reads (fields.map rename) := by
  induction fields <;> simp_all [LiveOut.reads, Val.rename]

private theorem attachTerm_rename (rename : V → W) (exit : K → Bool) (fields : K → List V)
    (term : Term V K F) :
    LiveOut.attachTerm exit (fun k => (fields k).map rename) (renameTerm rename term) =
      renameTerm rename (LiveOut.attachTerm exit fields term) := by
  induction term with
  | br k value => cases h : exit k <;> simp [LiveOut.attachTerm, renameTerm, h, Val.rename, reads_rename]
  | case op x left y right ihl ihr => simp [renameTerm, LiveOut.attachTerm, ihl, ihr]

private theorem attachBody_rename (rename : V → W) (exit : K → Bool) (fields : K → List V)
    (body : Body V K F) :
    LiveOut.attachBody exit (fun k => (fields k).map rename) (renameBody rename body) =
      renameBody rename (LiveOut.attachBody exit fields body) := by
  induction body with
  | term tail => simp [LiveOut.attachBody, renameBody, attachTerm_rename]
  | let1 _ _ _ ih | let2 _ _ _ _ ih => simp [LiveOut.attachBody, renameBody, ih]

theorem attach_rename [DecidableEq K] (rename : V → W) (fields : K → List V) (g : CFG V K F) :
    LiveOut.attach (fun k => (fields k).map rename) (renameGraph rename g) =
      renameGraph rename (LiveOut.attach fields g) := by
  have exits : (fun k => ((renameGraph rename g).blocks.lookup k).isNone) =
      fun k => (g.blocks.lookup k).isNone :=
    funext fun k => lookup_map rename g.blocks k
  unfold LiveOut.attach
  rw [exits]
  simp only [renameGraph, attachBody_rename, List.map_map, Function.comp_def]

variable [DecidableEq V] [DecidableEq W] (rename : V ↪ W)

private theorem val_fv (a : Val V) : (a.rename rename).fv = a.fv.map rename := by
  induction a <;> simp_all [Val.rename, Val.fv, Finset.map_union]

private theorem op_fv (a : Op V F) : (a.rename rename).fv = a.fv.map rename := by
  cases a <;> simp [Op.rename, Op.fv, val_fv]

private theorem term_fv (t : Term V K F) :
    (renameTerm rename t).toRegion.fv = t.toRegion.fv.map rename := by
  induction t <;> simp_all [renameTerm, Term.toRegion, Region.fv, val_fv, op_fv,
    Finset.map_union, Finset.map_erase]

private theorem body_fv (b : Body V K F) :
    (renameBody rename b).toRegion.fv = b.toRegion.fv.map rename := by
  induction b <;> simp_all [renameBody, Body.toRegion, Region.fv, term_fv, op_fv,
    Finset.map_union, Finset.map_erase]

theorem closed_rename (g : CFG V K F) (closed : PacketClosed g) :
    PacketClosed (renameGraph rename g) := by
  intro item mem
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp mem
  change (renameBody rename source.2.body).toRegion.fv ⊆ {rename source.2.param}
  rw [body_fv, ← Finset.map_singleton, Finset.map_subset_map]
  exact closed source present

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.RegisterRename
