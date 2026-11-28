module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RegisterRename.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.RegisterRename

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Cyclic.RoundTrip (renameGraph renameTerm renameBody)

universe v w
variable {V W K : Type w} {F : Type v} [DecidableEq V] [DecidableEq W]
  (rename : V ↪ W)

private theorem bind_rename {n : Nat} {old : Names V n} {new : Names W n}
    (agree : ∀ x, new (rename x) = old x) (reg key : V) :
    bindName new (rename reg) (rename key) = bindName old reg key := by
  simp [bindName, rename.injective.eq_iff, agree]

omit [DecidableEq V] [DecidableEq W] in
private theorem val_rename {n : Nat} {old : Names V n} {new : Names W n}
    (agree : ∀ x, new (rename x) = old x) (a : Val V) :
    value (F := F) new (a.rename rename) = value old a := by
  induction a <;> simp_all [value, Val.rename]

omit [DecidableEq V] [DecidableEq W] in
private theorem op_rename {n : Nat} {old : Names V n} {new : Names W n}
    (agree : ∀ x, new (rename x) = old x) (a : Op V F) :
    operand new (a.rename rename) = operand old a := by
  cases a <;> simp [operand, Op.rename, val_rename rename agree]

variable {labels : Nat} (index : K → Option (Fin labels))

private theorem term_rename {n : Nat} {old : Names V n} {new : Names W n}
    (agree : ∀ x, new (rename x) = old x) (t : Term V K F) :
    term index new (renameTerm rename t) = term index old t := by
  induction t generalizing n with
  | br k a => simp [term, renameTerm, val_rename rename agree]
  | case op x l y r ihl ihr =>
    simp only [term, renameTerm, op_rename rename agree, ihl (bind_rename rename agree x),
      ihr (bind_rename rename agree y)]

private theorem body_rename {n : Nat} {old : Names V n} {new : Names W n}
    (agree : ∀ x, new (rename x) = old x) (b : Body V K F) :
    body index new (renameBody rename b) = body index old b := by
  induction b generalizing n with
  | term t => exact term_rename rename index agree t
  | let1 x op rest ih =>
    simp only [body, renameBody, op_rename rename agree, ih (bind_rename rename agree x)]
  | let2 x y op rest ih =>
    simp only [body, renameBody, op_rename rename agree,
      ih (bind_rename rename (bind_rename rename agree x) y)]

omit [DecidableEq V] [DecidableEq W] in
private theorem index_rename [DecidableEq K] (g : CFG V K F) (exits : List K) (k : K) :
    labelIndex (renameGraph rename g).blocks exits k =
      (labelIndex g.blocks exits k).map
        (Fin.cast (congrArg (· + exits.length) (List.length_map ..).symm)) := by
  have indices : ((renameGraph rename g).blocks.findFinIdx? (fun b => k == b.1)) =
      (g.blocks.findFinIdx? (fun b => k == b.1)).map (Fin.cast (List.length_map ..).symm) := by
    simp only [renameGraph, List.findFinIdx?_eq_pmap_findIdx?, List.findIdx?_map, Option.map_pmap]
    rfl
  simp only [labelIndex, indices]
  cases g.blocks.findFinIdx? (fun b => k == b.1) with
  | some i => rfl
  | none =>
    simp only [Option.map_none, Option.map_map]
    apply congrArg (fun f => (exits.findFinIdx? (fun exit => k == exit)).map f)
    funext i
    apply Fin.ext
    simp [renameGraph]

theorem elaborateAt_rename [DecidableEq K] (g : CFG V K F) (exits : List K) {n : Nat}
    (captures : Fin n → V) (count : Nat) (len : g.blocks.length = count)
    (renamedLen : (renameGraph rename g).blocks.length = count) :
    elaborateAt (renameGraph rename g) exits (rename ∘ captures) count renamedLen =
      elaborateAt g exits captures count len := by
  let number : K → Option (Fin (count + exits.length)) := fun k =>
    (labelIndex g.blocks exits k).map (Fin.cast (congrArg (· + exits.length) len))
  have numbered : (fun k => (labelIndex (renameGraph rename g).blocks exits k).map
      (Fin.cast (congrArg (· + exits.length) renamedLen))) = number := by
    funext k
    rw [index_rename]
    unfold number
    erw [Option.map_map]
    rfl
  have captured (x : V) : first (rename ∘ captures) (rename x) = first captures x := by
    simp [first, rename.injective.eq_iff]
  have block (i : Fin count) :
      body number (blockNames (n := n) ((renameGraph rename g).blocks[Fin.cast renamedLen.symm i]).2.param)
        ((renameGraph rename g).blocks[Fin.cast renamedLen.symm i]).2.body =
      body number (blockNames (n := n) g.blocks[Fin.cast len.symm i].2.param)
        g.blocks[Fin.cast len.symm i].2.body := by
    have picked : (renameGraph rename g).blocks[Fin.cast renamedLen.symm i] =
        (g.blocks[Fin.cast len.symm i].1,
          ⟨rename g.blocks[Fin.cast len.symm i].2.param, renameBody rename g.blocks[Fin.cast len.symm i].2.body⟩) := by
      have bound : i.val < (g.blocks.map (fun b =>
          (b.1, Block.mk (rename b.2.param) (renameBody rename b.2.body)))).length :=
        by simpa only [List.length_map] using (len.symm ▸ i.isLt : i.val < g.blocks.length)
      change (g.blocks.map (fun b => (b.1, Block.mk (rename b.2.param)
        (renameBody rename b.2.body))))[i.val]'bound = _
      rw [List.getElem_map]
      rfl
    rw [picked]
    exact body_rename rename number (bind_rename rename (fun _ => rfl) _) _
  unfold elaborateAt
  rw [numbered, show (renameGraph rename g).entry = renameBody rename g.entry from rfl]
  simp only [body_rename rename number captured, block]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.RegisterRename
