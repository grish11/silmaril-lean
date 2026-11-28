module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.LambdaSSA
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG

universe u v w

variable {V K : Type w} {F G : Type u} (f : F → G)

theorem elaborateAt_eq {n : Nat} [DecidableEq V] [DecidableEq K]
    (g : CFG V K F) (exits : List K) (captures : Fin n → V) :
    elaborateAt g exits captures g.blocks.length rfl = elaborate g exits captures := by
  have idcast : Fin.cast (congrArg (· + exits.length) (rfl : g.blocks.length = _)) = id :=
    funext Fin.cast_eq_self
  simp only [elaborateAt, elaborate, idcast, Option.map_id, Fin.cast_eq_self, id_eq]

private theorem value_map {n : Nat} (ns : Names V n) (a : Val V) :
    (value (F := G) ns a) = (value (F := F) ns a).map (fun t => t.mapInstr f) := by
  induction a <;> simp_all [value, LetCase.LocallyNameless.Tm.mapInstr, Option.map_bind,
    Option.bind_map, Function.comp_def]

private theorem operand_map {n : Nat} (ns : Names V n) (a : Op V F) :
    operand ns (a.mapOp f) = (operand ns a).map (fun t => t.mapInstr f) := by
  cases a with
  | val a => exact value_map f ns a
  | app op a =>
    simp only [operand, Op.mapOp]
    rw [value_map f ns a]
    simp only [Option.map_map, Function.comp_def, LetCase.LocallyNameless.Tm.mapInstr]
  | inl | inr | abort => rfl

variable [DecidableEq V] {labels : Nat} (idx : K → Option (Fin labels))

private theorem term_map {n : Nat} (ns : Names V n) (a : Term V K F) :
    term idx ns (a.mapOp f) = (term idx ns a).map (fun t => t.mapInstr f) := by
  induction a generalizing n with
  | br label arg =>
    simp only [Term.mapOp, term]
    cases idx label with
    | none => rfl
    | some i =>
      simp only [Option.bind_some]
      rw [value_map f ns arg]
      simp only [Option.map_map, Function.comp_def, Flat.mapInstr]
  | case op x l y r ihl ihr =>
    simp only [Term.mapOp, term, operand_map, ihl, ihr, Option.bind_map, Option.map_map,
      Option.map_bind, Function.comp_def, Flat.mapInstr]

private theorem body_map {n : Nat} (ns : Names V n) (a : Body V K F) :
    body idx ns (a.mapOp f) = (body idx ns a).map (fun t => t.mapInstr f) := by
  induction a generalizing n with
  | term t => exact term_map f idx ns t
  | let1 _ _ _ ih | let2 _ _ _ _ ih =>
    simp only [Body.mapOp, body, operand_map, ih, Option.bind_map, Option.map_bind,
      Option.map_map, Function.comp_def, Flat.mapInstr]

private theorem tabulate_map {A : Type u} {B : Type v} (map : A → B) (n : Nat)
    (xs : Fin n → Option A) :
    tabulate n (fun i => (xs i).map map) =
      (tabulate n xs).map (fun table i => map (table i)) := by
  induction n with
  | zero => exact congrArg some (funext fun i => i.elim0)
  | succ n ih =>
    simp only [tabulate, ih, Option.bind_map, Option.map_map, Option.map_bind, Function.comp_def]
    cases xs 0 <;> simp only [Option.bind_none, Option.bind_some]
    congr 1
    funext table i
    exact Fin.cases rfl (fun _ => rfl) i

variable [DecidableEq K]

omit [DecidableEq V] in
private theorem labelIndex_map (bs : List (K × Block V K F)) (exits : List K) (k : K) :
    labelIndex (bs.map (fun b => (b.1, b.2.mapOp f))) exits k =
      (labelIndex bs exits k).map
        (Fin.cast (congrArg (· + exits.length) (List.length_map ..).symm)) := by
  have indices : (bs.map (fun b => (b.1, b.2.mapOp f))).findFinIdx? (fun b => k == b.1) =
      (bs.findFinIdx? (fun b => k == b.1)).map (Fin.cast (List.length_map ..).symm) := by
    simp only [List.findFinIdx?_eq_pmap_findIdx?, List.findIdx?_map, Option.map_pmap]
    rfl
  simp only [labelIndex, indices]
  cases bs.findFinIdx? (fun b => k == b.1) with
  | some i => rfl
  | none =>
    simp only [Option.map_none, Option.map_map]
    apply congrArg (fun f => (exits.findFinIdx? (fun exit => k == exit)).map f)
    funext i
    apply Fin.ext
    simp

theorem elaborateAt_mapOp (g : CFG V K F) (exits : List K) {n : Nat} (captures : Fin n → V)
    (count : Nat) (len : g.blocks.length = count) (mappedLen : (g.mapOp f).blocks.length = count) :
    elaborateAt (g.mapOp f) exits captures count mappedLen =
      (elaborateAt g exits captures count len).map (FiniteCFG.mapInstr f) := by
  let number : K → Option (Fin (count + exits.length)) := fun label =>
    (labelIndex g.blocks exits label).map (Fin.cast (congrArg (· + exits.length) len))
  have index : (fun label => (labelIndex (g.mapOp f).blocks exits label).map
      (Fin.cast (congrArg (· + exits.length) mappedLen))) = number := by
    funext label
    simp only [CFG.mapOp, labelIndex_map, Option.map_map]
    rfl
  have block (i : Fin count) :
      body number (blockNames (n := n) ((g.mapOp f).blocks[Fin.cast mappedLen.symm i]).2.param)
        ((g.mapOp f).blocks[Fin.cast mappedLen.symm i]).2.body =
      (body number (blockNames (n := n) (g.blocks[Fin.cast len.symm i]).2.param)
        (g.blocks[Fin.cast len.symm i]).2.body).map (Flat.mapInstr f) := by
    have sourceBound : i.val < g.blocks.length := len.symm ▸ i.isLt
    have mappedBound : i.val < (g.blocks.map (fun b => (b.1, b.2.mapOp f))).length :=
      by simpa only [List.length_map] using sourceBound
    have getBlock : (g.mapOp f).blocks[Fin.cast mappedLen.symm i] =
        (g.blocks[i.val].1, (g.blocks[i.val].2).mapOp f) := by
      change (g.blocks.map (fun b => (b.1, b.2.mapOp f)))[i.val]'mappedBound = _
      rw [List.getElem_map]
    exact (congrArg (fun b : K × Block V K G =>
      body number (blockNames (n := n) b.2.param) b.2.body) getBlock).trans
      (body_map f number (blockNames (n := n) g.blocks[i.val].2.param) g.blocks[i.val].2.body)
  unfold elaborateAt
  rw [index, show (g.mapOp f).entry = g.entry.mapOp f from rfl]
  simp only [body_map f number, block, tabulate_map, Option.bind_map, Option.map_bind,
    Option.map_map, Function.comp_def, FiniteCFG.mapInstr]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
