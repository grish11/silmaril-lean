module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation)
open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {old mid new : List (ValueSort Data)} {out : ValueSort Data}

private theorem operands_refl {T : Type u} {args ins : List T} (ops : Tuple (Port args) ins) :
    ops.map (fun t => Permutation.refl args t) = ops := by
  induction ops with
  | nil => rfl
  | cons p _ ih => exact congrArg (Tuple.cons p) ih

private theorem operands_trans {T : Type u} {args mid new ins : List T}
    (h : Permutation args mid) (k : Permutation mid new) (ops : Tuple (Port args) ins) :
    (ops.map (fun t => h t)).map (fun t => k t) = ops.map (fun t => h.trans k t) := by
  induction ops with
  | nil => rfl
  | cons p _ ih => exact congrArg (Tuple.cons (k _ (h _ p))) ih

theorem quad_refl (q : Quad Op old) : quad (Permutation.refl (dataPorts old)) q = q := by
  cases q with
  | mk ins result dest op operands =>
    exact congrArg (Quad.mk ins result dest op) (operands_refl operands)

theorem quad_trans (h : Registers old mid) (k : Registers mid new) (q : Quad Op old) :
    quad k (quad h q) = quad (h.trans k) q :=
  congrArg (Quad.mk q.ins q.result (k _ (h _ q.dest)) q.op) (operands_trans h k q.operands)

theorem program_refl (p : Program Op old out) :
    program (Permutation.refl (dataPorts old)) p = p := by
  have rename : quad (Op := Op) (Permutation.refl (dataPorts old)) = id := funext quad_refl
  cases p
  simp [program, rename, Permutation.refl]

theorem program_trans (h : Registers old mid) (k : Registers mid new) (p : Program Op old out) :
    program k (program h p) = program (h.trans k) p := by
  cases p
  simp [program, List.map_map, Function.comp_def, quad_trans, Permutation.trans]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Proofs
