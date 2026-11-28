module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Composition.Correctness

/-! The native quad renamer and forward tuple permutation compose exactly. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation pull_refl pull_trans)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {old mid new : List (ValueSort Data)} {out : ValueSort Data}

theorem program_refl (p : Program Op old out) :
    program (Permutation.refl (dataPorts old)) p = p :=
  Proofs.program_refl p

theorem program_trans (h : Registers old mid) (k : Registers mid new) (p : Program Op old out) :
    program k (program h p) = program (h.trans k) p :=
  Proofs.program_trans h k p

variable {F : SeaOfNodes.Diamond.Ty Data → Type w}

theorem push_refl (bank : Tuple F (dataPorts old)) :
    push (Permutation.refl (dataPorts old)) bank = bank :=
  pull_refl bank

theorem push_trans (h : Registers old mid) (k : Registers mid new)
    (bank : Tuple F (dataPorts old)) :
    push k (push h bank) = push (h.trans k) bank :=
  pull_trans k.symm h.symm bank

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex
