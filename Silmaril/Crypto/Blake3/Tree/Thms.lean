module

public import Silmaril.Crypto.Blake3.Tree.Defs
import Silmaril.Proofs.Crypto.Blake3.Evaluation

public section

namespace Silmaril.Crypto.Blake3

theorem Compression.graph_canonical (run : Input → Option CV) : Compression.Canonical (graph run) :=
  fun {_ _ _} left right => Option.some.inj (left.symm.trans right)

theorem Compression.noCollision_of_bindingOn {rel : Compression} {domain : Input → Prop}
    (binding : BindingOn rel domain) (within : ∀ ⦃input output⦄, rel input output → domain input) : ¬ Collision rel :=
  fun ⟨_, _, _, distinct, left, right⟩ => distinct (binding (within left) (within right) left right)

theorem geometry_size (first size : Nat) : (geometry first size).size = size :=
  Proofs.Crypto.Blake3.geometry_size first size

theorem eval_graph {run : Input → Option CV} {root : Bool} {shape : Shape} {opening : Opening} {output : CV} :
    eval? run root shape opening = some output ↔ Trace (Compression.graph run) root shape opening output :=
  Proofs.Crypto.Blake3.eval_graph

theorem eval_sound {rel : Compression} {run : Input → Option CV} {root : Bool}
    {shape : Shape} {opening : Opening} {output : CV} (consistent : Compression.Consistent rel run)
    (hit : eval? run root shape opening = some output) : Trace rel root shape opening output :=
  Proofs.Crypto.Blake3.eval_sound consistent hit

theorem root_graph {run : Input → Option CV} {size : Nat} {opening : Opening} {digest : Bytes} :
    root? run size opening = some digest ↔ Root (Compression.graph run) size digest opening :=
  Proofs.Crypto.Blake3.root_graph

theorem root_sound {rel : Compression} {run : Input → Option CV} {size : Nat} {opening : Opening}
    {digest : Bytes} (consistent : Compression.Consistent rel run)
    (hit : root? run size opening = some digest) : Root rel size digest opening :=
  Proofs.Crypto.Blake3.root_sound consistent hit

theorem hash_total {run : Input → Option CV} (total : ∀ input, ∃ cv, run input = some cv)
    {bytes : Bytes} (valid : validSize bytes.length) : ∃ digest, hash? run bytes = some digest :=
  Proofs.Crypto.Blake3.hash_total total valid

theorem digestBytes_length (cv : CV) : (digestBytes cv).length = 32 := Vector.length_toList

end Silmaril.Crypto.Blake3
