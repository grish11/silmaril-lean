module

public import Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.CellEmbedding.Body

/-! The frame is unchanged by in-image loads and stores. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding

open RVSDG (Port Tuple)

variable {small large : Nat} {args : List ValueSort}

theorem read_extend (e : Embedding small large) (frame : Heap large) (source : Heap small) (a : Address small) :
    (extend e frame source).read (e a) = source.read a :=
  Proofs.extend_apply_image e frame source a

theorem eq_extend_iff (e : Embedding small large) (frame final : Heap large) (source : Heap small) :
    final = extend e frame source ↔ restrict e final = source ∧ SameFrame e frame final :=
  Proofs.eq_extend_iff e frame final source

theorem restrict_extend (e : Embedding small large) (frame : Heap large) (source : Heap small) :
    restrict e (extend e frame source) = source :=
  ((eq_extend_iff e frame _ source).mp rfl).1

theorem extend_restrict (e : Embedding small large) (heap : Heap large) :
    extend e heap (restrict e heap) = heap :=
  Proofs.extend_restrict e heap

theorem result_injective (e : Embedding small large) (frame : Heap large) :
    Function.Injective (result e frame) :=
  Proofs.result_injective e frame

theorem write_extend (e : Embedding small large) (frame : Heap large) (source : Heap small)
    (a : Address small) (word : Word) :
    (extend e frame source).write (e a) word = extend e frame (source.write a word) :=
  Proofs.write_extend e frame source a word

theorem input_get (e : Embedding small large) (values : Tuple (Val small) args)
    {sort : ValueSort} (port : Port args sort) :
    (input e values).get port = value e sort (values.get port) :=
  Proofs.input_get e values port

theorem denote_graph (e : Embedding small large) (frame : Heap large) (graph : Memory.Graph args)
    (inputs : Tuple (Val small) args) (initial : Heap small) :
    graph.denote (input e inputs) (extend e frame initial) = result e frame (graph.denote inputs initial) :=
  Proofs.denote_graph e frame graph inputs initial

variable {middle : Nat}

theorem input_trans (e : Embedding small middle) (f : Embedding middle large)
    (values : Tuple (Val small) args) :
    input (e.trans f) values = input f (input e values) :=
  Proofs.input_trans e f values

theorem restrict_trans (e : Embedding small middle) (f : Embedding middle large) (heap : Heap large) :
    restrict (e.trans f) heap = restrict e (restrict f heap) :=
  rfl

/-- Separate the unchanged cells outside the outer image from the
unchanged cells inside that image but outside the inner image. -/
theorem sameFrame_trans (e : Embedding small middle) (f : Embedding middle large)
    (initial final : Heap large) :
    SameFrame (e.trans f) initial final ↔
      SameFrame f initial final ∧ SameFrame e (restrict f initial) (restrict f final) :=
  Proofs.sameFrame_trans e f initial final

/-- Combine independent inner and outer frames for a composite embedding. -/
theorem extend_trans (e : Embedding small middle) (f : Embedding middle large)
    (inner : Heap middle) (outer : Heap large) (source : Heap small) :
    extend (e.trans f) (extend f outer inner) source = extend f outer (extend e inner source) :=
  Proofs.extend_trans e f inner outer source

/-- Updating the first image leaves the other image's restriction unchanged. -/
theorem restrict_extend_disjoint (e : Embedding small large) (f : Embedding middle large)
    (disjoint : DisjointImages e f) (frame : Heap large) (source : Heap small) :
    restrict f (extend e frame source) = restrict f frame :=
  Proofs.restrict_extend_disjoint e f disjoint frame source

/-- The two local results determine their own images, and every other
cell still has its initial value. -/
theorem extend_disjoint_spec (e : Embedding small large) (f : Embedding middle large)
    (disjoint : DisjointImages e f) (initial : Heap large) (left : Heap small) (right : Heap middle) :
    let final := extend f (extend e initial left) right
    restrict e final = left ∧ restrict f final = right ∧
      (∀ a, (¬ ∃ b, e b = a) → (¬ ∃ b, f b = a) → final a = initial a) :=
  Proofs.extend_disjoint_spec e f disjoint initial left right

end Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding
