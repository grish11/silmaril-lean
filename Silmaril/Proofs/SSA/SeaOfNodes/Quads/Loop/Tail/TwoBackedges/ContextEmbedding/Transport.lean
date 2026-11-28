module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! Composition and valuation pullback for factored embeddings. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts sortValue Val)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (pull_get)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U V : EntrySignature} {result : Width}

theorem trans_id (path : Embedding S T) : path.trans (.id T) = path := by
  induction path <;> simp only [Embedding.trans, *]

theorem trans_assoc (first : Embedding S T) (second : Embedding T U) (third : Embedding U V) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  induction first <;> simp only [Embedding.trans, *]

theorem portMap_trans (first : Embedding S T) (second : Embedding T U) {t : SeaOfNodes.Diamond.Ty Width}
    (port : Port (dataPorts S.regs) t) :
    (first.trans second).portMap t port = second.portMap t (first.portMap t port) := by
  induction first with
  | id _ => rfl
  | permute order rest ih => exact ih second _
  | weaken fresh rest ih => exact ih second (.tail port)

theorem portMap_injective (path : Embedding S T) (t : SeaOfNodes.Diamond.Ty Width) :
    Function.Injective (path.portMap t) := by
  induction path with
  | id _ => exact Function.injective_id
  | permute order rest ih => exact ih.comp (order t).injective
  | weaken fresh rest ih => exact ih.comp (fun _ _ eq => Port.tail.inj eq)

theorem reduct_trans (first : Embedding S T) (second : Embedding T U) (input : Valuation U) :
    (first.trans second).reduct input = first.reduct (second.reduct input) := by
  induction first <;> simp only [Embedding.trans, Embedding.reduct, *]

private theorem project_get {t head : SeaOfNodes.Diamond.Ty Width}
    {ports : List (SeaOfNodes.Diamond.Ty Width)}
    (input : Tuple (Val Word) (head :: ports)) (port : Port ports t) :
    (Weakening.project input).get port = input.get (.tail port) := by
  cases input
  rfl

theorem reduct_get (path : Embedding S T) (input : Valuation T) {t : SeaOfNodes.Diamond.Ty Width}
    (port : Port (dataPorts S.regs) t) :
    (path.reduct input).get port = input.get (path.portMap t port) := by
  induction path with
  | id _ => rfl
  | permute order rest ih =>
    exact (pull_get order (rest.reduct input) port).trans (ih input (order t port))
  | weaken fresh rest ih =>
    exact (project_get (rest.reduct input) port).trans (ih input (.tail port))

theorem reduct_congr (first second : Embedding S T)
    (agrees : ∀ t p, first.portMap t p = second.portMap t p) (input : Valuation T) :
    first.reduct input = second.reduct input := by
  rw [← Quads.tabulate_get_eq (first.reduct input), ← Quads.tabulate_get_eq (second.reduct input)]
  apply congrArg (Quads.tabulate (dataPorts S.regs))
  funext t port
  rw [reduct_get, reduct_get, agrees]

theorem insertionOrder_fresh (fresh : ValueSort Width) (regs : List (ValueSort Width))
    (pos : Fin (regs.length + 1)) :
    slot ((insertionOrder fresh regs pos) (.value fresh) .head) = pos.val := by
  induction regs with
  | nil => exact Fin.cases rfl (fun i => i.elim0) pos
  | cons sort rest ih =>
    refine Fin.cases rfl (fun i => ?_) pos
    exact congrArg (· + 1) (ih i)

theorem reduct_insertValue (S : EntrySignature) (fresh : ValueSort Width) (pos : Fin (S.regs.length + 1))
    (value : sortValue Word fresh) (input : Valuation S) :
    (insert S fresh pos).reduct (insertValue fresh pos value input) = input :=
  congrArg (Weakening.project (F := Val Word) (head := RVSDG.PortType.value fresh) (tail := dataPorts S.regs))
    (Reindex.pull_push (F := Val Word) (insertionOrder fresh S.regs pos) (.cons value input))

theorem mapGenerated_lower (path : Embedding S T) (p : AdmittedAt S result) :
    path.mapGenerated (Generated.lower p) = Generated.lower (path.mapAdmitted p) := by
  induction path with
  | id _ => rfl
  | permute order rest ih => exact ih _
  | weaken fresh rest ih => exact ih _

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Proofs
