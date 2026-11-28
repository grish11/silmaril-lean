module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.ITree

/-! # Effectful capture closure for named weak ITree execution -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.Elgot.ITree (Tree)
open LetCase.LocallyNameless (Tm)

universe u v w x

section Capture

variable {τ : Type u} {F : Type v} {α Reply : Type w} {Events : Type x → Type x}
  {blocks exits n : Nat} {β : BoundCtx τ n} {input : Tm Empty F 0}
  {g : FiniteCFG F blocks exits n} {closed : FiniteCFG F blocks exits 0}
  {ambient : Env α} {original : Reply → Env α} {produce : Tree Events Reply}

/-- Decoding the canonical capture record supplies the original slots to a
scoped flat region, as an equality of its complete weak trees. -/
theorem Capture.unpack_tree {labels : Nat} (instr : Primitive Events F α) (body : LambdaSSA.Flat F labels n)
    (context : BoundCtx τ n) (original ambient : Env α) :
    region instr (LambdaSSA.Semantics.extend ambient (Capture.packEnv n original))
      (body.erase.packInputsDestructure context.toList) = region instr original body.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.unpack_tree instr body context original ambient

/-- The capture expression runs the producer and packs its reply environment.
The erased decoder then gives the original entry tree for that reply. -/
theorem Capture.entry_tree (instr : Primitive Events F α) (closure : Capture.Closes β input g closed)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase input) =
        (produce >>= fun reply => pure (Capture.packEnv n (original reply)))) :
    region instr ambient closed.entry.erase =
      (produce >>= fun reply => region instr (original reply) g.entry.erase) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.entry_tree instr closure packet

/-- The producer's effects and continuations are preserved through feedback.
Each closed block uses only its incoming tagged packet, and the closure keeps
its erased body. -/
theorem Capture.graph_tree (instr : Primitive Events F α) (closure : Capture.Closes β input g closed)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase input) =
        (produce >>= fun reply => pure (Capture.packEnv n (original reply)))) :
    region instr ambient closed.erase = (produce >>= fun reply => region instr (original reply) g.erase) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.graph_tree instr closure packet

/-- Pass the exact capture record as the packed program's external input.
Decoding is pure and shares the decoded values with every block. The only
change to the resulting tree is the outward tag. -/
theorem Capture.packed_context_tree [TypeFormers τ] [HasTy F τ]
    (instr : Primitive Events F α) {R : Fin blocks → τ} {L : Fin exits → τ}
    (typed : g.HasType β R L) (ambient original : Env α) :
    region instr (LambdaSSA.Semantics.extend ambient (Capture.packEnv n original))
        ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) =
      (region instr original g.erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.packed_context_tree instr typed ambient original

end Capture

variable {Events : Type u → Type u} {F : Type v} {V K α Reply : Type (u + 1)}
  {n : Nat} [DecidableEq V] [DecidableEq K]

/-- With the accepted elaboration and typed capture closure of the generated
graph, the packed dispatcher runs the producer once. At each reply it has the
same tree as the named runner with matching version-zero captures, followed
by the dispatcher sum tag on the original exit payload. -/
theorem packed_run_tree {τ : Type w} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    (instr : Primitive Events F α) (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    {R : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → τ}
    {L : Fin exits.length → τ}
    {target : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}
    {closed : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length 0}
    {input : Tm Empty F 0} {ambient : Env α} {original : Reply → Env α}
    {produce : Tree Events Reply} (store : Reply → V × Nat → Value α)
    (accepted : compile source exits captures = some target)
    (inputs : ∀ reply (i : Fin n), original reply i.val = store reply (captures i, 0))
    (typed : closed.HasType .nil R L) (closure : Capture.Closes β input target closed)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase input) =
        (produce >>= fun reply => pure (Capture.packEnv n (original reply)))) :
    region instr ambient (FiniteCFG.packedExecutionRegion typed) =
      (produce >>= fun reply => CFG.Cyclic.runSSA (treeModel instr)
        (CFG.Cyclic.Versioning.compile source) (store reply) >>= fun p =>
          pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) := by
  rw [FiniteCFG.packedExecution_tree instr typed ambient, Capture.graph_tree instr closure packet, bind_assoc]
  apply congrArg (fun continuation => produce >>= continuation)
  funext reply
  rw [← compile_run_tree instr source exits captures accepted (store reply) (original reply) (inputs reply),
    bind_assoc]
  simp only [pure_bind]

/-- An admitted named graph also runs from an externally supplied record.
The record encodes the same version-zero captures as the initial named store.
The dispatcher preserves the visible tree and tags its outward transfer. -/
theorem packed_entry_run_tree {τ : Type w} [TypeFormers τ] [HasTy F τ] {β : BoundCtx τ n}
    (instr : Primitive Events F α) (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    {R : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → τ} {L : Fin exits.length → τ}
    {target : FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length exits.length n}
    (accepted : compile source exits captures = some target) (typed : target.HasType β R L)
    (store : V × Nat → Value α) (ambient original : Env α)
    (inputs : ∀ i : Fin n, original i.val = store (captures i, 0)) :
    region instr (LambdaSSA.Semantics.extend ambient (Capture.packEnv n original))
        ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) =
      (CFG.Cyclic.runSSA (treeModel instr) (CFG.Cyclic.Versioning.compile source) store >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) := by
  rw [Capture.packed_context_tree, ← compile_run_tree instr source exits captures accepted store original inputs,
    bind_assoc]
  simp only [pure_bind]

end Silmaril.Isotope.Bridge.NamedFlat
