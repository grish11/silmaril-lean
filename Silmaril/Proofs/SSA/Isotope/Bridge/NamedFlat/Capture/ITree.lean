module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Packet

/-! # Capture destructuring and weak interaction-tree feedback -/

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat.Capture
open LambdaSSA
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction
open LambdaSSA.Region.InputDestructure
open Silmaril.Elgot.ITree (Tree iterate)
open LetCase.LocallyNameless (Tm)

universe u v w x

variable {τ : Type u} {F : Type v} {α Reply : Type w} {E : Type x → Type x}
variable (instr : Primitive E F α)

private theorem split_tree (Γ : List τ) (slot : Nat) (original ambient : Env α)
    (packet : ambient slot = packEnv Γ.length original) (r : Region F) :
    region instr ambient (split Γ slot r) = region instr (decoded Γ.length original ambient) r := by
  induction Γ generalizing slot original ambient with
  | nil => rfl
  | cons A Γ ih =>
    simp only [split, region, term, packet, List.length_cons, packEnv, pure_bind, decoded]
    exact ih 1 (original ∘ Nat.succ) _ rfl

private theorem unpack_tree {n labels : Nat} (a : Flat F labels n)
    (β : BoundCtx τ n) (original ambient : Env α) :
    region instr (extend ambient (packEnv n original)) (a.erase.packInputsDestructure β.toList) =
      region instr original a.erase := by
  let base := extend ambient (packEnv n original)
  have packet : base 0 = packEnv β.toList.length original := by
    rw [BoundCtx.length_toList]
    rfl
  unfold Region.packInputsDestructure
  rw [split_tree instr β.toList 0 original base packet]
  apply flat_rename_tree instr a
  intro i
  exact decoded_field β.toList original base (BoundCtx.length_toList β |>.symm ▸ i.isLt)

theorem packed_context_tree [TypeFormers τ] [HasTy F τ] {blocks exits n : Nat}
    {β : BoundCtx τ n} {g : FiniteCFG F blocks exits n} {R : Fin blocks → τ} {L : Fin exits → τ}
    (typed : g.HasType β R L) (ambient original : Env α) :
    region instr (extend ambient (packEnv n original))
        ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) =
      (region instr original g.erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) := by
  let base := extend ambient (packEnv n original)
  have packet : base 0 = packEnv β.toList.length original := by
    rw [BoundCtx.length_toList]
    rfl
  unfold Region.packInputsDestructure
  rw [split_tree instr β.toList 0 original base packet, region_renameVars instr _ (fun _ => rfl),
    FiniteCFG.packedExecution_tree]
  rw [cfg_tree_of_agree instr g (env := original)]
  intro i
  exact decoded_field β.toList original base (BoundCtx.length_toList β |>.symm ▸ i.isLt)

variable {blocks exits n : Nat} {β : BoundCtx τ n} {input : Tm Empty F 0}
  {g : FiniteCFG F blocks exits n} {closed : FiniteCFG F blocks exits 0}
  {ambient : Env α} {original : Reply → Env α} {produce : Tree E Reply}

theorem entry_tree (h : Closes β input g closed)
    (packet : term instr ambient (Morphism.CaseSSA.erase input) =
      (produce >>= fun reply => pure (packEnv n (original reply)))) :
    region instr ambient closed.entry.erase =
      (produce >>= fun reply => region instr (original reply) g.entry.erase) := by
  rw [h.entry]
  simp only [region, packet, bind_assoc, pure_bind]
  apply congrArg (fun continuation => produce >>= continuation)
  funext reply
  exact unpack_tree instr g.entry β (original reply) ambient

theorem graph_tree (h : Closes β input g closed)
    (packet : term instr ambient (Morphism.CaseSSA.erase input) =
      (produce >>= fun reply => pure (packEnv n (original reply)))) :
    region instr ambient closed.erase = (produce >>= fun reply => region instr (original reply) g.erase) := by
  let closedStep (p : BlockInput α blocks) :=
    region instr (extend ambient p.2) (closed.block p.1).erase >>= fun out =>
      pure (splitTransfer blocks out)
  let originalStep (reply : Reply) (p : BlockInput α blocks) :=
    region instr (extend (original reply) p.2) (g.block p.1).erase >>= fun out =>
      pure (splitTransfer blocks out)
  have steps (reply : Reply) : closedStep = originalStep reply := by
    funext p
    unfold closedStep originalStep
    rw [← h.block p.1, flat_tree_of_agree instr (closed.block p.1)
      (env' := extend ambient p.2) (env := extend (original reply) p.2)
      (Fin.cases rfl (fun i => i.elim0))]
  change (region instr ambient closed.entry.erase >>= fun out =>
      Sum.elim pure (iterate closedStep) (splitTransfer blocks out)) =
    (produce >>= fun reply => region instr (original reply) g.entry.erase >>= fun out =>
      Sum.elim pure (iterate (originalStep reply)) (splitTransfer blocks out))
  rw [entry_tree instr h packet, bind_assoc]
  apply congrArg (fun continuation => produce >>= continuation)
  funext reply
  rw [steps reply]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture
