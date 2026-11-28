module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms

import Silmaril.Semantics.Elgot.Partition.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)
open Silmaril.Elgot (iter partitionTransfer partitionStepByTarget iter_partition_target)
open Silmaril.Elgot.ITree (Tree diverge_bind iterate_fixpoint iterate_uniformity)

universe u v w
variable {Events : Type u → Type u} {F : Type v} {α : Type w} {blocks exits labels labelCount n : Nat}

private theorem renamed_then (raw : Primitive Events F α) (env : Env α) (t : Flat F labels n)
    (ρ : Fin labels → Fin labelCount) {B : Type w} (before after : Transfer α → Tree Events B)
    (agree : ∀ i : Fin labels, ∀ v, after ((ρ i).val, v) = before (i.val, v)) :
    (region raw env (renameLabels ρ t).erase >>= after) =
      (region raw env t.erase >>= before) := by
  induction t generalizing env with
  | br i a => simp only [renameLabels, Flat.erase, region, bind_assoc, pure_bind, agree]
  | let₁ a t ih => simp only [renameLabels, Flat.erase, region, bind_assoc, ih]
  | let₂ a t ih =>
    simp only [renameLabels, Flat.erase, region, bind_assoc]
    apply bind_congr
    intro v
    cases v <;> first | exact ih _ | simp only [diverge_bind]
  | case a l r left right =>
    simp only [renameLabels, Flat.erase, region, bind_assoc]
    apply bind_congr
    intro v
    cases v <;> first | exact left _ | exact right _ | simp only [diverge_bind]

private def embed (p : BlockInput α blocks) : BlockInput α (blocks + 1) := (p.1.castSucc, p.2)

private theorem split_relocate (i : Fin (blocks + exits)) (v : Value α) :
    splitTransfer (blocks + 1) ((relocate blocks exits i).val, v) =
      (splitTransfer blocks (i.val, v)).map id embed := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have inside : j.val < blocks + 1 := by omega
    simp [relocate, splitTransfer, embed, j.isLt, inside]
    rfl
  · have outside : ¬ blocks + j.val < blocks := by omega
    have moved : ¬ blocks + 1 + j.val < blocks + 1 := by omega
    simp [relocate, splitTransfer, outside, moved]

private def isFresh (p : BlockInput α (blocks + 1)) : Bool := decide (blocks ≤ p.1.val)

private abbrev phaseTransfer (out : Transfer α ⊕ BlockInput α (blocks + 1)) :=
  partitionTransfer isFresh out

private theorem phase_old (out : Transfer α ⊕ BlockInput α blocks) :
    phaseTransfer (out.map id embed) = .inl (out.map id embed) := by
  cases out with
  | inl ret => rfl
  | inr next =>
    change partitionTransfer isFresh (.inr (embed next)) = .inl (.inr (embed next))
    simp [partitionTransfer, isFresh, embed, Nat.not_le_of_lt next.1.isLt]

private theorem phase_fresh (payload : Value α) :
    phaseTransfer (.inr (Fin.last blocks, payload)) = .inr (Fin.last blocks, payload) := by
  simp [phaseTransfer, partitionTransfer, isFresh]

private noncomputable def step (raw : Primitive Events F α) (env : Env α)
    (g : FiniteCFG F blocks exits n) (p : BlockInput α blocks) :
    Tree Events (Transfer α ⊕ BlockInput α blocks) :=
  region raw (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)

private noncomputable abbrev phased (f : BlockInput α (blocks + 1) →
    Tree Events (Transfer α ⊕ BlockInput α (blocks + 1))) :=
  partitionStepByTarget f isFresh

private theorem phased_apply (f : BlockInput α (blocks + 1) →
    Tree Events (Transfer α ⊕ BlockInput α (blocks + 1))) (p : BlockInput α (blocks + 1)) :
    phased f p = (f p >>= fun out => pure (phaseTransfer out)) := by
  simp only [phased, partitionStepByTarget, map_eq_pure_bind]

private theorem continuation_step (raw : Primitive Events F α) (env : Env α)
    {g : FiniteCFG F blocks exits n} (s : Selection g) (packet payload : Value α) :
    step raw env (graph s) (Fin.last blocks, .pair packet payload) =
      (region raw (extend (extend env packet) payload) (Flat.br s.arm.destination s.arm.operand).erase >>=
        fun out => pure ((splitTransfer blocks out).map id embed)) := by
  simp only [step, graph, Fin.lastCases_last, Arm.continuation, Flat.erase, region, erase, term, pure_bind]
  let env' := extend (extend (extend env (.pair packet payload)) packet) payload
  let original := extend (extend env packet) payload
  let ρ : Fin (n + 2) → Fin (n + 3) := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))
  have agree : ∀ i, env' (ρ i).val = original i.val := Fin.cases rfl (Fin.cases rfl fun _ => rfl)
  change ((term raw env' (erase (s.arm.operand.rename ρ)) >>= fun v =>
      pure ((relocate blocks exits s.arm.destination).val, v)) >>= _) = _
  rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw ρ agree]
  simp only [bind_assoc, pure_bind, split_relocate]
  rfl

private theorem continuation_iter (raw : Primitive Events F α) (env : Env α)
    {g : FiniteCFG F blocks exits n} (s : Selection g) (packet payload : Value α) :
    iter (phased (step raw env (graph s))) (Fin.last blocks, .pair packet payload) =
      (region raw (extend (extend env packet) payload) (Flat.br s.arm.destination s.arm.operand).erase >>=
        fun out => pure ((splitTransfer blocks out).map id embed)) := by
  rw [congrFun (iterate_fixpoint (phased (step raw env (graph s)))) (Fin.last blocks, .pair packet payload)]
  rw [phased_apply, continuation_step]
  simp only [bind_assoc, pure_bind, phase_old, Sum.elim_inl]

private theorem inner_old (raw : Primitive Events F α) (env : Env α)
    {g : FiniteCFG F blocks exits n} (s : Selection g) (p : BlockInput α blocks) :
    iter (phased (step raw env (graph s))) (embed p) =
      (step raw env g p >>= fun out => pure (out.map id embed)) := by
  let next := iter (phased (step raw env (graph s)))
  let after (out : Transfer α) := Sum.elim pure next (phaseTransfer (splitTransfer (blocks + 1) out))
  let before (out : Transfer α) := (pure ((splitTransfer blocks out).map id embed) :
    Tree Events (Transfer α ⊕ BlockInput α (blocks + 1)))
  have relocated (i : Fin (blocks + exits)) (v : Value α) :
      after ((relocate blocks exits i).val, v) = before (i.val, v) := by
    simp only [after, before, split_relocate, phase_old, Sum.elim_inl]
  rw [congrFun (iterate_fixpoint (phased (step raw env (graph s)))) (embed p), phased_apply]
  change (((region raw (extend env p.2) ((graph s).block p.1.castSucc).erase >>= _) >>= _) >>= _) =
    ((region raw (extend env p.2) (g.block p.1).erase >>= _) >>= _)
  simp only [bind_assoc, pure_bind]
  change (region raw (extend env p.2) ((graph s).block p.1.castSucc).erase >>= after) =
    (region raw (extend env p.2) (g.block p.1).erase >>= before)
  by_cases selected : p.1 = s.selected
  · simp only [graph, Fin.lastCases_castSucc, selected, ↓reduceIte]
    rw [s.readback]
    have active (payload : Value α) :
        after (blocks, .pair p.2 payload) =
          (region raw (extend (extend env p.2) payload) (Flat.br s.arm.destination s.arm.operand).erase >>=
            before) := by
      have fresh : splitTransfer (blocks + 1)
          (blocks, .pair p.2 payload) = .inr (Fin.last blocks, .pair p.2 payload) := by
        simp [splitTransfer]
        rfl
      simp only [after, fresh, phase_fresh, Sum.elim_inr, next, continuation_iter, Flat.erase, region, bind_assoc, before]
    cases side : s.arm.side <;>
      simp only [Arm.dispatch, Arm.source, Side.branch, side, Side.choose, Flat.erase, region, bind_assoc] <;>
      apply bind_congr <;> intro value <;> cases value <;> simp only [diverge_bind]
    · simp only [term, erase, Fin.val_zero, pure_bind]
      exact active _
    · exact renamed_then raw _ s.arm.bypass _ before after relocated
    · exact renamed_then raw _ s.arm.bypass _ before after relocated
    · simp only [term, erase, Fin.val_zero, pure_bind]
      exact active _
  · simp only [graph, Fin.lastCases_castSucc, selected, ↓reduceIte]
    exact renamed_then raw _ (g.block p.1) _ before after relocated

theorem graph_tree (raw : Primitive Events F α) (env : Env α)
    {g : FiniteCFG F blocks exits n} (s : Selection g) :
    region raw env (graph s).erase = region raw env g.erase := by
  let newStep := step raw env (graph s)
  have uniform := iterate_uniformity (step raw env g) (iter (phased newStep)) embed (by
    funext p
    change (step raw env g p >>= fun out => pure (out.map id embed)) =
      (pure (embed p) >>= iter (phased newStep))
    rw [pure_bind, inner_old])
  have loop (p : BlockInput α blocks) : iter newStep (embed p) = iter (step raw env g) p := by
    have agree := congrFun uniform p
    change iter (step raw env g) p = (pure (embed p) >>= iter (iter (phased newStep))) at agree
    rw [pure_bind, iter_partition_target newStep isFresh] at agree
    exact agree.symm
  change (region raw env (renameLabels (relocate blocks exits) g.entry).erase >>= fun out =>
    Sum.elim pure (iter newStep) (splitTransfer (blocks + 1) out)) =
    (region raw env g.entry.erase >>= fun out =>
      Sum.elim pure (iter (step raw env g)) (splitTransfer blocks out))
  apply renamed_then
  intro i v
  rw [split_relocate]
  cases splitTransfer blocks (i.val, v) with
  | inl ret => rfl
  | inr p => exact loop p

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
