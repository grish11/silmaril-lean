module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)
open Silmaril.Elgot (iter flatten flattenBody)
open Silmaril.Elgot.ITree (Tree diverge_bind iterate_fixpoint iterate_uniformity iterate_codiagonal)

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

private def phaseTransfer (out : Transfer α ⊕ BlockInput α (blocks + 1)) :
    (Transfer α ⊕ BlockInput α (blocks + 1)) ⊕ BlockInput α (blocks + 1) :=
  match out with
  | .inr next => if next.1.val < blocks then .inl out else .inr next
  | .inl ret => .inl (.inl ret)

private theorem phase_old (out : Transfer α ⊕ BlockInput α blocks) :
    phaseTransfer (out.map id embed) = .inl (out.map id embed) := by
  cases out with
  | inl ret => rfl
  | inr next => exact ite_eq_left next.1.isLt

private theorem phase_fresh (payload : Value α) :
    phaseTransfer (.inr (Fin.last blocks, payload)) = .inr (Fin.last blocks, payload) :=
  ite_eq_right (Nat.lt_irrefl blocks)

private theorem flatten_phase (out : Transfer α ⊕ BlockInput α (blocks + 1)) :
    flatten (phaseTransfer out) = out := by
  cases out with
  | inl ret => rfl
  | inr next => by_cases old : next.1.val < blocks <;> simp [phaseTransfer, flatten, old]

private noncomputable def step (raw : Primitive Events F α) (env : Env α)
    (g : FiniteCFG F blocks exits n) (p : BlockInput α blocks) :
    Tree Events (Transfer α ⊕ BlockInput α blocks) :=
  region raw (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)

private noncomputable def phased (f : BlockInput α (blocks + 1) →
    Tree Events (Transfer α ⊕ BlockInput α (blocks + 1))) (p : BlockInput α (blocks + 1)) :=
  f p >>= fun out => pure (phaseTransfer out)

private theorem phase_iter (f : BlockInput α (blocks + 1) →
    Tree Events (Transfer α ⊕ BlockInput α (blocks + 1))) :
    iter (iter (phased f)) = iter f := by
  rw [iterate_codiagonal]
  congr 1
  funext p
  change ((f p >>= fun out => pure (phaseTransfer out)) >>= fun out => pure (flatten out)) = f p
  simp only [bind_assoc, pure_bind, flatten_phase, bind_pure]

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
  unfold phased
  rw [continuation_step]
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
  rw [congrFun (iterate_fixpoint (phased (step raw env (graph s)))) (embed p)]
  change (((region raw (extend env p.2) ((graph s).block p.1.castSucc).erase >>= _) >>= _) >>= _) =
    ((region raw (extend env p.2) (g.block p.1).erase >>= _) >>= _)
  simp only [bind_assoc, pure_bind]
  change (region raw (extend env p.2) ((graph s).block p.1.castSucc).erase >>= after) =
    (region raw (extend env p.2) (g.block p.1).erase >>= before)
  by_cases selected : p.1 = s.selected
  · simp only [graph, Fin.lastCases_castSucc, selected, ↓reduceIte]
    rw [s.readback]
    simp only [Arm.dispatch, Arm.source, Flat.erase, region, bind_assoc]
    apply bind_congr
    intro v
    cases v <;> simp only [diverge_bind]
    next payload =>
      simp only [term, erase, Fin.val_zero, pure_bind]
      have fresh : splitTransfer (blocks + 1)
          (blocks, .pair p.2 payload) = .inr (Fin.last blocks, .pair p.2 payload) := by
        simp [splitTransfer]
        rfl
      change after (blocks, .pair p.2 payload) = _
      simp only [after, fresh, phase_fresh, Sum.elim_inr, next, continuation_iter, Flat.erase, region, bind_assoc, before]
    next payload =>
      exact renamed_then raw _ s.arm.bypass _ before after relocated
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
    rw [pure_bind, phase_iter] at agree
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
