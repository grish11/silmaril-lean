module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
open Silmaril.Isotope.LambdaSSA (FiniteCFG Flat)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend extend_zero extend_succ)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LetCase.LocallyNameless (Tm)
open Silmaril.Elgot.ITree (diverge_bind iterate_uniformity)
open Morphism.CaseSSA (erase)

universe u v w
variable {Events : Type u → Type u} {F : Type v} {α : Type w} {blocks exits m k : Nat}

private def carried (blocks : Nat) (v : Value α) (p : Transfer α) : Transfer α :=
  (p.1, if p.1 < blocks then .pair p.2 v else p.2)

private theorem extend_agree {ρ : Fin m → Fin k} {env env' : Env α}
    (agree : ∀ i, env' (ρ i).val = env i.val) (v : Value α) :
    ∀ i, extend env' v (Tm.up ρ i).val = extend env v i.val :=
  Fin.cases rfl fun i => agree i

private theorem body_tree (raw : Primitive Events F α) (t : Flat F (blocks + exits) m)
    (ρ : Fin m → Fin k) (slot : Fin k) {env env' : Env α}
    (agree : ∀ i, env' (ρ i).val = env i.val) :
    region raw env' (body t ρ slot).erase =
      (region raw env t.erase >>= fun p => pure (carried blocks (env' slot.val) p)) := by
  induction t generalizing k env env' with
  | br i a =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have inside : (Fin.castAdd exits j).val < blocks := j.isLt
      simp only [body, Fin.addCases_left, Flat.erase, region, erase, term, bind_assoc, pure_bind, carried, inside, ↓reduceIte]
      rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw ρ agree]
    · have outside : ¬ (Fin.natAdd blocks j).val < blocks := by
        change ¬ blocks + j.val < blocks
        omega
      simp only [body, Fin.addCases_right, Flat.erase, region, bind_assoc, pure_bind, carried, outside, ↓reduceIte]
      rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw ρ agree]
  | let₁ a tail ih =>
    simp only [body, Flat.erase, region, bind_assoc]
    rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw ρ agree]
    exact congrArg _ (funext fun v => ih _ _ (extend_agree agree v))
  | let₂ a tail ih =>
    simp only [body, Flat.erase, region, bind_assoc]
    rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw ρ agree]
    congr 1
    funext v
    cases v <;> simp only [diverge_bind]
    next a b => exact ih _ _ (extend_agree (extend_agree agree a) b)
  | case a l r ihl ihr =>
    simp only [body, Flat.erase, region, bind_assoc]
    rw [LambdaSSA.Acyclic.FlatLetCase.operand_rename_tree raw ρ agree]
    congr 1
    funext v
    cases v <;> simp only [diverge_bind]
    next v => exact ihl _ _ (extend_agree agree v)
    next v => exact ihr _ _ (extend_agree agree v)

private theorem decoded_agree (env : Env α) (slot : Fin m) (v : Value α) :
    ∀ i, extend (extend (extend env (.pair v (env slot.val))) v) (env slot.val)
      (decodedIndex slot i).val = extend env v i.val :=
  Fin.cases rfl fun i => by
    by_cases same : i = slot
    · subst i
      simp only [decodedIndex, Fin.cases_succ, ↓reduceIte, Fin.val_zero, Fin.val_succ, extend_zero, extend_succ]
    · simp only [decodedIndex, Fin.cases_succ, same, ↓reduceIte, Fin.val_succ, extend_succ]

private theorem split_carried (v : Value α) (p : Transfer α) :
    splitTransfer blocks (carried blocks v p) =
      (splitTransfer blocks p).map id (fun q => (q.1, .pair q.2 v)) := by
  by_cases inside : p.1 < blocks <;> simp [splitTransfer, carried, inside]

private theorem row_tree (raw : Primitive Events F α) (g : FiniteCFG F blocks exits m)
    (slot : Fin m) (env : Env α) (p : BlockInput α blocks) :
    (region raw (extend env (.pair p.2 (env slot.val))) ((graph g slot).block p.1).erase >>=
      fun out => pure (splitTransfer blocks out)) =
    ((region raw (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)) >>=
      fun out => pure (out.map id (fun q => (q.1, .pair q.2 (env slot.val))))) := by
  simp only [graph, Flat.erase, region, erase, term, pure_bind]
  change (region raw (extend (extend (extend env (.pair p.2 (env slot.val))) p.2)
    (env slot.val)) (body (g.block p.1) (decodedIndex slot) 0).erase >>= _) = _
  rw [body_tree raw _ _ _ (decoded_agree env slot p.2), bind_assoc, bind_assoc]
  simp only [pure_bind, Fin.val_zero, extend_zero, split_carried]

theorem graph_tree (raw : Primitive Events F α) (g : FiniteCFG F blocks exits m)
    (slot : Fin m) (env : Env α) :
    region raw env (graph g slot).erase = region raw env g.erase := by
  let oldStep : BlockInput α blocks → _ := fun p =>
    region raw (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)
  let newStep : BlockInput α blocks → _ := fun p =>
    region raw (extend env p.2) ((graph g slot).block p.1).erase >>= fun out =>
      pure (splitTransfer blocks out)
  let inject : BlockInput α blocks → BlockInput α blocks := fun p => (p.1, .pair p.2 (env slot.val))
  have row (p : BlockInput α blocks) :
      newStep (inject p) = (oldStep p >>= fun out => pure (out.map id inject)) :=
    row_tree raw g slot env p
  have uniform := iterate_uniformity oldStep newStep inject (by
    funext p
    change (oldStep p >>= fun out => pure (out.map id inject)) = (pure (inject p) >>= newStep)
    rw [pure_bind, row])
  change (region raw env (body g.entry id slot).erase >>= fun out =>
    Sum.elim pure (Silmaril.Elgot.iter newStep) (splitTransfer blocks out)) =
    (region raw env g.entry.erase >>= fun out =>
      Sum.elim pure (Silmaril.Elgot.iter oldStep) (splitTransfer blocks out))
  rw [body_tree raw g.entry id slot (env := env) (env' := env) (fun _ => rfl), bind_assoc]
  simp only [pure_bind, split_carried]
  congr 1
  funext p
  cases h : splitTransfer blocks p with
  | inl => rfl
  | inr q =>
    have loop := congrFun uniform q
    change Silmaril.Elgot.iter oldStep q = (pure (inject q) >>= Silmaril.Elgot.iter newStep) at loop
    rw [pure_bind] at loop
    exact loop.symm

theorem graphList_entry_tree (raw : Primitive Events F α) (g : FiniteCFG F blocks exits m)
    (slots : List (Fin m)) (env : Env α) :
    region raw env (graphList g slots).entry.erase =
      (region raw env g.entry.erase >>= fun out =>
        pure (out.1, if out.1 < blocks then packValue env slots out.2 else out.2)) := by
  induction slots generalizing g with
  | nil =>
    simp only [graphList, packValue, List.foldl_nil, ite_self]
    exact (bind_pure _).symm
  | cons slot rest ih =>
    change region raw env (graphList (graph g slot) rest).entry.erase = _
    rw [ih]
    change (region raw env (body g.entry id slot).erase >>= _) = _
    rw [body_tree raw g.entry id slot (fun _ => rfl), bind_assoc]
    simp only [pure_bind, carried]
    apply bind_congr
    intro out
    by_cases inside : out.1 < blocks <;> simp [inside, packValue]

theorem graphList_row_tree (raw : Primitive Events F α) (g : FiniteCFG F blocks exits m)
    (slots : List (Fin m)) (env : Env α) (p : BlockInput α blocks) :
    (region raw (extend env (packValue env slots p.2)) ((graphList g slots).block p.1).erase >>=
      fun out => pure (splitTransfer blocks out)) =
    ((region raw (extend env p.2) (g.block p.1).erase >>= fun out => pure (splitTransfer blocks out)) >>=
      fun out => pure (out.map id (fun q => (q.1, packValue env slots q.2)))) := by
  induction slots generalizing g p with
  | nil =>
    simp only [graphList, packValue, List.foldl_nil, bind_assoc, pure_bind]
    congr 1
    funext out
    cases splitTransfer blocks out <;> rfl
  | cons slot rest ih =>
    simp only [graphList, packValue, List.foldl_cons]
    have tail := ih (graph g slot) (p.1, .pair p.2 (env slot.val))
    rw [graphList, packValue] at tail
    rw [tail, row_tree raw g slot env p]
    simp only [bind_assoc, pure_bind]
    congr 1
    funext out
    cases splitTransfer blocks out <;> rfl

theorem graphList_tree (raw : Primitive Events F α) (g : FiniteCFG F blocks exits m)
    (slots : List (Fin m)) (env : Env α) :
    region raw env (graphList g slots).erase = region raw env g.erase := by
  induction slots generalizing g with
  | nil => rfl
  | cons slot rest ih => exact (ih (graph g slot)).trans (graph_tree raw g slot env)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry
