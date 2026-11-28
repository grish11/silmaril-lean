module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Row assign)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe w
variable {V W K J : Type w} [DecidableEq K] [DecidableEq J] (plan : Plan V W K J)

omit [DecidableEq J] in
private theorem rekey_injective (target : K) : Function.Injective (plan.rekey target) := by
  intro a b equal
  by_cases ha : plan.selected a target <;> by_cases hb : plan.selected b target
  · exact (ha.1).trans hb.1.symm
  · cases b with
    | none => simp [Plan.rekey, ha, hb] at equal
    | some b => simp [Plan.rekey, ha, hb, Ne.symm (plan.fresh b)] at equal
  · cases a with
    | none => simp [Plan.rekey, ha, hb] at equal
    | some a => simp [Plan.rekey, ha, hb, plan.fresh a] at equal
  · exact Option.map_injective plan.label.injective (by simpa [Plan.rekey, ha, hb] using equal)

private theorem lookup_column (target : K) (pred : Option K) (entries : List (Option K × Val V)) :
    (entries.map fun (k, value) => (plan.rekey target k, value.rename plan.register)).lookup
        (plan.rekey target pred) =
      (entries.lookup pred).map (Val.rename plan.register) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases hit : pred = key
    · subst key
      simp
    · have missed := beq_eq_false_iff_ne.mpr hit
      have mappedMiss := beq_eq_false_iff_ne.mpr (fun equal => hit (rekey_injective plan target equal))
      simp only [List.map_cons, List.lookup_cons, missed, mappedMiss, ih]

theorem operand_rename (target : K) (pred : Option K) (row : Row V K) :
    (plan.renameRow target row).operand (plan.rekey target pred) =
      (row.operand pred).rename plan.register := by
  unfold Plan.renameRow Row.operand
  rw [lookup_column]
  cases row.incoming.lookup pred <;> rfl

universe v
variable {F : Type v}

private theorem lookup_forwardAt_other (pred : Option K) (target : K) :
    (plan.forwardAt (F := F) pred).lookup (plan.label target) = none := by
  by_cases selected : pred = plan.predecessor
  · simp [Plan.forwardAt, selected, plan.fresh target]
  · simp [Plan.forwardAt, selected]

theorem lookup_renamed (source : Graph V K F) (target : K) :
    (plan.rewrite source).blocks.lookup (plan.label target) =
      (source.blocks.lookup target).map (plan.renameBlock target) := by
  change (plan.forwardAt none ++ source.blocks.flatMap _).lookup (plan.label target) = _
  rw [List.lookup_append, lookup_forwardAt_other, Option.none_or]
  induction source.blocks with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨key, block⟩ := entry
    simp only [List.flatMap_cons, List.append_assoc]
    rw [List.lookup_append, lookup_forwardAt_other, Option.none_or]
    by_cases same : target = key
    · subst key
      simp
    · have missed := beq_eq_false_iff_ne.mpr same
      have mappedMiss := beq_eq_false_iff_ne.mpr (fun equal => same (plan.label.injective equal))
      simp only [List.cons_append, List.nil_append, List.lookup_cons, missed, mappedMiss, ih]

theorem lookup_forward (source : Graph V K F) (edge : plan.hasEdge source = true) :
    (plan.rewrite source).blocks.lookup plan.forward = some plan.forwardBlock := by
  cases selected : plan.predecessor with
  | none =>
    simp [Plan.rewrite, Plan.forwardAt, selected]
  | some pred =>
    have present : (source.blocks.lookup pred).isSome = true := by
      cases h : source.blocks.lookup pred <;> simp_all [Plan.hasEdge]
    have empty : plan.forwardAt (F := F) none = [] := by simp [Plan.forwardAt, selected]
    change (plan.forwardAt none ++ source.blocks.flatMap _).lookup plan.forward = _
    rw [empty, List.nil_append]
    generalize source.blocks = blocks at *
    induction blocks with
    | nil => simp at present
    | cons entry entries ih =>
      obtain ⟨key, block⟩ := entry
      by_cases hit : key = pred
      · subst key
        simp [Plan.forwardAt, selected]
      · have missesForward := beq_eq_false_iff_ne.mpr (Ne.symm (plan.fresh key))
        have missed := beq_eq_false_iff_ne.mpr (Ne.symm hit)
        have noPrefix : plan.forwardAt (F := F) (some key) = [] := by
          simp [Plan.forwardAt, selected, hit]
        simp only [List.flatMap_cons, noPrefix, List.nil_append, List.cons_append, List.lookup_cons,
          missesForward]
        apply ih
        simpa only [List.lookup_cons, missed] using present


section Evaluation

variable {M : Type w → Type w} {α : Type w} [Monad M]
  [DecidableEq V] [DecidableEq W] (model : Model F M α)

omit [DecidableEq K] [DecidableEq J] [Monad M] in
private theorem update {β : Type w} (store : V → β) (x : V) (value : β) :
    upd (plan.renameStore store) (plan.register x) value =
      plan.renameStore (upd store x value) := by
  funext y
  obtain ⟨y, rfl⟩ := plan.register.surjective y
  simp [Plan.renameStore, upd]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
omit [Monad M] in
private theorem val_eval (store : V → α) (value : Val V) :
    (value.rename plan.register).eval model (plan.renameStore store) =
      value.eval model store := by
  induction value with
  | var x => simp [Val.rename, Val.eval, Plan.renameStore]
  | unit => rfl
  | pair a b ihA ihB => simp only [Val.rename, Val.eval, ihA, ihB]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem op_eval (store : V → α) (op : Op V F) :
    (op.rename plan.register).eval model (plan.renameStore store) =
      op.eval model store := by
  cases op <;> simp [Op.rename, Op.eval, val_eval]

omit [DecidableEq K] [DecidableEq J] in
private theorem term_exec {β : Type w} (route : Option K → Option J)
    (next : Option J → α → (W → α) → M β)
    (term : CFG.Term V (Option K) F) (store : V → α) :
    (plan.renameTerm route term).exec model next (plan.renameStore store) =
      term.exec model (fun k a s => next (route k) a (plan.renameStore s)) store := by
  induction term generalizing store with
  | br key value => simp [Plan.renameTerm, CFG.Term.exec, val_eval]
  | case op x left y right ihL ihR =>
    simp only [Plan.renameTerm, CFG.Term.exec, op_eval, update]
    congr 1
    funext branch
    cases branch <;> simp [ihL, ihR]

omit [DecidableEq K] [DecidableEq J] in
theorem exec_rename {β : Type w} (route : Option K → Option J)
    (next : Option J → α → (W → α) → M β)
    (body : CFG.Body V (Option K) F) (store : V → α) :
    (plan.renameBody route body).exec model next (plan.renameStore store) =
      body.exec model (fun k a s => next (route k) a (plan.renameStore s)) store := by
  induction body generalizing store with
  | term term => exact term_exec plan model route next term store
  | let1 x op body ih => simp [Plan.renameBody, CFG.Body.exec, op_eval, update, ih]
  | let2 x y op body ih => simp [Plan.renameBody, CFG.Body.exec, op_eval, update, ih]

omit [Monad M] in
theorem assign_rename (target : K) (pred : Option K) (rows : List (Row V K))
    (snapshot store : V → α) :
    assign model (plan.rekey target pred) (plan.renameStore snapshot)
        (rows.map (plan.renameRow target)) (plan.renameStore store) =
      plan.renameStore (assign model pred snapshot rows store) := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, assign, operand_rename plan, val_eval]
    change assign model _ _ _ (upd (plan.renameStore store) (plan.register row.dst) _) = _
    rw [update, ih]

end Evaluation

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Split
