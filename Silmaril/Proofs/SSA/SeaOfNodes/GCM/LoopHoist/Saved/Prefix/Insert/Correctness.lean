module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input Γ args : List Width} {w : Width}
variable {leading : Prefix Input Γ} {op : TargetOp args w} {operands : Operands Γ args}
variable {trailing : Nat} {edit : Insertion Input Γ w}

theorem insert?_length (done : leading.insert? op trailing operands = some edit) :
    edit.physical.length = Γ.length + 1 := by
  induction trailing generalizing Γ with
  | zero => cases done; rfl
  | succ trailing ih =>
    cases leading with
    | nil => cases done
    | snoc prior later laterOperands =>
      obtain ⟨earlier, _, next⟩ := Option.bind_eq_some_iff.mp done
      obtain ⟨inner, inserted, result⟩ := Option.bind_eq_some_iff.mp next
      cases result
      exact congrArg (· + 1) (ih inserted)

theorem insert?_indices (done : leading.insert? op trailing operands = some edit) :
    edit.inserted.index = trailing ∧
    ∀ {width} (ref : Var Γ width),
      (edit.previous ref).index = if ref.index < trailing then ref.index else ref.index + 1 := by
  induction trailing generalizing Γ with
  | zero =>
    cases done
    exact ⟨rfl, fun ref => by simp [Var.index]⟩
  | succ trailing ih =>
    cases leading with
    | nil => cases done
    | snoc prior later laterOperands =>
      obtain ⟨earlier, _, next⟩ := Option.bind_eq_some_iff.mp done
      obtain ⟨inner, inserted, result⟩ := Option.bind_eq_some_iff.mp next
      cases result
      obtain ⟨position, remap⟩ := ih inserted
      refine ⟨congrArg (· + 1) position, ?_⟩
      intro width ref
      cases ref with
      | here => simp [under, Var.index]
      | there ref =>
        simp only [under, Var.index, remap ref]
        by_cases before : ref.index < trailing
        · simp [before, Nat.succ_lt_succ_iff]
        · simp [before, Nat.succ_lt_succ_iff]

private theorem beforeBinding_agree {later : Width} (old : Env Γ) (value : BitVec later.val) :
    CapturesAgree beforeBinding (.cons value old) old := by
  intro width ref captured found
  cases ref with
  | here => cases found
  | there ref => cases found; rfl

theorem insert?_eval (done : leading.insert? op trailing operands = some edit) (input : Env Input) :
    ∀ {width} (ref : Var (w :: Γ) width),
      (edit.leading.eval input).get (edit.toPhysical ref) =
        (Env.cons (evalOp op (operands.eval (leading.eval input))) (leading.eval input)).get ref := by
  induction trailing generalizing Γ with
  | zero =>
    cases done
    intro width ref
    cases ref <;> rfl
  | succ trailing ih =>
    cases leading with
    | nil => cases done
    | snoc prior later laterOperands =>
      obtain ⟨earlier, captured, next⟩ := Option.bind_eq_some_iff.mp done
      obtain ⟨inner, inserted, result⟩ := Option.bind_eq_some_iff.mp next
      cases result
      have same {width : Width} (ref : Var (w :: _) width) := ih inserted ref
      have sameEarlier := evalCaptureOrigins beforeBinding operands captured _ _
        (beforeBinding_agree (prior.eval input) (evalOp later (laterOperands.eval (prior.eval input))))
      intro width ref
      cases ref with
      | here =>
        simpa only [Insertion.toPhysical, replaceBinding, Prefix.eval, Env.get, sameEarlier]
          using same (Var.here : Var (w :: _) w)
      | there ref =>
        cases ref with
        | here =>
          simp only [Insertion.toPhysical, replaceBinding, under, Prefix.eval, Env.get]
          rw [evalRenameOperands inner.previous _ _ (fun ref => same (.there ref))]
        | there ref =>
          exact same (.there ref)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix
