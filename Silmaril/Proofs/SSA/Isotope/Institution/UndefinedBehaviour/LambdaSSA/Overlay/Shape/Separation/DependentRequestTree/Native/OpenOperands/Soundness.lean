module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits exit_type resultBehaviour)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional
open Syntax (Payload Primitives model)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (denote_push fault_bind diverge_bind)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {n : Nat}

private theorem cast_val {A B : Syntax.Ty} (h : A = B) (a : Payload A) :
    (cast (congrArg Payload h) a).val = a.val := by
  cases h
  rfl

private noncomputable def graph (g : Table S R) (input : Payload (R.get g.entry))
    (prim : Primitives Φ n) : Feedback.Run R Exits Unit (Fin n) :=
  feedbackRun (.native g.entryRegion) (fun i => .native (g.blocks i)) (model prim (g.bindings input)).raw

private noncomputable def after (g : Table S R) (input : Payload (R.get g.entry))
    (prim : Primitives Φ n) : Fin Exits.length → Value Unit → Fin n → Behaviour Exits.length Unit (Fin n) :=
  let M := (model prim (g.bindings input)).raw
  fun j a t => denote (CFG.Dependent.Native.exitContinuation (Γ := [R.get g.entry]) (L := Exits)
    (Φ := Φ) g.selected j) (extendModel M a) t

private noncomputable def atPoint (g : Table S R) (input : Payload (R.get g.entry))
    (prim : Primitives Φ n) (p : Feedback.Point R.length Unit (Fin n)) : Behaviour Exits.length Unit (Fin n) :=
  (Feedback.close (graph g input prim) p).bind (after g input prim)

private theorem expand_agrees (g : Table S R) (input : Payload (R.get g.entry)) (prim : Primitives Φ n)
    (fuel : Nat) (i : Fin R.length) (ranked : (g.ranks.get i).isSome = true)
    (bound : (g.ranks.get i).getD 0 < fuel) (incoming : Payload (R.get i)) (s : Fin n) :
    resultBehaviour ((g.expand input fuel i ranked bound incoming).execute prim s) =
      atPoint g input prim (.block i incoming.val s) := by
  induction fuel generalizing i s with
  | zero => exact (Nat.not_lt_zero _ bound).elim
  | succ fuel ih =>
    rw [Table.expand]
    split
    · rename_i j rowEq
      have run : graph g input prim (.block i incoming.val s) =
          WithTop.some {Feedback.external R Exits (.ret j .unit s)} := by
        change denote (.native (g.blocks i)) (extendModel (model prim (g.bindings input)).raw incoming.val) s = _
        rw [denote_push prim _ incoming, Table.blocks, rowEq]
        exact CFG.observe_jump (L := R ++ Exits) prim ((g.bindings input).push incoming)
          (CFG.Dependent.exitLabel R Exits j)
          ((CFG.Dependent.external_type (R := R) (L := Exits) j).trans (exit_type j)) .unit s
      rw [atPoint, close_terminal run, return_bind]
      unfold after
      rw [CFG.Dependent.Native.denote_exitContinuation (Γ := [R.get g.entry])]
      cases marked : g.selected j <;> rfl
    · rename_i f arg next typed rowEq
      let env := (g.bindings input).push incoming
      have run : graph g input prim (.block i incoming.val s) =
          match prim f (arg.eval env) s with
          | .ret b t =>
            let p := CFG.Dependent.unpack (cast (congrArg Payload (S.target f)) b)
            WithTop.some {Outcome.ret (Feedback.internal R Exits (next p.1)) p.2.val t}
          | .fault t => WithTop.some {Outcome.fault t}
          | .diverge => WithTop.some {Outcome.diverge} := by
        let target (j : Fin (S.replies f).length) := Feedback.internal R Exits (next j)
        let type (j : Fin (S.replies f).length) :=
          (CFG.Dependent.internal_type (L := Exits) (next j)).trans (typed j)
        change denote (.native (g.blocks i)) (extendModel (model prim (g.bindings input)).raw incoming.val) s = _
        rw [denote_push prim _ incoming, Table.blocks, rowEq]
        change Shape.denote (.native (CFG.Dependent.Native.packedRequestTo f arg
          (S.target f) target type)) (model prim env) s = _
        rw [← CFG.Dependent.Native.packedRequestTo_agrees, CFG.Dependent.observe_packedRequestTo]
        cases prim f (arg.eval env) s <;> rfl
      rw [Tree.execute]
      cases reply : prim f (arg.eval env) s with
      | ret b t =>
        rw [reply] at run
        let p := CFG.Dependent.unpack (cast (congrArg Payload (S.target f)) b)
        have edge : next p.1 ∈ g.targets i := by
          rw [Table.targets, rowEq, Row.targets]
          exact List.mem_ofFn.mpr ⟨p.1, rfl⟩
        have successor := Rank.ranked_successor g.targets ranked edge
        let carried : Payload (R.get (next p.1)) := cast (congrArg Payload (typed p.1).symm) p.2
        have same : carried.val = p.2.val := cast_val (typed p.1).symm p.2
        apply Eq.trans (ih (next p.1) successor.1
          (successor.2.trans_le (Nat.le_of_lt_succ bound)) carried t)
        rw [same]
        unfold atPoint
        rw [close_branch (p := .block i incoming.val s) run]
      | fault t =>
        rw [reply] at run
        have stop : Feedback.close (graph g input prim) (.block i incoming.val s) = WithTop.some {Outcome.fault t} :=
          close_terminal (o := .fault t) run
        exact ((congrArg (fun b => b.bind (after g input prim)) stop).trans (fault_bind t _)).symm
      | diverge =>
        rw [reply] at run
        have stop : Feedback.close (graph g input prim) (.block i incoming.val s) = WithTop.some {Outcome.diverge} :=
          close_terminal (o := .diverge) run
        exact ((congrArg (fun b => b.bind (after g input prim)) stop).trans (diverge_bind _)).symm

theorem agrees (g : Table S R) (ok : g.entryCheck = true) (input : Payload (R.get g.entry))
    (prim : Primitives Φ n) (s : Fin n) :
    resultBehaviour ((g.extract ok input).execute prim s) =
      Shape.denote (CFG.Dependent.Native.withExitUB g.native g.selected) (model prim (g.bindings input)) s := by
  have start : graph g input prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R Exits g.entry) input.val s} :=
    CFG.observe_jump (L := R ++ Exits) prim (g.bindings input) (Feedback.internal R Exits g.entry)
      (CFG.Dependent.internal_type (L := Exits) g.entry) (.var 0) s
  change _ = (denote (.native g.native) (model prim (g.bindings input)).raw s).bind (after g input prim)
  unfold Table.native
  rw [← denote_native_feedback]
  change _ = atPoint g input prim (.entry s)
  rw [atPoint, close_branch start]
  exact expand_agrees g input prim _ g.entry _ _ input s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
