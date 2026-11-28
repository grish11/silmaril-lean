module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits exit_type)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional
open Syntax (Ty Payload Expr Bindings Primitives emptyBindings model)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (denote_push fault_bind diverge_bind)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {n : Nat}

private theorem cast_val {A B : Syntax.Ty} (h : A = B) (a : Payload A) :
    (cast (congrArg Payload h) a).val = a.val := by
  cases h
  rfl

private noncomputable def graph (g : Table S R) (prim : Primitives Φ n) :
    Feedback.Run R Exits Unit (Fin n) :=
  feedbackRun (.native g.entryRegion) (fun i => .native (g.blocks i)) (model prim emptyBindings).raw

private noncomputable def after (g : Table S R) (prim : Primitives Φ n) :
    Fin Exits.length → Value Unit → Fin n → Behaviour Exits.length Unit (Fin n) :=
  let M := (model prim emptyBindings).raw
  fun j a t => denote (CFG.Dependent.Native.exitContinuation (Γ := []) (L := Exits) (Φ := Φ) g.selected j)
    (extendModel M a) t

private noncomputable def atPoint (g : Table S R) (prim : Primitives Φ n)
    (p : Feedback.Point R.length Unit (Fin n)) : Behaviour Exits.length Unit (Fin n) :=
  (Feedback.close (graph g prim) p).bind (after g prim)

private theorem at_agrees (g : Table S R) (prim : Primitives Φ n) (i : Fin R.length)
    (ranked : (g.ranks.get i).isSome = true) (a : Payload (R.get i))
    {Γ : List Syntax.Ty} (env : Bindings Γ) (s : Fin n) :
    Shape.denote ((g.extractAt i ranked).region S) (model prim env) s =
      atPoint g prim (.block i a.val s) := by
  rw [Table.extractAt]
  split
  · rename_i j rowEq
    have run : graph g prim (.block i a.val s) =
        WithTop.some {Feedback.external R Exits (.ret j .unit s)} := by
      change denote (.native (g.blocks i)) (extendModel (model prim emptyBindings).raw a.val) s = _
      rw [denote_push prim emptyBindings a, Table.blocks, rowEq]
      exact CFG.observe_jump (L := R ++ Exits) prim (emptyBindings.push a)
        (CFG.Dependent.exitLabel R Exits j)
        ((CFG.Dependent.external_type (R := R) (L := Exits) j).trans (exit_type j)) .unit s
    rw [atPoint, close_terminal run, return_bind]
    unfold after
    rw [CFG.Dependent.Native.denote_exitContinuation (Γ := [])]
    cases h : g.selected j
    · exact CFG.observe_jump (L := Exits) prim env j (exit_type j) .unit s
    · rfl
  · rename_i f arg next typed rowEq
    have run : graph g prim (.block i a.val s) =
        match prim f (arg.eval emptyBindings) s with
        | .ret b t =>
          let p := CFG.Dependent.unpack (cast (congrArg Payload (S.target f)) b)
          WithTop.some {Outcome.ret (Feedback.internal R Exits (next p.1)) p.2.val t}
        | .fault t => WithTop.some {Outcome.fault t}
        | .diverge => WithTop.some {Outcome.diverge} := by
      let target (j : Fin (S.replies f).length) := Feedback.internal R Exits (next j)
      let type (j : Fin (S.replies f).length) :=
        (CFG.Dependent.internal_type (L := Exits) (next j)).trans (typed j)
      let blockEnv := emptyBindings.push a
      change denote (.native (g.blocks i)) (extendModel (model prim emptyBindings).raw a.val) s = _
      rw [denote_push prim emptyBindings a, Table.blocks, rowEq]
      change Shape.denote (.native (CFG.Dependent.Native.packedRequestTo f
        (inContext arg) (S.target f) target type)) (model prim blockEnv) s = _
      rw [← CFG.Dependent.Native.packedRequestTo_agrees, CFG.Dependent.observe_packedRequestTo,
        inContext_eval]
      cases prim f (arg.eval emptyBindings) s <;> rfl
    have outgoing (j : Fin (S.replies f).length) : next j ∈ g.targets i := by
      rw [Table.targets, rowEq, Row.targets]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    let subtree (j : Fin (S.replies f).length) :=
      g.extractAt (next j) (Rank.ranked_successor g.targets ranked (outgoing j)).1
    change Shape.denote (.lsubst
      (CFG.Dependent.packedRequest f (inContext arg) (S.target f))
      (fun j => (subtree j).region S)) (model prim env) s = _
    rw [CFG.Dependent.observe_packedRequest_bind]
    change (match prim f ((inContext arg).eval env) s with
      | .ret b t => _
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge}) = _
    rw [inContext_eval]
    cases reply : prim f (arg.eval emptyBindings) s with
    | ret b t =>
      rw [reply] at run
      let p := CFG.Dependent.unpack (cast (congrArg Payload (S.target f)) b)
      have edge : next p.1 ∈ g.targets i := outgoing p.1
      let carried : Payload (R.get (next p.1)) := cast (congrArg Payload (typed p.1).symm) p.2
      have same : carried.val = p.2.val := cast_val (typed p.1).symm p.2
      apply Eq.trans (at_agrees g prim (next p.1) (Rank.ranked_successor g.targets ranked edge).1
        carried (env.push p.2) t)
      rw [same]
      unfold atPoint
      rw [close_branch (p := .block i a.val s) run]
    | fault t =>
      rw [reply] at run
      have done : Feedback.close (graph g prim) (.block i a.val s) = WithTop.some {Outcome.fault t} :=
        close_terminal (o := .fault t) run
      exact (congrArg (fun b => b.bind (after g prim)) done).trans (fault_bind t _) |>.symm
    | diverge =>
      rw [reply] at run
      have done : Feedback.close (graph g prim) (.block i a.val s) = WithTop.some {Outcome.diverge} :=
        close_terminal (o := .diverge) run
      exact (congrArg (fun b => b.bind (after g prim)) done).trans (diverge_bind _) |>.symm
termination_by (g.ranks.get i).getD 0
decreasing_by exact (Rank.ranked_successor g.targets ranked edge).2

theorem agrees (g : Table S R) (ok : g.entryCheck = true) (prim : Primitives Φ n) (s : Fin n) :
    Shape.denote ((g.extract ok).region S) (model prim emptyBindings) s =
      Shape.denote (CFG.Dependent.Native.withExitUB g.native g.selected) (model prim emptyBindings) s := by
  let a := g.input.eval emptyBindings
  have start : graph g prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R Exits g.entry) a.val s} :=
    CFG.observe_jump (L := R ++ Exits) prim emptyBindings (Feedback.internal R Exits g.entry)
      (CFG.Dependent.internal_type (L := Exits) g.entry) g.input s
  change _ = (denote (.native g.native) (model prim emptyBindings).raw s).bind (after g prim)
  unfold Table.native
  rw [← denote_native_feedback]
  change _ = atPoint g prim (.entry s)
  rw [atPoint, close_branch start]
  exact at_agrees g prim g.entry _ a emptyBindings s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction
