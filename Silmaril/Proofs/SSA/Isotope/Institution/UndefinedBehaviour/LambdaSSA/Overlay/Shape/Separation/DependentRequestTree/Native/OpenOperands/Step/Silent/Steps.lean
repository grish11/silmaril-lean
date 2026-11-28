module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction hiding Table Row
open OpenOperands (Head StateTransition blockPoint)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet internal_type)
open Syntax (Expr Bindings Payload StatePrimitives model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag)
open Relation (ReflTransGen TransGen)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R Γ Δ : List Syntax.Ty} {A B C : Syntax.Ty} {σ : Type v}

private theorem eval_substitute (args : (i : Fin Δ.length) → Expr Γ (Δ.get i))
    (exp : Expr Δ A) (env : Bindings Γ) :
    (substitute args exp).eval env = exp.eval (fun i => (args i).eval env) := by
  induction exp <;> simp_all [substitute, Expr.eval]

private theorem specialize_head (selected : Tag → Bool) (arg : Expr [A, C] B)
    (row : OpenOperands.Row S R [B, C]) (env : Bindings [C]) (p : Payload A) :
    evalHead selected (env.push p) (specialize arg row) =
      evalHead selected (env.push (arg.eval (env.push p))) row := by
  cases row with
  | exit | diverge => rfl
  | request f operand next typed =>
    simp only [specialize, evalHead]
    rw [eval_substitute]
    have same : (fun i => (replacePacket arg i).eval (env.push p)) =
        env.push (arg.eval (env.push p)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    exact congrArg (fun env => evalHead selected env (.request f operand next typed)) same

/-- A witnessed singleton native internal transfer, including its final store. -/
abbrev Branch (f : Feedback.Run R Exits Unit σ) (p q : Feedback.Point R.length Unit σ) : Prop :=
  ∃ i a s, q = .block i a s ∧ f p = WithTop.some {Outcome.ret (Feedback.internal R Exits i) a s}

theorem close_along {f : Feedback.Run R Exits Unit σ} {p q : Feedback.Point R.length Unit σ}
    (path : ReflTransGen (Branch f) p q) : Feedback.close f p = Feedback.close f q := by
  induction path with
  | refl => rfl
  | tail _ branch ih =>
    obtain ⟨i, a, s, rfl, run⟩ := branch
    exact ih.trans (close_branch run)

theorem close_along_infinite {f : Feedback.Run R Exits Unit σ} (starts : Nat → Feedback.Point R.length Unit σ)
    (progress : ∀ n, TransGen (Branch f) (starts n) (starts (n + 1))) :
    Feedback.close f (starts 0) = WithTop.some {Outcome.diverge} := by
  obtain ⟨path, start, branches⟩ := Feedback.transitive_segments_path starts progress
  rw [← start]
  exact close_infinite_of_singleton path branches

theorem jump_branch (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    {i j : Fin R.length} {arg : Expr [R.get i, R.get g.entry] (R.get j)}
    (eq : g.row i = .jump j arg) (p : Payload (R.get i)) (s : σ) :
    Branch (g.feedback caller prim) (blockPoint ⟨i, p⟩ s)
      (blockPoint ⟨j, arg.eval ((g.visible.bindings caller).push p)⟩ s) := by
  refine ⟨j, (arg.eval ((g.visible.bindings caller).push p)).val, s, rfl, ?_⟩
  change denote (.native (g.blocks i))
    (extendModel (model prim (g.visible.bindings caller)).raw p.val) s = _
  rw [Syntax.denote_push, OpenOperands.Silent.Table.blocks, eq]
  exact CFG.observe_jump prim ((g.visible.bindings caller).push p) (Feedback.internal R Exits j)
    (internal_type j) arg s

private theorem guarded_step (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    {i : Fin R.length} {row : OpenOperands.Row S R [R.get i, R.get g.entry]}
    (eq : g.row i = .guarded row) (p : Payload (R.get i)) (s : σ) :
    g.feedback caller prim (blockPoint ⟨i, p⟩ s) =
      ((evalHead g.selected ((g.visible.bindings caller).push p) row).execute prim s).routed := by
  have visibleRow : g.visible.row i = row := by simp [Table.visible, eq]
  have old := g.visible.feedback_step caller prim ⟨i, p⟩ s
  have same : g.feedback caller prim (blockPoint ⟨i, p⟩ s) =
      g.visible.feedback caller prim (blockPoint ⟨i, p⟩ s) := by
    let M := extendModel (model prim (g.visible.bindings caller)).raw p.val
    change denote (.native (g.blocks i)) M s = denote (.native (g.visible.blocks i)) M s
    rw [OpenOperands.Silent.Table.blocks, eq, OpenOperands.Table.blocks, visibleRow]
    rfl
  have head : g.visible.head caller ⟨i, p⟩ = evalHead g.selected ((g.visible.bindings caller).push p) row := by
    rw [OpenOperands.Table.head, visibleRow]
    cases row <;> rfl
  rw [head] at old
  exact same.trans old

theorem resolve_segment (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (fuel : Nat) (i : Fin R.length) {row : OpenOperands.Row S R [R.get i, R.get g.entry]}
    (found : g.resolve fuel i = some row) (p : Payload (R.get i)) (s : σ) :
    ∃ q, ReflTransGen (Branch (g.feedback caller prim)) (blockPoint ⟨i, p⟩ s) q ∧
      g.feedback caller prim q = ((evalHead g.selected ((g.visible.bindings caller).push p) row).execute prim s).routed := by
  induction fuel generalizing i with
  | zero => cases found
  | succ fuel ih =>
    rw [Table.resolve] at found
    split at found
    · rename_i code eq
      obtain rfl := Option.some.inj found
      exact ⟨_, .refl, guarded_step g caller prim eq p s⟩
    · rename_i j arg eq
      cases tail : g.resolve fuel j with
      | none => simp [tail] at found
      | some code =>
        have target : specialize arg code = row := by simpa [tail] using found
        subst row
        let incoming := arg.eval ((g.visible.bindings caller).push p)
        obtain ⟨q, path, step⟩ := ih j tail incoming
        refine ⟨q, .head (jump_branch g caller prim eq p s) path, ?_⟩
        rwa [specialize_head]

theorem normalize_head (g : Table S R) (caller : Payload (R.get g.entry)) (p : Packet R) :
    g.normalize.head caller p =
      match g.resolve R.length p.1 with
      | some row => evalHead g.selected ((g.visible.bindings caller).push p.2) row
      | none => .diverge := by
  unfold OpenOperands.Table.head
  cases found : g.resolve R.length p.1 with
  | none => simp [found]
  | some row =>
    cases row <;> simp [found, evalHead, OpenOperands.Table.bindings]

theorem normalized_segment (g : Table S R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ)
    (resolves : g.resolve R.length p.1 ≠ none) :
    ∃ q, ReflTransGen (Branch (g.feedback caller prim)) (blockPoint p s) q ∧
      g.feedback caller prim q = ((g.normalize.head caller p).execute prim s).routed := by
  obtain ⟨i, a⟩ := p
  rw [normalize_head g caller]
  cases found : g.resolve R.length i with
  | none => exact (resolves found).elim
  | some row => exact resolve_segment g caller prim R.length i found a s

theorem native_close (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (s : σ) :
    denote (.native g.native) (model prim (g.visible.bindings caller)).raw s =
      Feedback.close (g.feedback caller prim) (blockPoint ⟨g.entry, caller⟩ s) := by
  unfold OpenOperands.Silent.Table.native
  rw [← denote_native_feedback]
  have start : g.feedback caller prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R Exits g.entry) caller.val s} :=
    CFG.observe_jump prim (g.visible.bindings caller) (Feedback.internal R Exits g.entry)
      (internal_type g.entry) (.var 0) s
  exact close_branch start

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
