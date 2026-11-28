module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
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
open CFG.Dependent (Packet internal_type external_type exitLabel unpack)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives Primitives model)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (denote_push fault_bind diverge_bind)

universe u x

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {states : Nat} {σ : Type x}

private theorem cast_value {A B : Syntax.Ty} (h : A = B) (p : Payload A) :
    (cast (congrArg Payload h) p).val = p.val := by
  cases h
  rfl

theorem raw_step (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (config : Packet R) (s : σ) :
    g.feedback caller prim (blockPoint config s) = ((g.head caller config).execute prim s).routed := by
  obtain ⟨i, incoming⟩ := config
  rw [Table.head]
  split
  · rename_i j rowEq
    change denote (.native (g.blocks i)) (extendModel (model prim (g.bindings caller)).raw incoming.val) s =
      WithTop.some {Feedback.external R Exits (.ret j .unit s)}
    rw [denote_push prim _ incoming, Table.blocks, rowEq]
    exact CFG.observe_jump (L := R ++ Exits) prim ((g.bindings caller).push incoming)
      (exitLabel R Exits j) ((external_type (R := R) (L := Exits) j).trans (exit_type j)) .unit s
  · rename_i rowEq
    change denote (.native (g.blocks i)) (extendModel (model prim (g.bindings caller)).raw incoming.val) s = _
    rw [denote_push prim _ incoming, Table.blocks, rowEq]
    exact CFG.Dependent.Native.observe_diverge prim ((g.bindings caller).push incoming) s
  · rename_i f arg next typed rowEq
    let env := (g.bindings caller).push incoming
    let target (j : Fin (S.replies f).length) := Feedback.internal R Exits (next j)
    let type (j : Fin (S.replies f).length) := (internal_type (L := Exits) (next j)).trans (typed j)
    change denote (.native (g.blocks i)) (extendModel (model prim (g.bindings caller)).raw incoming.val) s = _
    rw [denote_push prim _ incoming, Table.blocks, rowEq]
    change Shape.denote (.native (CFG.Dependent.Native.packedRequestTo f arg
      (S.target f) target type)) (model prim env) s = _
    rw [← CFG.Dependent.Native.packedRequestTo_agrees, CFG.Dependent.observe_packedRequestTo]
    rw [Head.execute]
    cases prim f (arg.eval env) s with
    | ret a t =>
      let reply := unpack (cast (congrArg Payload (S.target f)) a)
      exact congrArg (fun v : Value Unit => WithTop.some ({Outcome.ret (target reply.1) v t} : Set _))
        (cast_value (typed reply.1).symm reply.2).symm
    | fault | diverge => rfl

theorem step_iff (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (config : Packet R) (s : σ) (q : Feedback.Point R.length Unit (σ)) :
    Feedback.Step (g.feedback caller prim) (blockPoint config s) q ↔
      ∃ (next : Packet R) (t : σ),
        (g.head caller config).execute prim s = .repeat next t ∧ q = blockPoint next t := by
  have run := raw_step g caller prim config s
  cases current : (g.head caller config).execute prim s with
  | exit j selected t =>
    rw [current] at run
    simpa using no_step_of_terminal (L := Exits) (o := .ret j .unit t) (q := q) run
  | «repeat» next t =>
    rw [current] at run
    rw [step_of_branch_iff run]
    simp [blockPoint]
  | fault t =>
    rw [current] at run
    simpa using no_step_of_terminal (o := .fault t) (q := q) run
  | diverge =>
    rw [current] at run
    simpa using no_step_of_terminal (o := .diverge) (q := q) run

theorem observe_state_step (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (config : Packet R) (s : σ) :
    g.observeAt caller prim config s =
      match (g.head caller config).execute prim s with
      | .exit i selected t => if selected then ⊤ else WithTop.some {Outcome.ret i .unit t}
      | .repeat next t => g.observeAt caller prim next t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  have run := raw_step g caller prim config s
  cases current : (g.head caller config).execute prim s with
  | exit j selected t =>
    rw [current] at run
    rw [Table.observeAt, close_terminal run, return_bind, CFG.Dependent.Native.denote_exitContinuation]
    have marked : selected = g.selected j := by
      revert current
      unfold Table.head
      split
      · intro eq
        obtain ⟨rfl, rfl, _⟩ := StateTransition.exit.inj eq
        rfl
      · intro impossible
        cases impossible
      · rename_i f arg next typed _
        rw [Head.execute]
        split <;> simp
    rw [marked]
  | «repeat» next t =>
    rw [current] at run
    rw [Table.observeAt, close_branch run]
    rfl
  | fault t =>
    rw [current] at run
    rw [Table.observeAt, close_terminal (o := .fault t) run]
    exact fault_bind t _
  | diverge =>
    rw [current] at run
    rw [Table.observeAt, close_terminal (o := .diverge) run]
    exact diverge_bind _

theorem observe_step (g : Table S R) (caller : Payload (R.get g.entry)) (prim : Primitives Φ states)
    (config : Packet R) (s : Fin states) :
    g.observeAt caller prim config s =
      match (g.head caller config).execute prim s with
      | .exit i selected t => resultBehaviour (if selected then .ub else .ret i t)
      | .repeat next t => g.observeAt caller prim next t
      | .fault t => resultBehaviour (.fault t)
      | .diverge => resultBehaviour .diverge := by
  rw [observe_state_step]
  cases (g.head caller config).execute prim s with
  | exit i selected t => cases selected <;> rfl
  | «repeat» | fault | diverge => rfl

theorem observe_of_closed (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : Primitives Φ states) (config : Packet R) (s : Fin states) (outcome : Result 2 states)
    (closed : Feedback.close (g.feedback caller prim) (blockPoint config s) = resultBehaviour outcome) :
    g.observeAt caller prim config s = resultBehaviour (g.markExit outcome) := by
  rw [Table.observeAt, closed]
  cases outcome with
  | ret i t =>
    rw [resultBehaviour, return_bind, CFG.Dependent.Native.denote_exitContinuation]
    cases selected : g.selected i <;> simp [Table.markExit, selected, resultBehaviour]
  | fault t => exact fault_bind t _
  | diverge => exact diverge_bind _
  | ub => exact Behaviour.top_bind _

theorem observe_entry [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (checked : g.checkNative raw = true) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) s =
      g.observeAt caller prim ⟨g.entry, caller⟩ s := by
  rw [g.checked_reemission checked]
  have start : g.feedback caller prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R Exits g.entry) caller.val s} :=
    CFG.observe_jump (L := R ++ Exits) prim (g.bindings caller) (Feedback.internal R Exits g.entry)
      (internal_type (L := Exits) g.entry) (.var 0) s
  let M := (model prim (g.bindings caller)).raw
  change (denote (.native g.native) M s).bind _ = _
  unfold Table.native
  rw [← denote_native_feedback]
  change (Feedback.close (g.feedback caller prim) (.entry s)).bind _ = _
  rw [close_branch start]
  rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
