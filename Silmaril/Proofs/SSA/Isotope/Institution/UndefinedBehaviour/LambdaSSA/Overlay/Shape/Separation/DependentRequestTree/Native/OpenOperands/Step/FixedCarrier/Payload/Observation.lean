module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Transport.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
open CFG.Dependent (Packet internal_type external_type exitLabel unpack)
open CFG.Dependent.Native (withExitUB denote_exitContinuation)
open ScheduleSearch (StateInventory)
open Syntax (Payload Primitives model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {A : Syntax.Ty}

private theorem cast_value {X Y : Syntax.Ty} (h : X = Y) (p : Payload X) :
    (cast (congrArg Payload h) p).val = p.val := by cases h; rfl

theorem returnPacket_value (g : Endpoint S R A) (caller : Payload (R.get g.control.entry))
    (p : Packet R) (i : Tag) :
    (g.returnPacket caller p i).2.val = ((g.output p.1).eval ((g.control.bindings caller).push p.2)).val :=
  cast_value (exit_type (A := A) i).symm _

theorem raw_step {σ : Type v} (g : Endpoint S R A)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (config : Packet R) (s : σ) :
    g.feedback caller prim (blockPoint config s) = g.route caller config ((g.control.head caller config).execute prim s) := by
  obtain ⟨i, incoming⟩ := config
  rw [Table.head]
  split
  · rename_i j rowEq
    change denote (.native (g.blocks i)) (extendModel (model prim (g.control.bindings caller)).raw incoming.val) s =
      WithTop.some {Feedback.external R (Exits A) (.ret j (g.returnPacket caller ⟨i, incoming⟩ j).2.val s)}
    rw [Syntax.denote_push prim _ incoming, Endpoint.blocks, rowEq, returnPacket_value]
    exact CFG.observe_jump (L := R ++ Exits A) prim ((g.control.bindings caller).push incoming)
      (exitLabel R (Exits A) j) ((external_type (R := R) (L := Exits A) j).trans (exit_type j)) (g.output i) s
  · rename_i rowEq
    change denote (.native (g.blocks i)) (extendModel (model prim (g.control.bindings caller)).raw incoming.val) s = _
    rw [Syntax.denote_push prim _ incoming, Endpoint.blocks, rowEq]
    exact CFG.Dependent.Native.observe_diverge prim ((g.control.bindings caller).push incoming) s
  · rename_i f arg next typed rowEq
    let env := (g.control.bindings caller).push incoming
    let target (j : Fin (S.replies f).length) := Feedback.internal R (Exits A) (next j)
    let type (j : Fin (S.replies f).length) := (internal_type (L := Exits A) (next j)).trans (typed j)
    change denote (.native (g.blocks i)) (extendModel (model prim (g.control.bindings caller)).raw incoming.val) s = _
    rw [Syntax.denote_push prim _ incoming, Endpoint.blocks, rowEq]
    change Shape.denote (.native (CFG.Dependent.Native.packedRequestTo f arg
      (S.target f) target type)) (model prim env) s = _
    rw [← CFG.Dependent.Native.packedRequestTo_agrees, CFG.Dependent.observe_packedRequestTo, Head.execute]
    cases prim f (arg.eval env) s with
    | ret a t =>
      let reply := unpack (cast (congrArg Payload (S.target f)) a)
      exact congrArg (fun v : Value Unit => WithTop.some ({Outcome.ret (target reply.1) v t} : Set _))
        (cast_value (typed reply.1).symm reply.2).symm
    | fault | diverge => rfl

theorem observe_entry_state [DecidableEq Φ] {σ : Type v} (g : Endpoint S R A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)) (readback : g.checkNative raw = true)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s =
      g.observeAt caller prim ⟨g.control.entry, caller⟩ s := by
  have same : raw = g.native := Subtype.ext (CFG.Dependent.Native.sameRegion_eq readback)
  subst raw
  have start : g.feedback caller prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R (Exits A) g.control.entry) caller.val s} :=
    CFG.observe_jump (L := R ++ Exits A) prim (g.control.bindings caller)
      (Feedback.internal R (Exits A) g.control.entry) (internal_type g.control.entry) (.var 0) s
  let M := (model prim (g.control.bindings caller)).raw
  change (denote (.native g.native) M s).bind _ = _
  unfold Endpoint.native
  rw [← denote_native_feedback]
  change (Feedback.close (g.feedback caller prim) (.entry s)).bind _ = _
  rw [close_branch start]
  change (Feedback.close (g.feedback caller prim) (blockPoint ⟨g.control.entry, caller⟩ s)).bind _ = _
  rfl

theorem observe_state_step {σ : Type v} (g : Endpoint S R A)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (p : Packet R) (s : σ) :
    g.observeAt caller prim p s =
      match (g.control.head caller p).execute prim s with
      | .exit i _ t => if g.control.selected i then ⊤ else WithTop.some {Outcome.ret i (g.returnPacket caller p i).2.val t}
      | .repeat next t => g.observeAt caller prim next t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  have run := raw_step g caller prim p s
  cases now : (g.control.head caller p).execute prim s <;> rw [now] at run
  · rename_i i marked t
    rw [Endpoint.observeAt, close_terminal run]
    simp only [denote_exitContinuation]
    cases selected : g.control.selected i <;> simp [selected, Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind, selected]
  · rw [Endpoint.observeAt, close_branch run]
    rfl
  · rw [Endpoint.observeAt, close_terminal (o := .fault _) run]
    simp [Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind]
  · rw [Endpoint.observeAt, close_terminal (o := .diverge) run]
    simp [Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind]

private def headTransition {σ : Type v} (head : Packet R → Head S R) (output : Packet R → Tag → Value Unit)
    (prim : Syntax.StatePrimitives Φ σ) (x : Packet R × σ) :
    (Packet R × σ) ⊕ Outcome 2 Unit σ :=
  match (head x.1).execute prim x.2 with
  | .exit i _ t => .inr (.ret i (output x.1 i) t)
  | .repeat next t => .inl (next, t)
  | .fault t => .inr (.fault t)
  | .diverge => .inr .diverge

private theorem close_head_transition {σ : Type v} (head : Packet R → Head S R) (output : Packet R → Tag → Value Unit)
    (prim : Syntax.StatePrimitives Φ σ) (f : Feedback.Run R (Exits A) Unit σ)
    (localRow : ∀ p s, f (blockPoint p s) =
      match (head p).execute prim s with
      | .exit i _ t => WithTop.some {Feedback.external R (Exits A) (.ret i (output p i) t)}
      | .repeat q t => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) q.1) q.2.val t}
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge})
    (p : Packet R) (s : σ) :
    Feedback.close f (blockPoint p s) =
      (Feedback.Graph.transitions (headTransition head output prim) Outcome.diverge).close (p, s) := by
  let invoke (x : Packet R × σ) : Fin R.length × Value Unit × σ := (x.1.1, x.1.2.val, x.2)
  have rows (x : Packet R × σ) :
      f (.block (invoke x).1 (invoke x).2.1 (invoke x).2.2) =
        match headTransition head output prim x with
        | .inl y => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) (invoke y).1) (invoke y).2.1 (invoke y).2.2}
        | .inr o => WithTop.some {Feedback.external R (Exits A) o} := by
    change f (blockPoint x.1 x.2) = _
    rw [localRow]
    unfold headTransition
    cases (head x.1).execute prim x.2 <;> rfl
  have same := (Feedback.Graph.transitions_run (headTransition head output prim) Outcome.diverge invoke id
    f rfl (fun x => by
      cases h : headTransition head output prim x <;> simpa only [h] using! rows x)).close_eq (p, s)
  change Feedback.close (f) (blockPoint p s) = _ at same
  simpa [Set.image_id] using same

open Classical in
private theorem decorate_set {σ : Type v} (selected : Tag → Bool) (xs : Set (Outcome 2 Unit σ)) :
    Behaviour.bind (WithTop.some xs : Behaviour 2 Unit σ)
        (fun (i : Tag) a s => if selected i then ⊤ else (WithTop.some {Outcome.ret i a s} : Behaviour 2 Unit _)) =
      if (∃ i a s, Outcome.ret i a s ∈ xs ∧ selected i = true) then ⊤ else WithTop.some xs := by
  classical
  by_cases h : ∃ i a s, Outcome.ret i a s ∈ xs ∧ selected i = true
  · obtain ⟨i, a, s, mem, hit⟩ := h
    rw [ite_eq_left ⟨i, a, s, mem, hit⟩, Behaviour.bind]
    exact ite_eq_left (Or.inr ⟨i, a, s, mem, by simp [hit]⟩)
  · have no (i : Fin 2) (a : Value Unit) (s : σ) (mem : Outcome.ret i a s ∈ xs) :
        selected i = false := Bool.eq_false_iff.mpr fun hit => h ⟨i, a, s, mem, hit⟩
    have never : ¬ ∃ i a s, Outcome.ret i a s ∈ xs ∧
        (if selected i then (⊤ : Behaviour 2 Unit σ) else WithTop.some {Outcome.ret i a s}) = ⊤ := by
      rintro ⟨i, a, s, mem, top⟩
      simp [no i a s mem] at top
    simp only [Behaviour.bind, WithTop.coe_ne_top, false_or, Behaviour.possible, WithTop.untopD_coe,
      h, never, ↓reduceIte, WithTop.coe_inj]
    apply Set.ext
    intro o
    simp only [Outcome.bind, Set.mem_ofPred_eq]
    constructor
    · rintro (pass | ⟨i, a, s, mem, here⟩)
      · cases o <;> first | exact pass | exact pass.elim
      · have eq : o = Outcome.ret i a s := by simpa [no i a s mem] using here
        exact eq.symm ▸ mem
    · intro mem
      cases o with
      | ret i a s => exact Or.inr ⟨i, a, s, mem, by simp [no i a s mem]⟩
      | fault | diverge => exact Or.inl mem

private theorem decorate_mapState {σ : Type v} {τ : Type w} (e : σ → τ) (selected : Tag → Bool)
    (b : Behaviour 2 Unit σ) :
    Behaviour.bind (b.mapState e) (fun (i : Tag) a s => if selected i then ⊤ else (WithTop.some {Outcome.ret i a s} : Behaviour 2 Unit _)) =
      Behaviour.mapState e (Behaviour.bind b (fun (i : Tag) a s => if selected i then ⊤ else (WithTop.some {Outcome.ret i a s} : Behaviour 2 Unit _))) := by
  classical
  induction b using WithTop.recTopCoe with
  | top => simp [Behaviour.mapState, Behaviour.bind]
  | coe b =>
    simp only [Behaviour.mapState, WithTop.map_coe, decorate_set]
    have same :
        (∃ i a s, Outcome.ret i a s ∈ Outcome.mapState e '' b ∧ selected i = true) ↔
          (∃ i a s, Outcome.ret i a s ∈ b ∧ selected i = true) := by
      constructor
      · rintro ⟨i, a, s, ⟨o, mem, eq⟩, hit⟩
        cases o <;> simp [Outcome.mapState] at eq
        obtain ⟨rfl, rfl, rfl⟩ := eq
        exact ⟨_, _, _, mem, hit⟩
      · rintro ⟨i, a, s, mem, hit⟩
        exact ⟨i, a, e s, ⟨_, mem, rfl⟩, hit⟩
    simp only [same]
    split <;> rfl

theorem head_feedback_mapState {σ : Type v} {τ : Type w} (head : Packet R → Head S R) (output : Packet R → Tag → Value Unit)
    (e : σ ↪ τ) (prim : Syntax.StatePrimitives Φ σ) (other : Syntax.StatePrimitives Φ τ)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e)
    (f : Feedback.Run R (Exits A) Unit σ) (h : Feedback.Run R (Exits A) Unit τ)
    (source : ∀ p s, f (blockPoint p s) =
      match (head p).execute prim s with
      | .exit i _ t => WithTop.some {Feedback.external R (Exits A) (.ret i (output p i) t)}
      | .repeat q t => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) q.1) q.2.val t}
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge})
    (target : ∀ p s, h (blockPoint p s) =
      match (head p).execute other s with
      | .exit i _ t => WithTop.some {Feedback.external R (Exits A) (.ret i (output p i) t)}
      | .repeat q t => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) q.1) q.2.val t}
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge})
    (selected : Tag → Bool) (p : Packet R) (s : σ) :
    (Feedback.close h (blockPoint p (e s))).bind
        (fun i a t => if selected i then ⊤ else WithTop.some {Outcome.ret i a t}) =
      Behaviour.mapState e ((Feedback.close f (blockPoint p s)).bind
        (fun i a t => if selected i then ⊤ else WithTop.some {Outcome.ret i a t})) := by
  let point (x : Packet R × σ) := (x.1, e x.2)
  have next (x : Packet R × σ) :
      headTransition head output other (point x) =
        (headTransition head output prim x).map point (Outcome.mapState e) := by
    obtain ⟨p, s⟩ := x
    unfold headTransition
    dsimp [point]
    cases head p with
    | exit | diverge => rfl
    | request f arg route =>
      simp only [Head.execute, agree]
      cases prim f arg s <;> rfl
  have rel : Feedback.Graph.Transport
      (Feedback.Graph.transitions (headTransition head output prim) Outcome.diverge)
      (Feedback.Graph.transitions (headTransition head output other) Outcome.diverge) point (Outcome.mapState e) := by
    constructor
    · intro x y
      change headTransition head output other (point x) = .inl y ↔ _
      rw [next]
      cases h : headTransition head output prim x <;> simp [Feedback.Graph.transitions, h]
    · intro x
      rfl
    · intro x o
      change headTransition head output other (point x) = .inr o ↔ _
      rw [next]
      cases h : headTransition head output prim x <;> simp [Feedback.Graph.transitions, h]
    · rfl
  rw [close_head_transition head output prim f source, close_head_transition head output other h target]
  rw [show (Feedback.Graph.transitions (headTransition head output other) Outcome.diverge).close (p, e s) =
    ((Feedback.Graph.transitions (headTransition head output prim) Outcome.diverge).close (p, s)).map
      (Set.image (Outcome.mapState e)) from rel.close_eq (p, s)]
  exact decorate_mapState e _ _

theorem observeAt_mapState {σ τ : Type v} (g : Endpoint S R A) (e : σ ↪ τ)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (other : Syntax.StatePrimitives Φ τ)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e) (p : Packet R) (s : σ) :
    g.observeAt caller other p (e s) = Behaviour.mapState e (g.observeAt caller prim p s) := by
  simp only [Endpoint.observeAt, denote_exitContinuation]
  apply head_feedback_mapState (g.control.head caller) (fun p i => (g.returnPacket caller p i).2.val) e prim other agree
  · intro p s
    rw [raw_step]
    cases (g.control.head caller p).execute prim s <;> rfl
  · intro p s
    rw [raw_step]
    cases (g.control.head caller p).execute other s <;> rfl

theorem unit_blocks (g : Table S R) : (Endpoint.unit g).blocks = g.blocks := by
  funext i
  unfold Endpoint.blocks Table.blocks
  simp only [Endpoint.unit]
  cases g.row i <;> rfl

theorem unit_native (g : Table S R) : (Endpoint.unit g).native = g.native := by
  apply Subtype.ext
  change nativeFeedback (Endpoint.unit g).entryRegion (Endpoint.unit g).blocks =
    nativeFeedback g.entryRegion g.blocks
  rw [unit_blocks]
  rfl

theorem unit_observeAt {σ : Type v} (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : Syntax.StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    (Endpoint.unit g).observeAt caller prim p s = g.observeAt caller prim p s := by
  unfold Endpoint.observeAt Table.observeAt Endpoint.feedback Table.feedback
  rw [unit_blocks]
  rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
