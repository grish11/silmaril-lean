module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Observer.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Observation.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet unpack)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives model)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (diverge_bind)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {σ : Type v} {A : Syntax.Ty}

theorem check_pair_iff [DecidableEq Φ] (replies : ReplyEnumeration S)
    (related : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies related q = true ↔ p.Matches (fun x y => related x y = true) q := by
  cases p with
  | exit i selected =>
    cases q with
    | exit j selected' => cases selected <;> cases selected' <;> simp [Head.checkPair, Head.Matches, Head.MatchesWith]
    | request | diverge => cases selected <;> simp [Head.checkPair, Head.Matches, Head.MatchesWith]
  | diverge =>
    cases q with
    | exit _ selected => cases selected <;> simp [Head.checkPair, Head.Matches, Head.MatchesWith]
    | request | diverge => simp [Head.checkPair, Head.Matches, Head.MatchesWith]
  | request f arg next =>
    cases q with
    | diverge => simp [Head.checkPair, Head.Matches, Head.MatchesWith]
    | exit i selected => cases selected <;> simp [Head.checkPair, Head.Matches, Head.MatchesWith]
    | request g arg' next' =>
      rw [Head.checkPair, Head.Matches, Head.MatchesWith]
      split
      · rename_i hits
        obtain ⟨keys, values⟩ := Prod.mk.inj hits
        subst g
        rw [List.all_eq_true]
        constructor
        · exact fun all => ⟨rfl, values, fun r => all r (replies.complete f r)⟩
        · rintro ⟨_, _, all⟩ r _
          exact all r
      · rename_i misses
        simp only [Bool.false_eq_true, false_iff]
        exact fun ⟨keys, values, _⟩ => misses (Prod.ext keys values)

theorem product_contains_iff (pairs : List (Packet R × Packet T)) (p : Packet R) (q : Packet T) :
    productContains pairs p q = true ↔ (p, q) ∈ pairs := by
  rw [productContains, List.any_eq_true]
  simp only [decide_eq_true_eq, CFG.Dependent.Packet.raw_injective.eq_iff]
  constructor
  · rintro ⟨⟨_, _⟩, mem, rfl, rfl⟩
    exact mem
  · exact fun mem => ⟨_, mem, rfl, rfl⟩

theorem head_mark (g : Table S R) (caller : Payload (R.get g.entry)) (p : Packet R)
    {i : Tag} {marked : Bool} (head : g.head caller p = .exit i marked) : g.selected i = marked := by
  unfold Table.head at head
  split at head
  · obtain ⟨rfl, eq⟩ := Head.exit.inj head
    exact eq
  all_goals contradiction

theorem payload_observe_infinite (g : Endpoint S R A) (caller : Payload (R.get g.control.entry))
    (prim : StatePrimitives Φ σ) (configs : Nat → Packet R) (store : Nat → σ)
    (next : ∀ n, (g.control.head caller (configs n)).execute prim (store n) = .repeat (configs (n + 1)) (store (n + 1))) :
    g.observeAt caller prim (configs 0) (store 0) = WithTop.some {Outcome.diverge} := by
  let path := fun n => blockPoint (configs n) (store n)
  have loop := close_infinite_of_singleton (f := g.feedback caller prim) path
    (fun n => ⟨(configs (n + 1)).1, (configs (n + 1)).2.val, store (n + 1), rfl,
      (g.feedback_step caller prim (configs n) (store n)).trans (congrArg (g.route caller (configs n)) (next n))⟩)
  rw [Endpoint.observeAt, loop]
  exact diverge_bind _

@[expose] noncomputable def payload_observer (g : Endpoint S R A) (caller : Payload (R.get g.control.entry)) :
    HeadObserver.{u,v} S R where
  head := g.control.head caller
  returnValue p i := (g.returnPacket caller p i).2.val
  observe := fun prim => g.observeAt caller prim
  step := by
    intro σ prim p s
    rw [g.observe_state_step]
    cases head : g.control.head caller p with
    | exit i selected => simp only [Head.execute, head_mark g.control caller p head]
    | diverge => rfl
    | request f arg next =>
      simp only [Head.execute]
      cases prim f arg s <;> rfl
  infinite := fun prim => payload_observe_infinite g caller prim
  mapState := fun e prim other => g.observeAt_mapState e caller prim other

private theorem local_match (g : HeadObserver.{u,v} S R) (h : HeadObserver.{u,v} S T)
    (prim : StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (p : Packet R) (q : Packet T) (s : σ) (agreement : (g.head p).MatchesWith
      (fun i j => (i, g.returnValue p i) = (j, h.returnValue q j)) rel (h.head q)) :
    g.observe prim p s ≤ h.observe prim q s ∨
      ∃ p' q' t, (g.head p).execute prim s = .repeat p' t ∧
        (h.head q).execute prim s = .repeat q' t ∧ rel p' q' := by
  cases upper : h.head q with
  | exit j selected =>
    cases selected with
    | true =>
      left
      rw [h.step, upper]
      simp only [Head.execute, ↓reduceIte]
      exact le_top
    | false =>
      cases lower : g.head p with
      | exit i marked =>
        cases marked with
        | true => simp [lower, upper, Head.MatchesWith] at agreement
        | false =>
          have same : (i, g.returnValue p i) = (j, h.returnValue q j) := by
            simpa [lower, upper, Head.MatchesWith] using agreement
          have tag : i = j := congrArg Prod.fst same
          have val : g.returnValue p i = h.returnValue q j :=
            congrArg Prod.snd same
          left
          rw [g.step, h.step, lower, upper]
          simp only [Head.execute,
            Bool.false_eq_true, ↓reduceIte]
          rw [val, tag]
      | request | diverge => simp [lower, upper, Head.MatchesWith] at agreement
  | diverge =>
    cases lower : g.head p with
    | exit | request => simp [lower, upper, Head.MatchesWith] at agreement
    | diverge =>
      left
      rw [g.step, h.step, lower, upper]
      exact le_rfl
  | request op' operand' next' =>
    cases lower : g.head p with
    | exit | diverge => simp [lower, upper, Head.MatchesWith] at agreement
    | request op operand next =>
      rw [lower, upper] at agreement
      obtain ⟨keys, values, replies⟩ := agreement
      subst op'
      have same : operand = operand' := Subtype.ext values
      subst operand'
      cases answer : prim op operand s with
      | ret a t =>
        let reply := unpack (cast (congrArg Payload (S.target op)) a)
        right
        exact ⟨next reply.1 reply.2, next' reply.1 reply.2, t,
          by rw [Head.execute, answer],
          by rw [Head.execute, answer], replies reply⟩
      | fault t =>
        left
        rw [g.step, h.step, lower, upper, Head.execute, Head.execute, answer]
      | diverge =>
        left
        rw [g.step, h.step, lower, upper, Head.execute, Head.execute, answer]

theorem observer_closed_relation_sound (g : HeadObserver.{u,v} S R) (h : HeadObserver.{u,v} S T)
    (prim : StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head p).MatchesWith
      (fun i j => (i, g.returnValue p i) = (j, h.returnValue q j)) rel (h.head q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observe prim p s ≤ h.observe prim q s := by
  classical
  by_contra fails
  let Bad := { x : Packet R × Packet T × σ // rel x.1 x.2.1 ∧
    ¬ g.observe prim x.1 x.2.2 ≤ h.observe prim x.2.1 x.2.2 }
  let start : Bad := ⟨(p, q, s), related, fails⟩
  have advance (x : Bad) : ∃ y : Bad,
      (g.head x.val.1).execute prim x.val.2.2 = .repeat y.val.1 y.val.2.2 ∧
      (h.head x.val.2.1).execute prim x.val.2.2 = .repeat y.val.2.1 y.val.2.2 := by
    obtain ⟨⟨p, q, s⟩, related, fails⟩ := x
    obtain order | ⟨p', q', t, lp, rp, related'⟩ :=
      local_match g h prim rel p q s (closed p q related)
    · exact (fails order).elim
    have fails' : ¬ g.observe prim p' t ≤ h.observe prim q' t := by
      rw [g.step, h.step, lp, rp] at fails
      exact fails
    exact ⟨⟨(p', q', t), related', fails'⟩, lp, rp⟩
  let path : Nat → Bad := fun n => Nat.rec start (fun _ x => (advance x).choose) n
  have edges (n : Nat) := (advance (path n)).choose_spec
  let store := fun n => (path n).val.2.2
  have left := g.infinite prim (fun n => (path n).val.1) store (fun n => (edges n).1)
  have right := h.infinite prim (fun n => (path n).val.2.1) store (fun n => (edges n).2)
  change g.observe prim p s = WithTop.some {Outcome.diverge} at left
  change h.observe prim q s = WithTop.some {Outcome.diverge} at right
  exact fails ((left.trans right.symm).le)

theorem payload_closed_relation_sound (g : Endpoint S R A) (h : Endpoint S T A) (caller : Payload (R.get g.control.entry))
    (caller' : Payload (T.get h.control.entry)) (prim : StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.control.head caller p).MatchesWith
      (fun i j => (g.returnPacket caller p i).raw = (h.returnPacket caller' q j).raw) rel (h.control.head caller' q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s :=
  observer_closed_relation_sound (payload_observer g caller) (payload_observer h caller') prim rel closed related s

theorem unit_matches_iff (g : Table S R) (h : Table S T) (a : Payload (R.get g.entry))
    (b : Payload (T.get h.entry)) (p : Packet R) (q : Packet T) (rel : Packet R → Packet T → Prop)
    (lower : Head S R) (upper : Head S T) :
    lower.MatchesWith
      (fun i j => ((Endpoint.unit g).returnPacket a p i).raw = ((Endpoint.unit h).returnPacket b q j).raw)
      rel upper ↔ lower.Matches rel upper := by
  cases lower with
  | diverge =>
    cases upper with
    | request | diverge => rfl
    | exit _ selected => cases selected <;> rfl
  | request =>
    cases upper with
    | request | diverge => rfl
    | exit j selected => cases selected <;> rfl
  | exit i marked =>
    cases upper with
    | request | diverge => rfl
    | exit j selected =>
      cases marked <;> cases selected
      all_goals try rfl
      change ((Endpoint.unit g).returnPacket a p i).raw = ((Endpoint.unit h).returnPacket b q j).raw ↔ i = j
      constructor
      · exact congrArg Prod.fst
      · intro eq
        apply Prod.ext eq
        change ((Endpoint.unit g).returnPacket a p i).2.val = ((Endpoint.unit h).returnPacket b q j).2.val
        exact ((Endpoint.unit g).returnPacket_value a p i).trans
          ((Endpoint.unit h).returnPacket_value b q j).symm

theorem closed_relation_sound (g : Table S R) (h : Table S T) (caller : Payload (R.get g.entry))
    (caller' : Payload (T.get h.entry)) (prim : StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head caller p).Matches rel (h.head caller' q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s := by
  rw [← Endpoint.unit_observeAt g, ← Endpoint.unit_observeAt h]
  apply payload_closed_relation_sound (Endpoint.unit g) (Endpoint.unit h) caller caller' prim rel _ related s
  intro p q related
  exact (unit_matches_iff g h caller caller' p q rel _ _).mpr (closed p q related)

theorem product_sound [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (caller : Payload (R.get g.entry)) (caller' : Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pairs : List (Packet R × Packet T))
    (checked : g.checkProduct h caller caller' replies pairs = true) (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) s ≤
      Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) s := by
  rw [g.observe_entry raw readback, h.observe_entry raw' readback']
  obtain ⟨entry, all⟩ := Bool.and_eq_true_iff.mp checked
  exact closed_relation_sound g h caller caller' prim (fun p q => productContains pairs p q = true)
    (fun p q mem => (check_pair_iff replies _ _ _).mp
      (List.all_eq_true.mp all (p, q) ((product_contains_iff pairs p q).mp mem))) entry s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
