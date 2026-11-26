module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Defs
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
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits resultBehaviour)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet unpack)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives model)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax (diverge_bind)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {states : Nat}

theorem check_pair_iff [DecidableEq Φ] (replies : ReplyEnumeration S)
    (related : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies related q = true ↔ p.Matches (fun x y => related x y = true) q := by
  cases p with
  | exit i selected =>
    cases q with
    | exit j selected' => cases selected <;> cases selected' <;> simp [Head.checkPair, Head.Matches]
    | request => cases selected <;> simp [Head.checkPair, Head.Matches]
  | request f arg next =>
    cases q with
    | exit i selected => cases selected <;> simp [Head.checkPair, Head.Matches]
    | request g arg' next' =>
      rw [Head.checkPair, Head.Matches]
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

private theorem observe_infinite (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : Primitives Φ states) (configs : Nat → Packet R) (store : Nat → Fin states)
    (next : ∀ n, (g.head caller (configs n)).execute prim (store n) = .repeat (configs (n + 1)) (store (n + 1))) :
    g.observeAt caller prim (configs 0) (store 0) = resultBehaviour .diverge := by
  let path := fun n => blockPoint (configs n) (store n)
  have loop := close_infinite_of_singleton (f := g.feedback caller prim) path
    (fun n => ⟨(configs (n + 1)).1, (configs (n + 1)).2.val, store (n + 1), rfl,
      (g.feedback_step caller prim (configs n) (store n)).trans (congrArg StateTransition.routed (next n))⟩)
  rw [Table.observeAt, loop]
  exact diverge_bind _

private theorem local_match (g : Table S R) (h : Table S T) (caller : Payload (R.get g.entry))
    (caller' : Payload (T.get h.entry)) (prim : Primitives Φ states) (rel : Packet R → Packet T → Prop)
    (p : Packet R) (q : Packet T) (s : Fin states) (agreement : (g.head caller p).Matches rel (h.head caller' q)) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s ∨
      ∃ p' q' t, (g.head caller p).execute prim s = .repeat p' t ∧
        (h.head caller' q).execute prim s = .repeat q' t ∧ rel p' q' := by
  cases upper : h.head caller' q with
  | exit j selected =>
    cases selected with
    | true =>
      left
      rw [h.observe_step, upper]
      exact le_top
    | false =>
      cases lower : g.head caller p with
      | exit i marked =>
        cases marked with
        | true => simp [lower, upper, Head.Matches] at agreement
        | false =>
          have same : i = j := by simpa [lower, upper, Head.Matches] using agreement
          left
          rw [g.observe_step, h.observe_step, lower, upper, same]
          exact le_rfl
      | request => simp [lower, upper, Head.Matches] at agreement
  | request op' operand' next' =>
    cases lower : g.head caller p with
    | exit => simp [lower, upper, Head.Matches] at agreement
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
        rw [g.observe_step, h.observe_step, lower, upper, Head.execute, Head.execute, answer]
      | diverge =>
        left
        rw [g.observe_step, h.observe_step, lower, upper, Head.execute, Head.execute, answer]

theorem closed_relation_sound (g : Table S R) (h : Table S T) (caller : Payload (R.get g.entry))
    (caller' : Payload (T.get h.entry)) (prim : Primitives Φ states) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head caller p).Matches rel (h.head caller' q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : Fin states) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s := by
  classical
  by_contra fails
  let Bad := { x : Packet R × Packet T × Fin states // rel x.1 x.2.1 ∧
    ¬ g.observeAt caller prim x.1 x.2.2 ≤ h.observeAt caller' prim x.2.1 x.2.2 }
  let start : Bad := ⟨(p, q, s), related, fails⟩
  have advance (x : Bad) : ∃ y : Bad,
      (g.head caller x.val.1).execute prim x.val.2.2 = .repeat y.val.1 y.val.2.2 ∧
      (h.head caller' x.val.2.1).execute prim x.val.2.2 = .repeat y.val.2.1 y.val.2.2 := by
    obtain ⟨⟨p, q, s⟩, related, fails⟩ := x
    obtain order | ⟨p', q', t, lp, rp, related'⟩ :=
      local_match g h caller caller' prim rel p q s (closed p q related)
    · exact (fails order).elim
    have fails' : ¬ g.observeAt caller prim p' t ≤ h.observeAt caller' prim q' t := by
      rw [g.observe_step, h.observe_step, lp, rp] at fails
      exact fails
    exact ⟨⟨(p', q', t), related', fails'⟩, lp, rp⟩
  let path : Nat → Bad := fun n => Nat.rec start (fun _ x => (advance x).choose) n
  have edges (n : Nat) := (advance (path n)).choose_spec
  let store := fun n => (path n).val.2.2
  have left := observe_infinite g caller prim (fun n => (path n).val.1) store (fun n => (edges n).1)
  have right := observe_infinite h caller' prim (fun n => (path n).val.2.1) store (fun n => (edges n).2)
  change g.observeAt caller prim p s = resultBehaviour .diverge at left
  change h.observeAt caller' prim q s = resultBehaviour .diverge at right
  exact fails ((left.trans right.symm).le)

theorem product_sound [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (caller : Payload (R.get g.entry)) (caller' : Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pairs : List (Packet R × Packet T))
    (checked : g.checkProduct h caller caller' replies pairs = true) (prim : Primitives Φ states) (s : Fin states) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) s ≤
      Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) s := by
  rw [g.observe_entry raw readback, h.observe_entry raw' readback']
  obtain ⟨entry, all⟩ := Bool.and_eq_true_iff.mp checked
  exact closed_relation_sound g h caller caller' prim (fun p q => productContains pairs p q = true)
    (fun p q mem => (check_pair_iff replies _ _ _).mp
      (List.all_eq_true.mp all (p, q) ((product_contains_iff pairs p q).mp mem))) entry s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
