module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exit)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature Handler Prefix)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

theorem exit_order {n : Nat} (p q : Exit) (s : Fin n) :
    (p.result s).refines (q.result s) ↔ p.Refines q := by
  cases p <;> cases q <;> simp [Exit.result, Exit.Refines, Result.refines]

theorem sound (p q : Tree S) (related : p.Refines q) {n : Nat}
    (prim : Syntax.Primitives Φ n) (s : Fin n) :
    (p.execute prim s).refines (q.execute prim s) := by
  induction p generalizing q s with
  | stop e =>
    cases q with
    | stop e' => exact (exit_order e e' s).mpr related
    | ask f arg next => exact False.elim related
  | ask f arg arms ih =>
    cases q with
    | stop e =>
      cases e with
      | ub => exact Or.inl rfl
      | ret i => exact False.elim related
    | ask g arg' next =>
      obtain ⟨keys, values, branches⟩ := related
      subst g
      have same : arg = arg' := Subtype.ext values
      subst arg'
      rw [Tree.execute, Tree.execute]
      cases prim f arg s with
      | ret a t =>
        let packet := CFG.Dependent.unpack (cast (congrArg Syntax.Payload (S.target f)) a)
        exact ih packet.1 packet.2 _ (branches packet.1 packet.2) t
      | fault | diverge => exact Or.inr rfl

theorem execute_ask {n : Nat} (f : Φ) (arg : Syntax.Payload (instrSrc f))
    (arms : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Tree S)
    (h : Handler S.replies n) (s : Fin n) :
    (Tree.ask f arg arms).execute (S.primitives h) s =
      match h f arg.val s with
      | .reply i a t => (arms i a).execute (S.primitives h) t
      | .fault t => .fault t
      | .diverge => .diverge := by
  rw [Tree.execute]
  unfold RequestSignature.primitives
  cases h f arg.val s with
  | reply i a t =>
    let packet : CFG.Dependent.Packet (S.replies f) := ⟨i, a⟩
    let typeEq := congrArg Syntax.Payload (S.target f)
    have roundtrip : cast typeEq (cast typeEq.symm (CFG.Dependent.pack packet)) =
        CFG.Dependent.pack packet := by simp only [cast_cast, cast_eq]
    let run (reply : CFG.Dependent.Packet (S.replies f)) :=
      (arms reply.1 reply.2).execute (S.primitives h) t
    change run (CFG.Dependent.unpack (cast typeEq (cast typeEq.symm (CFG.Dependent.pack packet)))) =
      run packet
    rw [roundtrip, CFG.Dependent.unpack_pack]
  | fault | diverge => rfl

private def shift {n : Nat} : Result 2 n → Result 2 (n + 1)
  | .ret i s => .ret i s.succ
  | .fault s => .fault s.succ
  | .diverge => .diverge
  | .ub => .ub

private theorem shift_order {n : Nat} (p q : Result 2 n) :
    (shift p).refines (shift q) ↔ p.refines q := by
  cases p <;> cases q <;> simp [shift, Result.refines]

variable [DecidableEq Φ]

private theorem execute_succ {n : Nat} (p : Tree S) (rest : Prefix S.replies n)
    (f : Φ) (arg : Value Unit) (i : Fin (S.replies f).length) (a : Syntax.Payload ((S.replies f).get i))
    (s : Fin (n + 1)) :
    p.execute (S.primitives (Prefix.step f arg i a rest).handler) s.succ =
      shift (p.execute (S.primitives rest.handler) s) := by
  induction p generalizing s with
  | stop e => cases e <;> rfl
  | ask g operand arms ih =>
    rw [execute_ask, execute_ask, Prefix.handler_succ]
    cases rest.handler g operand.val s with
    | reply j b t => exact ih j b t
    | fault | diverge => rfl

private theorem execute_step {n : Nat} (f : Φ) (arg : Syntax.Payload (instrSrc f))
    (arms : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Tree S)
    (i : Fin (S.replies f).length) (a : Syntax.Payload ((S.replies f).get i)) (rest : Prefix S.replies n) :
    (Tree.ask f arg arms).execute (S.primitives (Prefix.step f arg.val i a rest).handler) 0 =
      shift ((arms i a).execute (S.primitives rest.handler) 0) := by
  have entry : (Prefix.step f arg.val i a rest).handler f arg.val 0 = .reply i a (Fin.succ 0) := by
    simp [Prefix.handler]
  rw [execute_ask, entry]
  exact execute_succ (arms i a) rest f arg.val i a 0

theorem prefix_step_order {n : Nat} (f : Φ) (arg : Syntax.Payload (instrSrc f))
    (arms next : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Tree S)
    (i : Fin (S.replies f).length) (a : Syntax.Payload ((S.replies f).get i)) (rest : Prefix S.replies n) :
    ((Tree.ask f arg arms).execute (S.primitives (Prefix.step f arg.val i a rest).handler) 0).refines
      ((Tree.ask f arg next).execute (S.primitives (Prefix.step f arg.val i a rest).handler) 0) ↔
      ((arms i a).execute (S.primitives rest.handler) 0).refines
        ((next i a).execute (S.primitives rest.handler) 0) := by
  rw [execute_step, execute_step, shift_order]

theorem separate (p q : Tree S) (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix S.replies n), p.Follows probe ∧ q.Follows probe ∧
      ¬ (p.execute (S.primitives probe.handler) 0).refines (q.execute (S.primitives probe.handler) 0) := by
  classical
  induction p generalizing q with
  | stop e =>
    cases q with
    | stop e' =>
      exact ⟨0, .stop none, .stop _ _, .stop _ _, fun h => fails ((exit_order e e' 0).mp h)⟩
    | ask g arg arms =>
      refine ⟨0, .stop none, .stop _ _, .stop _ _, ?_⟩
      rw [execute_ask]
      cases e <;> simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]
  | ask f arg arms ih =>
    cases q with
    | stop e =>
      cases e with
      | ub => exact (fails trivial).elim
      | ret i =>
        refine ⟨0, .stop none, .stop _ _, .stop _ _, ?_⟩
        rw [execute_ask]
        simp [Tree.execute, Prefix.handler, Exit.result, Result.refines]
    | ask g arg' next =>
      by_cases query : (f, arg.val) = (g, arg'.val)
      · obtain ⟨keys, values⟩ := Prod.mk.inj query
        subst g
        have same : arg = arg' := Subtype.ext values
        subst arg'
        have missing : ∃ i a, ¬ (arms i a).Refines (next i a) := by
          by_contra no
          exact fails ⟨rfl, rfl, fun i a => Classical.byContradiction fun bad => no ⟨i, a, bad⟩⟩
        obtain ⟨i, a, bad⟩ := missing
        obtain ⟨n, rest, left, right, counterexample⟩ := ih i a (next i a) bad
        refine ⟨n + 1, .step f arg.val i a rest, .step left, .step right, ?_⟩
        rwa [prefix_step_order]
      · refine ⟨0, .stop (some (f, arg.val)), .stop _ _, .stop _ _, ?_⟩
        have off : ¬ (f = g ∧ arg.val = arg'.val) := fun ⟨key, value⟩ => query (Prod.ext key value)
        rw [execute_ask, execute_ask]
        simp [Prefix.handler, off, Result.refines]

omit [DecidableEq Φ] in
theorem follows_le {p : Tree S} {n depth : Nat} {probe : Prefix S.replies n}
    (path : p.Follows probe) (budget : p.Fits depth) : n ≤ depth := by
  induction path generalizing depth with
  | stop => exact Nat.zero_le _
  | step tail ih =>
    cases depth with
    | zero => exact False.elim budget
    | succ depth => exact Nat.succ_le_succ (ih (budget _ _))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
