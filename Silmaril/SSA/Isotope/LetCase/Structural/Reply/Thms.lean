module

public import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Reply.Categorical
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Reply.EmptyBoundary
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Reply.Replay
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Reply.Trace

/-! # Sum specialization and categorical reply cancellation for native LetCase -/

public section

namespace Silmaril.Isotope.LetCase.Structural.Reply

open LocallyNameless (Derivation Equiv HasType Tm)
open Silmaril.Isotope.Semantics (BoundEnv)
open LetIter.Semantics.Categorical (boundEnv boundObj)
open LetSeq.StraightLine.Structural (Trace)
open LetSeq.StraightLine.Structural.Categorical (traceTypes)
open scoped LetSeq.StraightLine.Structural

local notation "Value" => LetSeq.StraightLine.Structural.Value

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- Split any let-bound sum into constructor specializations of its exact
continuation. The scrutinee is kept once, before choosing a branch. -/
theorem split_let {n : Nat} {β : BoundCtx (Ty α) n} {e : Tm Empty Φ n}
    {k : Tm Empty Φ (n + 1)} {A B D : Ty α}
    (de : HasType Φ Γ₀ β e (.coprod A B))
    (dk : HasType Φ Γ₀ (β.snoc (.coprod A B)) k D) :
    Equiv false Γ₀ β (.let₁ e k)
      (.case e (specialize k (.inl (.bv 0))) (specialize k (.inr (.bv 0)))) D :=
  split_let_proof de dk

/-- Native contextual equality at a retained sum reduces to the two
constructor specializations, including for effectful exact bodies. -/
theorem equiv_iff_specializations {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ (n + 1)} {A B D : Ty α}
    (dt : HasType Φ Γ₀ (β.snoc (.coprod A B)) t D)
    (du : HasType Φ Γ₀ (β.snoc (.coprod A B)) u D) :
    Equiv false Γ₀ (β.snoc (.coprod A B)) t u D ↔
      Equiv false Γ₀ (β.snoc A) (specialize t (.inl (.bv 0))) (specialize u (.inl (.bv 0))) D ∧
      Equiv false Γ₀ (β.snoc B) (specialize t (.inr (.bv 0))) (specialize u (.inr (.bv 0))) D :=
  equiv_iff_specializations_proof dt du

/-- Successful logs of any native exact derivation at a fixed input are
prefix-free and determine the returned value. -/
theorem run_prefix_determined {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm Empty Φ n} {A : Ty α} (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Value β) :
    PrefixDetermined (run d ρ) :=
  run_prefix_determined_proof d ρ

/-- Cancel a common successful trace prefix on exactly the replies it can reach. -/
theorem bind_eq_iff_for_replies {A B : Type} {m : Trace α Φ A} (hm : PrefixDetermined m)
    (k l : A → Trace α Φ B) :
    (m >>= k) = (m >>= l) ↔ ∀ a w, (a, w) ∈ m.outcomes → k a = l a :=
  bind_eq_iff_for_replies_proof hm k l

/-- A common primitive can supply every typed reply whenever evaluation of
its argument has a successful trace. -/
theorem run_op_reaches_reply {n : Nat} {β : BoundCtx (Ty α) n} {arg : Tm Empty Φ n}
    (f : Φ) (d : Derivation Φ Γ₀ β arg (instrSrc f)) (ρ : BoundEnv Value β)
    (reply : Value (instrTrg f)) :
    (∃ w, (reply, w) ∈ (run (.op (f := f) d) ρ).outcomes) ↔ (run d ρ).outcomes.Nonempty :=
  run_op_reaches_reply_proof f d ρ reply

/-- Observe the actual categorical arrow at a bound-environment product. -/
theorem traceArrow_apply {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (ρ : boundObj (traceTypes α) β) :
    (traceArrow d).of (PUnit.unit, ρ) = run d (boundEnv Value ρ) :=
  traceArrow_apply_proof d ρ

/-- Equality of categorical trace arrows is pointwise equality of their runs. -/
theorem traceArrow_eq_iff_run {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) :
    traceArrow d = traceArrow e ↔ ∀ ρ, run d ρ = run e ρ :=
  traceArrow_eq_iff_run_proof d e

/-- The typed ordered trace model belongs to the compatible Freyd class. -/
theorem traceArrow_of_valid {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ n} {A : Ty α}
    {d : Derivation Φ Γ₀ β t A} {e : Derivation Φ Γ₀ β u A}
    (h : Valid d e) : traceArrow d = traceArrow e :=
  traceArrow_of_valid_proof h

/-- Native equations are sound in the existing compatible Freyd class. -/
theorem valid_of_equiv {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A)
    (h : Equiv false Γ₀ β t u A) : Valid d e :=
  valid_of_equiv_proof d e h

/-- For an arbitrary exact common scrutinee, categorical trace arrow equality
is exactly agreement of the arms on every reachable tagged payload. -/
theorem traceArrow_case_eq_iff_replies {n : Nat} {β : BoundCtx (Ty α) n}
    {A B D : Ty α} {scr : Tm Empty Φ n} {l l' r r' : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dl' : Derivation Φ Γ₀ (β.snoc A) l' D)
    (dr : Derivation Φ Γ₀ (β.snoc B) r D) (dr' : Derivation Φ Γ₀ (β.snoc B) r' D) :
    traceArrow (.case d dl dr) = traceArrow (.case d dl' dr') ↔
      ∀ ρ, RepliesAgree d dl dl' dr dr' ρ :=
  traceArrow_case_eq_iff_replies_proof d dl dl' dr dr'

/-- Lift arm reflectors through a common exact case when the scrutinee can
produce every tagged payload at each input. -/
theorem case_equiv_iff_valid {n : Nat} {β : BoundCtx (Ty α) n}
    {A B D : Ty α} {scr : Tm Empty Φ n} {l l' r r' : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dl' : Derivation Φ Γ₀ (β.snoc A) l' D)
    (dr : Derivation Φ Γ₀ (β.snoc B) r D) (dr' : Derivation Φ Γ₀ (β.snoc B) r' D)
    (reaches : ∀ ρ (x : Value (.coprod A B)), ∃ w, (x, w) ∈ (run d ρ).outcomes)
    (left : traceArrow dl = traceArrow dl' → Equiv false Γ₀ (β.snoc A) l l' D)
    (right : traceArrow dr = traceArrow dr' → Equiv false Γ₀ (β.snoc B) r r' D) :
    Equiv false Γ₀ β (.case scr l r) (.case scr l' r') D ↔ Valid (.case d dl dr) (.case d dl' dr') :=
  case_equiv_iff_valid_proof d dl dl' dr dr' reaches left right

namespace EmptyBoundary

/-- The compatible class validates the existing empty-sequencing
counterexample at a packed unit input. -/
theorem valid : Valid direct sequenced :=
  empty_sequence_valid_proof scrutinee .unit

theorem unprovable :
    ¬ Equiv false (Φ := signature.Instr) Γ₀ input
      (.abort (.op true .unit)) (.let₁ (.op true .unit) (.abort (.bv 0))) (.unit : Ty Empty) :=
  unprovable_proof

end EmptyBoundary

end Silmaril.Isotope.LetCase.Structural.Reply
