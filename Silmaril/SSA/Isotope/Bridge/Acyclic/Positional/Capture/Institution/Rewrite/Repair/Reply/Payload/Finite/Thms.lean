module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Recovery
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Replay

/-! # Structural replay and validated reflection at arbitrary finite depth -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

open Isotope.LetCase.LocallyNameless (Derivation Equiv HasType Tm)
open Isotope.Semantics (BoundEnv)
open Kleisli (value)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Region (packedExitType)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "J" => Kleisli.J (m := Trace)

theorem Expr.quote_eval (n : Nat) (table : Table n) (env : Assignment n) :
    (Expr.quote n table).eval env = table env :=
  quote_eval_proof n table env

/-- A pure bit test can be inserted before a term
when both branches weaken that term through the fresh unit binder. -/
theorem ignored_bit_case {k : Nat} {β : BoundCtx Sorts k} {i : Fin k}
    {t : Tm Empty signature.Instr k} {A : Sorts}
    (read : HasType signature.Instr Γ₀ β (.bv i) Bit)
    (body : HasType signature.Instr Γ₀ β t A) :
    Equiv false Γ₀ β t (.case (.bv i) t.lift t.lift) A :=
  ignore_case_proof read body

/-- A terminal expression replays its finite table at the actual typed slots. -/
theorem Expr.replay {n : Nat} (e : Expr n) {k : Nat} {β : BoundCtx Sorts k}
    (slots : Retained β n) :
    Equiv false Γ₀ β (e.operand slots).1 ((Expr.quote n e.eval).operand slots).1 Bit :=
  expr_replay_proof e slots

/-- The recursive replay is valid in an arbitrary open native context. -/
theorem Tree.replay {L : List Sorts} {n : Nat} (p : Tree L n)
    {k : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) :
    Equiv false Γ₀ β (p.operand slots).1 (p.normal.render.operand slots).1 (packedExitType L) :=
  tree_replay_proof p slots

theorem derive_normal (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0)
    (h : p.normal = q.normal) : Derivable false (equation H L p q) :=
  derive_normal_proof H L p q h

theorem derive_render (H : Sorts) (L : List Sorts) (p : Tree (H :: L) 0) :
    Derivable false (equation H L p p.normal.render) :=
  derive_render_proof H L p

theorem Retained.Matches.bind {k n : Nat} {β : BoundCtx Sorts k} {slots : Retained β n}
    {ρ : BoundEnv value β} {env : Assignment n} (h : slots.Matches ρ env) (b : Bool) :
    slots.bind.Matches (ρ.snoc (A := Bit) (bit b)) (env.push b) :=
  matches_bind_proof h b

/-- The pure test chooses a branch and extends the native context with unit. -/
theorem run_bit_case {k : Nat} {β : BoundCtx Sorts k} {A : Sorts}
    (ρ : BoundEnv value β) (d : Operand signature.Instr β Bit)
    (l r : Operand signature.Instr (β.snoc Ty.unit) A) (b : Bool)
    (read : Kleisli.run model d.2 ρ = pure (bit b)) :
    Kleisli.run model (Derivation.case d.2 l.2 r.2) ρ =
      Kleisli.run model (if b then r else l).2 (ρ.snoc (A := Ty.unit) PUnit.unit) :=
  run_bit_case_proof ρ d l r b read

/-- A normalized open subtree evaluates at its retained assignment. Each
request extends that assignment using the payload from its single evaluation. -/
theorem Normal.run {L : List Sorts} {n : Nat} (p : Normal L n)
    {k : Nat} {β : BoundCtx Sorts k} (slots : Retained β n)
    (ρ : BoundEnv value β) (env : Assignment n) (h : slots.Matches ρ env)
    (finish : value (packedExitType L) → Trace (value (packedExitType L)))
    (onReturn : ∀ x : Exits.Exit L, finish x.packed = pure x.packed) :
    (Kleisli.run model (p.render.operand slots).2 ρ >>= finish).outcomes = p.outcomes env :=
  normal_run_proof p slots ρ env h finish onReturn

/-- All assignments recover the open normal form. Distinct next
request labels identify the retained slot tested by a guard. -/
theorem Normal.traceTree_inj {L : List Sorts} {n : Nat} (p q : Normal L n)
    (h : ∀ env, p.traceTree env = q.traceTree env) : p = q :=
  traceTree_inj_proof p q h

theorem Normal.afterRequest {L : List Sorts} {n : Nat} (req : Bool) (l r : Normal L (n + 1))
    (env : Assignment n) (right b : Bool) :
    afterPayload req right b ((Normal.request req l r).outcomes env) =
      (if right then r else l).outcomes (env.push b) :=
  after_request_proof req l r env right b

/-- Read the selected request and extend the untested slots with its reply. -/
theorem Normal.afterTestRequest {L : List Sorts} {n : Nat}
    (test : Fin (n + 1)) (low : Bool) (falseLeft falseRight trueLeft trueRight : Normal L (n + 1))
    (env : Assignment (n + 1)) (right b : Bool) :
    afterPayload (if env test then !low else low) right b
        ((Normal.testRequest test low falseLeft falseRight trueLeft trueRight).outcomes env) =
      (if env test then (if right then trueRight else trueLeft) else (if right then falseRight else falseLeft)).outcomes
        ((env.without test).push b) :=
  after_test_request_proof test low falseLeft falseRight trueLeft trueRight env right b

/-- Evaluation of the actual packed term agrees with the independently
enumerated finite paths, including their ordered exit tags. -/
theorem programOutcomes_eq (H : Sorts) (L : List Sorts) (p : Tree (H :: L) 0) :
    programOutcomes H L p = p.normal.outcomes Fin.elim0 :=
  programOutcomes_proof H L p

theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0) :
    programOutcomes H L p = programOutcomes H L q ↔ p.normal = q.normal := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => outcomes_injective_proof _ h, congrArg (fun p : Normal (H :: L) 0 => p.outcomes Fin.elim0)⟩

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ p.normal = q.normal :=
  (Payload.separator_sat_iff _).trans
    ⟨fun h => (programOutcomes_iff_normal H L p q).mp (programOutcomes_eq_of_sat_proof H L p q h),
      fun h => Kleisli.sat_of_repaired model model_respectsPure _ (Repaired.ofNative (derive_normal H L p q h))⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Repaired false (equation H L p q) :=
  ⟨fun h => Repaired.ofNative (derive_normal H L p q ((separator_sat_iff_normal H L p q).mp h)),
    fun h => (Payload.separator_sat_iff _).mpr (Kleisli.sat_of_repaired model model_respectsPure _ h)⟩

/-- Validity in the existing validated class reflects to native
derivability on the finite tree grammar. -/
theorem derive_of_validated_valid (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0)
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Derivable false (equation H L p q) :=
  derive_normal H L p q ((separator_sat_iff_normal H L p q).mp (valid separator))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
