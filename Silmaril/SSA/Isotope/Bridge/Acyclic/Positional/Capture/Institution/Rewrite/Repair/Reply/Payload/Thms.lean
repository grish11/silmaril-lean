module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Recovery
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Replay

/-! # Native replay and validated reflection of finite payload tables -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Isotope.LetCase.LocallyNameless (Equiv)
open Isotope.Semantics (BoundEnv InstructionModel)
open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Acyclic (FiniteExit Operand)
open LambdaSSA.Region (packedExitType)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => Kleisli.J (m := Trace)

/-- Native sum η and unit η with pure let β turn a live bit into its two
constructor entries. The table retains the expression's two values. -/
theorem Expr.replay (e : Expr) {n : Nat} (β : BoundCtx Sorts n) (i : Fin n)
    (h : β.get i = Bit) :
    Equiv false (Ctx.nil : Ctx Empty Sorts) β (e.operand β i h).1
      ((Expr.table (e.evaluate false) (e.evaluate true)).operand β i h).1 Bit :=
  expr_replay_proof e β i h

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

theorem tag_congr {n : Nat} {β : BoundCtx Sorts n} (L : List Sorts) (i : Nat)
    {A : Sorts} (h : At L i A) (a b : Operand signature.Instr β A)
    (eq : Equiv false Γ₀ β a.1 b.1 A) :
    Equiv false Γ₀ β (FiniteExit.tag L i h a).1 (FiniteExit.tag L i h b).1 (packedExitType L) :=
  tag_congr_proof L i h a b eq

/-- Replay an arm at a live payload slot in any ambient context. -/
theorem Arm.replay_at {L : List Sorts} (a : Arm L) (effects : List Bool)
    {n : Nat} (β : BoundCtx Sorts n) (i : Fin n) (h : β.get i = Bit) :
    Equiv false Γ₀ β (a.renderPrefix effects β i h).1
      (a.normal.render.renderPrefix effects β i h).1 (packedExitType L) :=
  arm_replay_at_proof a effects β i h

/-- Normalize case binding in an open context while preserving a single
request and replaying its arms under their native payload binders. -/
theorem request_replay {n : Nat} {β : BoundCtx Sorts n} {A : Sorts}
    (req bound : Bool) (l r l' r' : Operand signature.Instr (β.snoc Bit) A)
    (hl : Equiv false Γ₀ (β.snoc Bit) l.1 l'.1 A)
    (hr : Equiv false Γ₀ (β.snoc Bit) r.1 r'.1 A) :
    Equiv false Γ₀ β (requestOperand req bound l r).1 (requestOperand req false l' r').1 A :=
  request_replay_proof req bound l r l' r' hl hr

/-- Replay in the actual packed terms, including effectful case binding
and the shared native exit continuation. -/
theorem derive_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : p.normal = q.normal) : Derivable false (equation H L p q) :=
  derive_normal_proof H L p q h

theorem derive_render (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Derivable false (equation H L p p.normal.render) :=
  derive_render_proof H L p

theorem model_respectsPure : InstructionModel.RespectsPure (ε := Bool) model :=
  model_pure_proof

/-- The free-type trace algebra has coherent native region witnesses. -/
theorem modelCoherent :
    letI := Kleisli.instructions model
    LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr) J Kleisli.types :=
  Kleisli.regionCoherent model model_pure_proof (Tagged.ofOutcomes ∅)

/-- The separator belongs to the existing validated room at the reply-payload signature. -/
noncomputable def separator : (grammarRoom J signature).Mod :=
  Kleisli.validated model modelCoherent

theorem separator_sat_iff (e : GrammarEquation signature) :
    (grammarRoom J signature).Sat separator e ↔
      ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase e) :=
  Kleisli.validated_sat_iff model modelCoherent e

theorem run_bitOperand {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) (b : Bool) :
    Kleisli.run model (bitOperand β b).2 ρ = pure (bit b) :=
  bit_operand_run_proof ρ b

theorem run_readPayload {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β)
    (i : Fin n) (h : β.get i = Bit) (b : Bool) (hi : h ▸ ρ i = bit b) :
    Kleisli.run model (readPayload β i h).2 ρ = pure (bit b) :=
  read_payload_run_proof ρ i h b hi

theorem Position.pack_result {L : List Sorts} (p : Position L) (b : Bool) :
    Exits.packAt L p.1 p.typed (bit b) = (p.result b).packed :=
  position_pack_result_proof p b

theorem Position.result_inj {L : List Sorts} {p q : Position L} {x y : Bool}
    (h : p.result x = q.result y) : p = q ∧ x = y :=
  position_result_inj_proof h

theorem requestTree_inj {R : Type} {req req' : Bool} {l r l' r' : Bool → Reply.Normal R}
    (h : requestTree req l r = requestTree req' l' r') :
    req = req' ∧ (∀ b, l b = l' b) ∧ (∀ b, r b = r' b) :=
  requestTree_inj_proof h

/-- Run the witnessed arm with an older payload still live at a typed slot. -/
theorem ArmNormal.run_at {L : List Sorts} (a : ArmNormal L)
    {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) (i : Fin n)
    (h : β.get i = Bit) (b : Bool) (hi : h ▸ ρ i = bit b)
    (finish : value (packedExitType L) → Trace (value (packedExitType L)))
    (onReturn : finish (a.result b).packed = pure (a.result b).packed) :
    (Kleisli.run model (a.render.renderPrefix a.emits β i h).2 ρ >>= finish).outcomes =
      (a.traceTree b).outcomesWith Exits.Exit.packed :=
  arm_run_at_proof a a.emits ρ i h b hi finish onReturn

/-- A direct native request sequences one primitive evaluation before
selecting the continuation for its exact reply. -/
theorem request_run {n : Nat} {β : BoundCtx Sorts n} {T : Sorts} {R A : Type}
    (req : Bool) (l r : Operand signature.Instr (β.snoc Bit) T)
    (ρ : BoundEnv value β) (finish : value T → Trace A) (success : R → A)
    (left right : Bool → Reply.Normal R)
    (hl : ∀ b, (Kleisli.run model l.2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes =
      (left b).outcomesWith success)
    (hr : ∀ b, (Kleisli.run model r.2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes =
      (right b).outcomesWith success) :
    (Kleisli.run model (requestOperand req false l r).2 ρ >>= finish).outcomes =
      (requestTree req left right).outcomesWith success :=
  request_run_proof req l r ρ finish success left right hl hr

theorem afterRequest {R A : Type} (success : R → A) (req : Bool)
    (l r : Bool → Reply.Normal R) (right b : Bool) :
    afterPayload req right b ((requestTree req l r).outcomesWith success) =
      ((if right then r else l) b).outcomesWith success :=
  afterRequest_proof success req l r right b

theorem ArmNormal.traceTree_inj {L : List Sorts} (p q : ArmNormal L)
    (h₀ : p.traceTree false = q.traceTree false) (h₁ : p.traceTree true = q.traceTree true) :
    p = q :=
  arm_traceTree_inj_proof p q h₀ h₁

/-- The actual packed term has the independently enumerated observations. -/
theorem programOutcomes_eq (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    programOutcomes H L p = p.normal.outcomes :=
  programOutcomes_proof H L p

/-- The exact reply fields, ordered effects, exit position, and result recover
the normal form. Distinct source expressions can have the same table. -/
theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    programOutcomes H L p = programOutcomes H L q ↔ p.normal = q.normal := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => outcomes_injective_proof _ h, congrArg Normal.outcomes⟩

/-- Observe one selected reply value at its original arm and ordered exit. -/
theorem programAfterPayload (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L))
    (right b : Bool) :
    afterPayload p.request right b (programOutcomes H L p) =
      ((if right then p.normal.right else p.normal.left).traceTree b).outcomesWith Exits.Exit.packed :=
  (congrArg (afterPayload p.request right b) (programOutcomes_eq H L p)).trans
    (afterPayload_proof p.normal right b)

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ p.normal = q.normal :=
  (separator_sat_iff _).trans
    ⟨fun h => (programOutcomes_iff_normal H L p q).mp (programOutcomes_eq_of_sat_proof H L p q h),
      fun h => Kleisli.sat_of_repaired model model_pure_proof _ (Repaired.ofNative (derive_normal H L p q h))⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Repaired false (equation H L p q) :=
  ⟨fun h => Repaired.ofNative (derive_normal H L p q ((separator_sat_iff_normal H L p q).mp h)),
    fun h => (separator_sat_iff _).mpr
      (Kleisli.sat_of_repaired model model_pure_proof _ h)⟩

/-- Validity in the whole existing model class reflects to the native rules on
this fragment. Its replay requires only the original LetCase equations. -/
theorem derive_of_validated_valid (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Derivable false (equation H L p q) :=
  derive_normal H L p q ((separator_sat_iff_normal H L p q).mp (valid separator))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
