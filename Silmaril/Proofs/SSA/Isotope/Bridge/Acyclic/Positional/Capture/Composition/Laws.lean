module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition

open Region (packedExitType)
open Reverse (CheckedTable checkedSetoid operandSetoid)
open LetCase.Structural.Finite (Context StructuralContext equiv_iff_traceArrow_eq_snoc)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀ run traceArrow traceArrow_eq_iff_run valid_of_equiv traceArrow_of_valid)
open Isotope.Semantics (BoundEnv)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open LambdaSSA.Semantics.Categorical (denoteRegion)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

local notation "Val" => LetCase.Structural.Finite.Value

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
  {β : Context d} {I J K : LCtx (Ty Empty)}

set_option backward.isDefEq.respectTransparency false

theorem seq_run_proof (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K)
    (env : BoundEnv Val β) (x : Val (packedExitType I)) :
    run (seq p q).toLetCase.2 (env.snoc x) =
      (run p.toLetCase.2 (env.snoc x) >>= fun y => run q.toLetCase.2 (env.snoc y)) := by
  let receiver := weaken I q
  have stage := Link.Open.serial_run p.table receiver.table p.checked receiver.checked
    0 0 p.entry receiver.entry (env.snoc x)
  refine stage.trans ?_
  exact congrArg (fun f => run p.toLetCase.2 (env.snoc x) >>= f)
    (funext (Link.Open.weaken_receiver_run q.table q.checked 0 q.entry env x))

private theorem replay_run {n : Nat} {γ : Context n} {L : LCtx (Ty Empty)}
    {p q : CheckedTable Φ γ L} (eq : (checkedSetoid Φ γ L).r p q) (env : BoundEnv Val γ) :
    run p.toLetCase.2 env = run q.toLetCase.2 env := by
  let := traceInstructions (α := Empty) (Φ := Φ)
  let := Native.trace_region_coherent (Φ := Φ)
  let F := traceJ (α := Empty) (Φ := Φ)
  let M := traceTypes Empty
  have packed := ReplayEqv.sound F M (fun _ _ => ⟨rfl, rfl⟩) eq
    (p.table.packedSSA_hasType 0 p.entry) (q.table.packedSSA_hasType 0 q.entry)
  have lc := (p.table.packed_denote_iff F M (fun _ _ => ⟨rfl, rfl⟩) q.table
    p.checked q.checked 0 0 p.entry q.entry).mp packed
  apply (traceArrow_eq_iff_run p.toLetCase.2 q.toLetCase.2).mp _ env
  unfold traceArrow LetIter.Semantics.Categorical.denoteOfType
  rw [Native.denote_caseIter F M, Native.denote_caseIter F M]
  exact lc

private theorem reflect_operand_run (input : StructuralContext β)
    (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType K))
    (eq : ∀ env : BoundEnv Val β, ∀ x : Val (packedExitType I),
      run a.2 (env.snoc x) = run b.2 (env.snoc x)) :
    (operandSetoid Φ (β.snoc (packedExitType I)) K).r a b := by
  apply (equiv_iff_traceArrow_eq_snoc input _ _).mpr
  apply (traceArrow_eq_iff_run _ _).mpr
  intro ρ
  have split : (BoundEnv.snoc (fun i => ρ i.succ) (ρ 0) : BoundEnv Val (β.snoc (packedExitType I))) = ρ :=
    funext (Fin.cases rfl (fun _ => rfl))
  rw [← split]
  exact eq _ _

private theorem replay_of_emit_equiv {n : Nat} {γ : Context n} {L : LCtx (Ty Empty)}
    (p q : CheckedTable Φ γ L) (eq : (operandSetoid Φ γ L).r p.toLetCase q.toLetCase) :
    (checkedSetoid Φ γ L).r p q :=
  p.table.packed_replay_of_equiv q.table p.checked q.checked 0 0 p.entry q.entry finite_pureLetBetaReplay eq

private theorem reflect_run (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) K)
    (eq : ∀ env : BoundEnv Val β, ∀ x : Val (packedExitType I),
      run p.toLetCase.2 (env.snoc x) = run q.toLetCase.2 (env.snoc x)) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) K).r p q :=
  replay_of_emit_equiv p q (reflect_operand_run input p.toLetCase q.toLetCase eq)

theorem emit_equiv_iff_replay_proof (input : StructuralContext β)
    (p q : CheckedTable Φ (β.snoc (packedExitType I)) K) :
    (operandSetoid Φ (β.snoc (packedExitType I)) K).r p.toLetCase q.toLetCase ↔
      (checkedSetoid Φ (β.snoc (packedExitType I)) K).r p q :=
  ⟨replay_of_emit_equiv p q, fun h => reflect_operand_run input p.toLetCase q.toLetCase
    (fun env x => replay_run h (env.snoc x))⟩

theorem emit_seq_equiv_proof (input : StructuralContext β)
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K) :
    (operandSetoid Φ (β.snoc (packedExitType I)) K).r
      (seq p q).toLetCase (Case.seq p.toLetCase q.toLetCase) := by
  apply reflect_operand_run input
  intro env x
  rw [seq_run_proof]
  change _ = (run p.toLetCase.2 (env.snoc x) >>= fun y =>
    run (q.toLetCase.2.underBinder (X := packedExitType I)) ((env.snoc x).snoc y))
  simp only [Link.Open.underBinder_run]

theorem readback_respects_proof (h : K ≠ [])
    {a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType K)}
    (eq : (operandSetoid Φ (β.snoc (packedExitType I)) K).r a b) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) K).r
      (CheckedTable.ofLetCase h a.2) (CheckedTable.ofLetCase h b.2) :=
  replay_of_emit_equiv _ _
    ((CheckedTable.ofLetCase_emit false h a.2).trans
      (LetCase.LocallyNameless.Equiv.trans eq (CheckedTable.ofLetCase_emit false h b.2).symm))

theorem seq_congr_proof (input : StructuralContext β)
    {p₁ p₂ : CheckedTable Φ (β.snoc (packedExitType I)) J}
    {q₁ q₂ : CheckedTable Φ (β.snoc (packedExitType J)) K}
    (hp : (checkedSetoid Φ (β.snoc (packedExitType I)) J).r p₁ p₂)
    (hq : (checkedSetoid Φ (β.snoc (packedExitType J)) K).r q₁ q₂) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) K).r (seq p₁ q₁) (seq p₂ q₂) := by
  apply reflect_run input
  intro ρ x
  rw [seq_run_proof, seq_run_proof, replay_run hp]
  exact congrArg (fun f => run p₂.toLetCase.2 (ρ.snoc x) >>= f)
    (funext fun y => replay_run hq (ρ.snoc y))

private theorem identity_run (h : I ≠ []) (env : BoundEnv Val β) (x : Val (packedExitType I)) :
    run (identity (Φ := Φ) (β := β) h).toLetCase.2 (env.snoc x) = pure x := by
  let p := identity (Φ := Φ) (β := β) h
  have sound := traceArrow_of_valid (valid_of_equiv p.toLetCase.2 p.entry.2 (Link.identity_equiv h p.entry))
  exact (traceArrow_eq_iff_run p.toLetCase.2 p.entry.2).mp sound (env.snoc x)

theorem left_identity_proof (input : StructuralContext β) (h : I ≠ [])
    (q : CheckedTable Φ (β.snoc (packedExitType I)) K) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) K).r (seq (identity h) q) q := by
  apply reflect_run input
  intro ρ x
  rw [seq_run_proof, identity_run, pure_bind]

theorem right_identity_proof (input : StructuralContext β) (h : J ≠ [])
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) J).r (seq p (identity h)) p := by
  apply reflect_run input
  intro ρ x
  rw [seq_run_proof]
  simp only [identity_run, bind_pure]

theorem associative_proof {L : LCtx (Ty Empty)} (input : StructuralContext β)
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K)
    (r : CheckedTable Φ (β.snoc (packedExitType K)) L) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) L).r (seq (seq p q) r) (seq p (seq q r)) := by
  apply reflect_run input
  intro ρ x
  simp only [seq_run_proof, bind_assoc]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition
