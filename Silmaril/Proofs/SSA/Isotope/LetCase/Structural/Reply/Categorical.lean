module

public import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Reply.Trace
import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms

public section

namespace Silmaril.Isotope.LetCase.Structural.Reply

open CategoryTheory
open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Isotope.Semantics (BoundEnv)
open LetIter.Semantics.Categorical
open LetSeq.StraightLine.Structural (model)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped MonoidalCategory LetSeq.StraightLine.Structural

local notation "Value" => LetSeq.StraightLine.Structural.Value

variable {α Φ : Type} [HasTy Φ (Ty α)]
set_option backward.isDefEq.respectTransparency false

theorem traceArrow_apply_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (ρ : boundObj (traceTypes α) β) :
    (traceArrow d).of (PUnit.unit, ρ) = run d (boundEnv Value ρ) := by
  simp only [traceArrow, denoteOfType_eq, Morphism.CaseIter.denote_derivation, run]
  congr 1
  funext x
  exact x.elim

omit [HasTy Φ (Ty α)] in
private theorem boundEnv_surjective {n : Nat} (β : BoundCtx (Ty α) n) :
    Function.Surjective (boundEnv Value (β := β)) := by
  induction β with
  | nil =>
    intro ρ
    exact ⟨PUnit.unit, funext (fun i => i.elim0)⟩
  | @snoc _ β A ih =>
    intro ρ
    obtain ⟨packed, equal⟩ := ih (fun i => ρ i.succ)
    refine ⟨(packed, ρ 0), ?_⟩
    rw [boundEnv_snoc, equal]
    exact funext (Fin.cases rfl (fun _ => rfl))

theorem traceArrow_eq_iff_run_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) :
    traceArrow d = traceArrow e ↔ ∀ ρ, run d ρ = run e ρ := by
  constructor
  · intro eq ρ
    obtain ⟨packed, rfl⟩ := boundEnv_surjective β ρ
    rw [← traceArrow_apply_proof, ← traceArrow_apply_proof, eq]
  · intro eq
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext ⟨γ, ρ⟩
    cases γ
    rw [traceArrow_apply_proof, traceArrow_apply_proof]
    exact eq _

theorem traceArrow_of_valid_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ n} {A : Ty α}
    {d : Derivation Φ Γ₀ β t A} {e : Derivation Φ Γ₀ β u A}
    (h : Valid d e) : traceArrow d = traceArrow e := by
  classical
  let := traceInstructions (α := α) (Φ := Φ)
  exact h (traceJ (α := α) (Φ := Φ)) (traceTypes α)
    (typingCoherent_ofType (ν := Empty) (fun _ : α => Nat) (model (Φ := Φ)))
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ hf => by cases hf)

theorem valid_of_equiv_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A)
    (h : Equiv false Γ₀ β t u A) : Valid d e := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr coherent shared pureInstr
  exact denote_equiv_of_coherent_shared_tensor J M coherent shared pureInstr
    (Morphism.CaseIter.embed_equiv h) (Morphism.CaseIter.derivation d) (Morphism.CaseIter.derivation e)

theorem traceArrow_case_eq_iff_replies_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {A B D : Ty α} {scr : Tm Empty Φ n} {l l' r r' : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dl' : Derivation Φ Γ₀ (β.snoc A) l' D)
    (dr : Derivation Φ Γ₀ (β.snoc B) r D) (dr' : Derivation Φ Γ₀ (β.snoc B) r' D) :
    traceArrow (.case d dl dr) = traceArrow (.case d dl' dr') ↔
      ∀ ρ, RepliesAgree d dl dl' dr dr' ρ := by
  rw [traceArrow_eq_iff_run_proof]
  exact ⟨fun h ρ => (run_case_eq_iff_replies_proof d dl dl' dr dr' ρ).mp (h ρ),
    fun h ρ => (run_case_eq_iff_replies_proof d dl dl' dr dr' ρ).mpr (h ρ)⟩

theorem case_equiv_iff_valid_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {A B D : Ty α} {scr : Tm Empty Φ n} {l l' r r' : Tm Empty Φ (n + 1)}
    (d : Derivation Φ Γ₀ β scr (.coprod A B))
    (dl : Derivation Φ Γ₀ (β.snoc A) l D) (dl' : Derivation Φ Γ₀ (β.snoc A) l' D)
    (dr : Derivation Φ Γ₀ (β.snoc B) r D) (dr' : Derivation Φ Γ₀ (β.snoc B) r' D)
    (reaches : ∀ ρ (x : Value (.coprod A B)), ∃ w, (x, w) ∈ (run d ρ).outcomes)
    (left : traceArrow dl = traceArrow dl' → Equiv false Γ₀ (β.snoc A) l l' D)
    (right : traceArrow dr = traceArrow dr' → Equiv false Γ₀ (β.snoc B) r r' D) :
    Equiv false Γ₀ β (.case scr l r) (.case scr l' r') D ↔ Valid (.case d dl dr) (.case d dl' dr') := by
  refine ⟨valid_of_equiv_proof _ _, fun h => ?_⟩
  have replies := (traceArrow_case_eq_iff_replies_proof d dl dl' dr dr').mp (traceArrow_of_valid_proof h)
  have leftEq := (traceArrow_eq_iff_run_proof dl dl').mpr (fun σ => by
    let ρ : BoundEnv Value β := fun i => σ i.succ
    obtain ⟨w, hw⟩ := reaches ρ (.inl (σ 0))
    have env : ρ.snoc (σ 0) = σ := funext (Fin.cases rfl (fun _ => rfl))
    simpa only [env] using (replies ρ).1 (σ 0) w hw)
  have rightEq := (traceArrow_eq_iff_run_proof dr dr').mpr (fun σ => by
    let ρ : BoundEnv Value β := fun i => σ i.succ
    obtain ⟨w, hw⟩ := reaches ρ (.inr (σ 0))
    have env : ρ.snoc (σ 0) = σ := funext (Fin.cases rfl (fun _ => rfl))
    simpa only [env] using (replies ρ).2 (σ 0) w hw)
  exact .case (.refl d.toHasType) (left leftEq) (right rightEq)

end Silmaril.Isotope.LetCase.Structural.Reply
