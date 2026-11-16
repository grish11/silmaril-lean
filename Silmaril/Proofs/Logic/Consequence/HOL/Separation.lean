module

public import Silmaril.Logic.Consequence.HOL.Defs
public import Silmaril.Logic.HOLLight.Consistency
public import Silmaril.Logic.HOLLight.Semantics.Logic

/-! Concrete HOL separations for `Silmaril.Logic.Consequence.HOL.Examples`: over the initial
signature, the free boolean variables `x = fvar 0 bool`, `y = fvar 1 bool` and `¬x`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.HOL

open Silmaril.Consequence Silmaril.Consequence.HOL Silmaril.Logic.HOLLight
open Silmaril.Logic.Institution.Metatheory (HolSig)

/-- The initial HOL signature. -/
def S₀ : HolSig := ⟨initialSignature⟩

/-- A type valuation. -/
noncomputable def ρ₀ : TypeValuation.{0} := fun _ => Carrier.unit

/-- The assignment sending every boolean variable `n` to `b n`. -/
noncomputable def env (b : Nat → Bool) : FreeEnv Model.standard.{0} ρ₀ := fun n A =>
  if h : A = .bool then h ▸ (if b n then Carrier.truth else Carrier.falsity)
  else Classical.choice inferInstance

/-- The free boolean variable `n`. -/
def var (n : Nat) : HOLProp S₀ := ⟨.fvar n .bool, .fvar n trivial⟩

/-- `¬ x₀`. -/
def notVar (n : Nat) : HOLProp S₀ :=
  ⟨Tm.neg (.fvar n .bool),
    (Eval.neg (Eval.fvar (ν := env fun _ => true) BoundEnv.empty n trivial)).typing⟩

theorem holds_var {M : Model.{0} S₀.sig} {ρ : TypeValuation.{0}} {ν : FreeEnv M ρ} (n : Nat) :
    Holds M ρ ν (var n).1 ↔ Carrier.Truth (ν n .bool) :=
  ⟨fun ⟨_, hv, ht⟩ => (hv.unique (Eval.fvar BoundEnv.empty n trivial)) ▸ ht,
    fun h => ⟨_, Eval.fvar BoundEnv.empty n trivial, h⟩⟩

theorem holds_notVar {M : Model.{0} S₀.sig} {ρ : TypeValuation.{0}} {ν : FreeEnv M ρ} (n : Nat) :
    Holds M ρ ν (notVar n).1 ↔ ¬ Carrier.Truth (ν n .bool) := by
  have he := Eval.neg (Eval.fvar (M := M) (ν := ν) BoundEnv.empty n (A := .bool) trivial)
  constructor
  · rintro ⟨_, hv, ht⟩
    exact (Carrier.truth_neg _).1 ((hv.unique he) ▸ ht)
  · exact fun h => ⟨_, he, (Carrier.truth_neg _).2 h⟩

theorem truth_env (b : Nat → Bool) (n : Nat) :
    Carrier.Truth (env b n .bool) ↔ b n = true := by
  cases hb : b n <;> simp [env, hb]

/-- `x ⊢ y` fails point-wise. -/
theorem not_seq_var : ¬ seq.{0} S₀ [var 0] (var 1) := by
  intro h
  have := h ⟨Model.standard, ρ₀, env fun n => n == 0⟩ fun q hq => by
    rw [List.mem_singleton.1 hq]; exact (holds_var 0).2 ((truth_env _ 0).2 rfl)
  exact absurd ((truth_env _ 1).1 ((holds_var 1).1 this)) (by decide)

/-- `x ⊢ y` holds model-wise: no model validates a free boolean variable. -/
theorem globalSeq_var : globalSeq.{0} S₀ [var 0] (var 1) := by
  intro M hM
  have hx := hM (var 0) (by simp) ⟨ρ₀, fun n A => if h : A = .bool then h ▸ Carrier.falsity
    else Classical.choice inferInstance⟩
  simp [satAt, holds_var] at hx

/-- `⊢ x, ¬x` holds point-wise. -/
theorem gentzen_excluded : gentzen.{0} S₀ [] [var 0, notVar 0] := by
  rintro ⟨M, ρ, ν⟩ -
  by_cases h : Carrier.Truth (ν 0 .bool)
  · exact ⟨var 0, by simp, (holds_var 0).2 h⟩
  · exact ⟨notVar 0, by simp, (holds_notVar 0).2 h⟩

/-- `⊢ x, ¬x` fails model-wise: neither is valid in the standard model. -/
theorem not_globalGentzen_excluded : ¬ globalGentzen.{0} S₀ [] [var 0, notVar 0] := by
  intro h
  obtain ⟨d, hd, hv⟩ := h Model.standard (by simp [Refutation.SatAll])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact absurd ((truth_env _ 0).1 ((holds_var 0).1 (hv ⟨ρ₀, env fun _ => false⟩))) (by decide)
  · exact (holds_notVar 0).1 (hv ⟨ρ₀, env fun _ => true⟩) ((truth_env _ 0).2 rfl)

end Silmaril.Proofs.Logic.Consequence.HOL
