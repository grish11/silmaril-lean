module

public import Silmaril.Logic.Temporal.LTL.Defs
public import Silmaril.Proofs.Logic.Temporal.LtlUntil

@[expose] public section

namespace Silmaril.Logic.Temporal.LTL

open Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

variable {P Q R : Type}

theorem Formula.eventually_iff (M : Model P) (p : Formula P) (n : Nat) :
    (eventually p).Holds M n ↔ ∃ d : Nat, p.Holds M (n + d) := by
  simp [eventually, top, Holds]

theorem Formula.always_iff (M : Model P) (p : Formula P) (n : Nat) :
    (always p).Holds M n ↔ ∀ d : Nat, p.Holds M (n + d) := by
  classical
  simp [always, eventually_iff, Holds]

theorem Formula.until_now (M : Model P) (p q : Formula P) (n : Nat)
    (hq : q.Holds M n) : (Formula.until p q).Holds M n :=
  ⟨0, by simpa only [Nat.add_zero] using hq, fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩

theorem Formula.until_eventually (M : Model P) (p q : Formula P) (n : Nat)
    (h : (Formula.until p q).Holds M n) : (eventually q).Holds M n :=
  (eventually_iff M q n).mpr ⟨h.choose, h.choose_spec.1⟩

/-- Strong until either finishes now, or continues for one step. -/
theorem Formula.until_unfold (M : Model P) (p q : Formula P) (n : Nat) :
    (Formula.until p q).Holds M n ↔
      q.Holds M n ∨ (p.Holds M n ∧ (Formula.until p q).Holds M (n + 1)) :=
  until_unfold_proof M p q n

theorem Formula.always_now (M : Model P) (p : Formula P) (n : Nat)
    (h : (always p).Holds M n) : p.Holds M n := by
  simpa only [Nat.add_zero] using (always_iff M p n).mp h 0

theorem Formula.always_next (M : Model P) (p : Formula P) (n : Nat)
    (h : (always p).Holds M n) : (always p).Holds M (n + 1) := by
  apply (always_iff M p (n + 1)).mpr
  intro d
  simpa only [Nat.add_assoc] using (always_iff M p n).mp h (1 + d)

/-- Exact SAT transport for the propositional inclusion. -/
theorem propositional_sat_iff (p : PL.Formula P) :
    (∃ v : PL.Model P, PL.Formula.eval v.val p) ↔
      ∃ M : Model P, Sat M (encodePropositional p) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨ULift.up (fun _ => v.val), (encodePropositional_holds _ p 0).mpr hv⟩
  · rintro ⟨M, hp⟩
    exact ⟨(initialValuation P).obj M, (encodePropositional_holds M p 0).mp hp⟩

theorem propositional_unsat_iff (p : PL.Formula P) :
    (¬ ∃ v : PL.Model P, PL.Formula.eval v.val p) ↔
      ¬ ∃ M : Model P, Sat M (encodePropositional p) :=
  not_congr (propositional_sat_iff p)

theorem propositional_entails_iff (H : Set (PL.Formula P)) (p : PL.Formula P) :
    (PL.room P).Entails H p ↔ (room P).Entails (encodePropositional '' H) (encodePropositional p) :=
  propositionalToLtl.entails_iff propositionalToLtl_modelExpansive P H p

/-- info: 'Silmaril.Logic.Temporal.LTL.propositional_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms propositional_entails_iff

end Silmaril.Logic.Temporal.LTL
