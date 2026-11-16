module

public import Silmaril.Logic.Szs.Defs
public import Mathlib.Computability.Language
import Silmaril.Proofs.Logic.Szs.Basic

/-!
# The SZS ontology: lemmas

**Codes.** `ofCode?_code`, `code_injective`: the three-letter codes name the statuses one to one.

**THM and TAU.** `Current.tau_thm`, `Current.tau_iff_thm`: Tautology is Theorem with axioms
true in every interpretation; `Current.thm_not_tau` shows they differ in general. For a problem
without axioms they coincide (`monolithic_thm_iff_tau`), which is the 2007 rule "Systems that
report Theorem for a monolithic formula must have established Tautology".

**SAT, CSA, NOC, CAX, UCA.** `noc_iff_sat_and_csa`: SAT and CSA together are NoConsequence,
not UCA. `cax_iff_not_sat_and_not_csa`: neither SAT nor CSA is exactly ContradictoryAxioms.
`uca_cax`, `uca_not_sat`, `uca_not_csa`: UCA is the case of CAX whose conjecture has no models,
so it excludes both SAT and CSA.

**Problems without axioms.** `monolithic_*`: THM and TAU say every interpretation is a model of
`C`, SAT some is, CSA some is not, UNS none is, NOC some are and some are not. CAX and UCA hold
exactly when there are no interpretations at all (`monolithic_cax_iff`, `monolithic_uca_iff`).
`ofPred_*`: the statuses of the project's `@[answers]` shapes, `∀ x, P x` (THM, and TAU),
`∃ x, P x` (SAT), `∀ x, ¬ P x` (UNS), `∃ x, ¬ P x` (CSA), are these statuses of `ofPred P`.

**Languages.** `ofLanguage_*`: for a language `L`, THM/TAU is "universal", SAT "nonempty", UNS
"empty", CSA "not universal", NOC "nonempty and not universal"; CAX and UCA never hold (the
empty word is an interpretation). `relative_*`: with a domain language `D` as the axioms, THM is
`D ⊆ L`, SAT `D ∩ L` nonempty, CSA `D ⊄ L`, CTH `D ∩ L = ∅`, CAX `D = ∅`.

**The 2007 text against its diagram.** The 2007 diagram draws TAU below TAC and EQV below SAT,
and glosses CEQ as "Ax xor C"; its definitions, transcribed literally, do not support these:
`V2007.tau_not_tac`, `V2007.eqv_not_sat`, `V2007.ceq_conj_eq_empty`. The current definitions do:
`Current.tac_of_tau`, `Current.sat_of_eqv`, `Current.ceq_xor`. The codes whose definitions did
not change are equal by definition (`holds2007?_eq`).
-/

@[expose] public section

namespace Silmaril.Logic.Szs

universe u

open Problem

/-! ## Codes -/

theorem ofCode?_code (s : Status) : Status.ofCode? s.code = some s := by
  cases s <;> rfl

theorem code_injective : Function.Injective Status.code := fun a b h => by
  have := ofCode?_code a; rw [h, ofCode?_code] at this; exact (Option.some.inj this).symm

theorem all_complete (s : Status) : s ∈ Status.all := by cases s <;> decide

theorem all_nodup : Status.all.Nodup := by decide

/-! ## THM and TAU -/

variable {I : Type u}

theorem Current.tau_thm {P : Problem I} (h : Current.TAU P) : Current.THM P :=
  fun _ _ => h.2 ▸ Set.mem_univ _

theorem Current.tau_iff_thm {P : Problem I} :
    Current.TAU P ↔ Current.THM P ∧ P.ax = Set.univ :=
  Silmaril.Proofs.Logic.Szs.tau_iff_thm

/-- THM does not imply TAU: `Ax = C = {true}` over `Bool`. -/
theorem Current.thm_not_tau :
    ∃ P : Problem Bool, Current.THM P ∧ ¬ Current.TAU P :=
  Silmaril.Proofs.Logic.Szs.thm_not_tau

/-! ## SAT, CSA, NOC, CAX, UCA -/

theorem noc_iff_sat_and_csa {P : Problem I} :
    Current.NOC P ↔ Current.SAT P ∧ Current.CSA P :=
  ⟨fun ⟨h, hs, hc⟩ => ⟨⟨h, hs⟩, ⟨h, hc⟩⟩, fun ⟨⟨h, hs⟩, ⟨_, hc⟩⟩ => ⟨h, hs, hc⟩⟩

theorem cax_iff_not_sat_and_not_csa {P : Problem I} :
    Current.CAX P ↔ ¬ Current.SAT P ∧ ¬ Current.CSA P :=
  Silmaril.Proofs.Logic.Szs.cax_iff_not_sat_and_not_csa

theorem uca_cax {P : Problem I} (h : Current.UCA P) : Current.CAX P := h.1

theorem uca_not_sat {P : Problem I} (h : Current.UCA P) : ¬ Current.SAT P :=
  (cax_iff_not_sat_and_not_csa.mp h.1).1

theorem uca_not_csa {P : Problem I} (h : Current.UCA P) : ¬ Current.CSA P :=
  (cax_iff_not_sat_and_not_csa.mp h.1).2

theorem uca_not_noc {P : Problem I} (h : Current.UCA P) : ¬ Current.NOC P :=
  fun hn => uca_not_sat h (noc_iff_sat_and_csa.mp hn).1

/-! ## Problems without axioms -/

section Monolithic

variable {C : Set I}

theorem monolithic_thm_iff : Current.THM (monolithic C) ↔ ∀ i, i ∈ C :=
  ⟨fun h i => h (Set.mem_univ i), fun h i _ => h i⟩

theorem monolithic_thm_iff_tau : Current.THM (monolithic C) ↔ Current.TAU (monolithic C) :=
  Current.tau_iff_thm.trans (and_iff_left rfl) |>.symm

theorem monolithic_sat_iff : Current.SAT (monolithic C) ↔ ∃ i, i ∈ C :=
  ⟨fun ⟨_, i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨⟨i, Set.mem_univ i⟩, i, Set.mem_univ i, h⟩⟩

theorem monolithic_csa_iff : Current.CSA (monolithic C) ↔ ∃ i, i ∉ C :=
  ⟨fun ⟨_, i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨⟨i, Set.mem_univ i⟩, i, Set.mem_univ i, h⟩⟩

theorem monolithic_uns_iff : Current.UNS (monolithic C) ↔ ∀ i, i ∉ C :=
  (and_iff_right rfl).trans Set.eq_empty_iff_forall_notMem

theorem monolithic_noc_iff : Current.NOC (monolithic C) ↔ (∃ i, i ∈ C) ∧ ∃ i, i ∉ C :=
  noc_iff_sat_and_csa.trans (and_congr monolithic_sat_iff monolithic_csa_iff)

theorem monolithic_cax_iff : Current.CAX (monolithic C) ↔ IsEmpty I :=
  Set.univ_eq_empty_iff

theorem monolithic_uca_iff : Current.UCA (monolithic C) ↔ IsEmpty I :=
  ⟨fun h => monolithic_cax_iff.mp h.1, fun h => ⟨Set.univ_eq_empty_iff.mpr h,
    Set.eq_empty_iff_forall_notMem.mpr fun i => h.elim i⟩⟩

end Monolithic

/-! ## The project's answer shapes -/

section Pred

variable {α : Type u} {P : α → Prop}

theorem ofPred_thm_iff : Current.THM (ofPred P) ↔ ∀ x, P x := monolithic_thm_iff
theorem ofPred_tau_iff : Current.TAU (ofPred P) ↔ ∀ x, P x :=
  monolithic_thm_iff_tau.symm.trans monolithic_thm_iff
theorem ofPred_sat_iff : Current.SAT (ofPred P) ↔ ∃ x, P x := monolithic_sat_iff
theorem ofPred_uns_iff : Current.UNS (ofPred P) ↔ ∀ x, ¬ P x := monolithic_uns_iff
theorem ofPred_csa_iff : Current.CSA (ofPred P) ↔ ∃ x, ¬ P x := monolithic_csa_iff
theorem ofPred_noc_iff : Current.NOC (ofPred P) ↔ (∃ x, P x) ∧ ∃ x, ¬ P x := monolithic_noc_iff

end Pred

/-! ## Languages -/

/-- A language `L` as a problem without axioms over all words. -/
def ofLanguage {α : Type u} (L : Language α) : Problem (List α) := monolithic {w | w ∈ L}

/-- The language `L` restricted to the domain `D`: `D` plays the axioms. -/
def relative {α : Type u} (D L : Language α) : Problem (List α) := ⟨{w | w ∈ D}, {w | w ∈ L}⟩

section Lang

variable {α : Type u} {L D : Language α}

theorem ofLanguage_thm_iff : Current.THM (ofLanguage L) ↔ ∀ w, w ∈ L := monolithic_thm_iff
theorem ofLanguage_tau_iff : Current.TAU (ofLanguage L) ↔ ∀ w, w ∈ L :=
  monolithic_thm_iff_tau.symm.trans monolithic_thm_iff
theorem ofLanguage_sat_iff : Current.SAT (ofLanguage L) ↔ ∃ w, w ∈ L := monolithic_sat_iff
theorem ofLanguage_uns_iff : Current.UNS (ofLanguage L) ↔ ∀ w, w ∉ L := monolithic_uns_iff
theorem ofLanguage_uns_iff_eq_zero : Current.UNS (ofLanguage L) ↔ L = 0 :=
  monolithic_uns_iff.trans Silmaril.Proofs.Logic.Szs.forall_notMem_iff_eq_zero
theorem ofLanguage_csa_iff : Current.CSA (ofLanguage L) ↔ ∃ w, w ∉ L := monolithic_csa_iff
theorem ofLanguage_noc_iff : Current.NOC (ofLanguage L) ↔ (∃ w, w ∈ L) ∧ ∃ w, w ∉ L :=
  monolithic_noc_iff
theorem ofLanguage_not_cax : ¬ Current.CAX (ofLanguage L) := fun h =>
  (monolithic_cax_iff.mp h).elim []
theorem ofLanguage_not_uca : ¬ Current.UCA (ofLanguage L) := fun h => ofLanguage_not_cax h.1

theorem relative_thm_iff : Current.THM (relative D L) ↔ ∀ w ∈ D, w ∈ L := Iff.rfl
theorem relative_sat_iff : Current.SAT (relative D L) ↔ ∃ w ∈ D, w ∈ L :=
  ⟨fun ⟨_, h⟩ => h, fun ⟨w, hd, hl⟩ => ⟨⟨w, hd⟩, w, hd, hl⟩⟩
theorem relative_csa_iff : Current.CSA (relative D L) ↔ ∃ w ∈ D, w ∉ L :=
  ⟨fun ⟨_, h⟩ => h, fun ⟨w, hd, hl⟩ => ⟨⟨w, hd⟩, w, hd, hl⟩⟩
theorem relative_cth_iff : Current.CTH (relative D L) ↔ ∀ w ∈ D, w ∉ L := Iff.rfl
theorem relative_cax_iff : Current.CAX (relative D L) ↔ ∀ w, w ∉ D :=
  Set.eq_empty_iff_forall_notMem

end Lang

/-! ## The 2007 text against its diagram, and the current definitions -/

/-- 2007: with any interpretation, TAU excludes TAC (TAC asks that not all interpretations be
models of Ax), although the diagram draws TAU below TAC. -/
theorem V2007.tau_not_tac [Nonempty I] {P : Problem I} (h : V2007.TAU P) : ¬ V2007.TAC P :=
  fun ht => ht.1.2 h.1

/-- 2007: EQV does not ask that Ax have a model, so it does not imply SAT. -/
theorem V2007.eqv_not_sat : ∃ P : Problem Unit, V2007.EQV P ∧ ¬ V2007.SAT P :=
  ⟨⟨∅, ∅⟩, ⟨le_rfl, le_rfl⟩, fun ⟨⟨_, h⟩, _⟩ => h⟩

/-- 2007: CEQ as written ("all models of C are models of Ax") forces C to have no models. -/
theorem V2007.ceq_conj_eq_empty {P : Problem I} (h : V2007.CEQ P) : P.conj = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ hi => h.1 (h.2 hi) hi

theorem Current.tac_of_tau [Nonempty I] {P : Problem I} (h : Current.TAU P) : Current.TAC P :=
  ⟨h.1 ▸ Set.univ_nonempty, h.2⟩

theorem Current.sat_of_eqv {P : Problem I} (h : Current.EQV P) : Current.SAT P :=
  let ⟨i, hi⟩ := h.1; ⟨⟨i, hi⟩, i, hi, h.2.1 hi⟩

/-- Current CEQ: every interpretation is a model of exactly one of Ax and C. -/
theorem Current.ceq_xor {P : Problem I} (h : Current.CEQ P) (i : I) : i ∈ P.ax ↔ i ∉ P.conj :=
  ⟨fun hi => h.2.1 hi, fun hi => h.2.2 hi⟩

/-- The codes whose definition is the same in both sources. -/
theorem holds2007?_eq (P : Problem I) :
    ∀ s ∈ [Status.SAT, .THM, .ETH, .TAU, .CAX, .SCA, .TCA, .CSA, .CTH, .ECT, .UNS, .UCA, .NOC],
      s.holds2007? P = some (s.holds P) := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Silmaril.Logic.Szs

end
