module

public import Silmaril.Containers.Precondition.Defs
public import Silmaril.Containers.Runtime.Thms

/-!
# Preconditions: theorems

PROVED (standard axioms); every proof is short and stays inline.

* `pre_weakest`: `Q` is sufficient for `φ` exactly when `Q` implies `pre R φ`, and `pre R φ` is
  itself sufficient: the semantic precondition is the weakest one;
* `pre_mono`, `pre_and`: monotone and conjunctive in the specification;
* `wp_wlp`: a total precondition is a liberal one;
* `vpre_noUB`, `vpre_iff`, `not_vpre_of_undefined`, `not_wlp_of_undefined`: every
  verification precondition requires that no run has undefined behaviour, and one run with
  undefined behaviour refutes it; `not_vpre_of_preservesUB`: the same under any model that
  preserves the undefined behaviour of `R` (`Runtime.restrict`, `mayKill`, `enforce`);
* `pre_antitone`: a model with more runs has a stronger precondition (runtime kills, a weaker
  account of the runtime), and a model with stronger assumptions a weaker one;
* `pre_of_infeasible`: an image with no run satisfies every specification (a miracle):
  feasibility is a separate obligation;
* `pre_refused`: an image the runtime refuses satisfies `φ` exactly when its refusal does; a
  refusal is not undefined behaviour, so a refused image satisfies every `wlp` (and no `wp`);
* `pre_ofShape_none`, `pre_layered`: for shaped flat images, and for layered images read from
  content stores, the precondition reduces to the flat contents and the refusals;
* `SufficientIn.sufficient`, `sufficientIn_of_expressive`: a concrete sufficient precondition
  is sufficient; with expressiveness, the weakest precondition is one.
-/

public section

namespace Silmaril.Containers

variable {I P P' E : Type}

theorem pre_weakest (R : Runtime I P E) (φ : Spec E) (Q : I → Prop) :
    Sufficient R Q φ ↔ ∀ i, Q i → pre R φ i := Iff.rfl

theorem pre_sufficient (R : Runtime I P E) (φ : Spec E) : Sufficient R (pre R φ) φ :=
  fun _ h => h

theorem pre_mono (R : Runtime I P E) {φ ψ : Spec E} (h : ∀ b, φ b → ψ b) {i : I}
    (hi : pre R φ i) : pre R ψ i := Model.Sat.mono hi h

theorem pre_and (R : Runtime I P E) (φ ψ : Spec E) (i : I) :
    pre R (fun b => φ b ∧ ψ b) i ↔ pre R φ i ∧ pre R ψ i :=
  ⟨fun h => ⟨fun b hb => (h b hb).1, fun b hb => (h b hb).2⟩, fun ⟨h₁, h₂⟩ => h₁.and h₂⟩

theorem wp_wlp (R : Runtime I P E) (post : List E → UInt8 → Prop) {i : I} (h : wp R post i) :
    wlp R post i := fun b hb => ⟨(h b hb).1, Spec.totalCorrect_partialCorrect (h b hb).2⟩

theorem vpre_noUB {R : Runtime I P E} {φ : Spec E} {i : I} (h : vpre R φ i) :
    pre R Spec.noUB i := fun b hb => (h b hb).1

theorem vpre_iff (R : Runtime I P E) (φ : Spec E) (i : I) :
    vpre R φ i ↔ pre R Spec.noUB i ∧ pre R φ i := pre_and R _ _ i

/-- A run with undefined behaviour refutes every verification precondition. -/
theorem not_vpre_of_undefined {R : Runtime I P E} {i : I} {t : List E} {u : UB}
    (h : R.beh i (.done t (.undefined u))) (φ : Spec E) : ¬ vpre R φ i :=
  fun hv => (hv _ h).1

theorem not_wlp_of_undefined {R : Runtime I P E} {i : I} {t : List E} {u : UB}
    (h : R.beh i (.done t (.undefined u))) (post : List E → UInt8 → Prop) : ¬ wlp R post i :=
  not_vpre_of_undefined h _

/-- A model that preserves the undefined behaviour of `R` refutes every verification
precondition `R` refutes through a run with undefined behaviour: runtime assumptions, kills and
enforcement cannot certify an image with reachable undefined behaviour. -/
theorem not_vpre_of_preservesUB {P' : Type} {R' : Runtime I P' E} {R : Runtime I P E}
    (h : R'.PreservesUB R) {i : I} {t : List E} {u : UB}
    (hb : R.beh i (.done t (.undefined u))) (φ : Spec E) : ¬ vpre R' φ i :=
  not_vpre_of_undefined (h i _ hb id) φ

theorem pre_antitone {R : Runtime I P E} {R' : Runtime I P' E} (h : R.Le R') {φ : Spec E}
    {i : I} (hi : pre R' φ i) : pre R φ i := Runtime.sat_of_le h hi

theorem pre_of_infeasible (R : Runtime I P E) {i : I} (h : ¬ Feasible R i) (φ : Spec E) :
    pre R φ i := fun b hb => (h ⟨b, hb⟩).elim

theorem pre_refused {R : Runtime I P E} {i : I} {r : Refusal} (hl : R.load i = .error r)
    (φ : Spec E) : pre R φ i ↔ φ (.done [] (.refused r)) := by
  simp only [pre, Model.Sat, Runtime.beh, hl, forall_eq]

theorem pre_ofShape_none {C : Type} {sh : Shape C P} {sem : ProcSem P E}
    {obs : Beh E → Beh E → Prop} {img : Flat C} (h : sh.program img = none) (φ : Spec E) :
    pre (Runtime.ofShape sh sem obs) φ img ↔ φ (.done [] (.refused .noShape)) :=
  pre_refused (by simp [Runtime.ofShape, h]) φ

theorem pre_layered {D C : Type} (S : Stores D C) (R : Runtime (Flat C) P E) (φ : Spec E)
    (m : Layered D) :
    pre (Runtime.layered S R) φ m ↔
      match m.flatten S with
      | some img => pre R φ img
      | none => φ (.done [] (.refused .missingBlob)) := by
  cases h : m.flatten S <;> simp [pre, Model.Sat, Runtime.beh, Runtime.layered, h]

theorem SufficientIn.sufficient {L : Assertions I} {R : Runtime I P E} {φ : Spec E}
    (s : SufficientIn L R φ) : Sufficient R (L.den s.pre) φ := s.sound

theorem sufficientIn_of_expressive {L : Assertions I} {R : Runtime I P E} {Φ : Spec E → Prop}
    (hL : Expressive L R Φ) {φ : Spec E} (hφ : Φ φ) : Nonempty (SufficientIn L R φ) :=
  let ⟨f, hf⟩ := hL φ hφ
  ⟨⟨f, fun i h => (hf i).1 h⟩⟩

end Silmaril.Containers
