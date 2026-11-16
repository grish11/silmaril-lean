module

public import Silmaril.Logic.Kore.Operational.Conditional.Defs
import Silmaril.Proofs.Logic.Kore.Operational.Conditional.Denotation
import Silmaril.Proofs.Logic.Kore.Operational.Conditional.Checking

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional

open Silmaril.Proofs.Logic.Kore.Operational.Conditional

theorem config_before_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) (c : Config) :
    c ∈ (model R).denote v (configPattern s true) ↔
      v 1 = v 2 ∧ c = ⟨s :: v 0, v 1, v 3⟩ :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.before_mem R v s c

/-- Public precondition meaning, retaining every captured field. -/
theorem rule_pre_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) (c : Config) :
    c ∈ (model R).denote v r.pre ↔
      v 1 = v 2 ∧ r.guard.Holds (v 1) ∧ c = r.beforeConfig (environment v) :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.pre_mem R v r c

/-- Public postcondition meaning in the original captured environment. -/
theorem rule_post_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) :
    (model R).denote v r.post = {r.afterConfig (environment v)} :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.post_denote R v r

/-- The explicit INT.eq/BOOL.not interpretation returns a singleton Boolean. -/
theorem guard_bool_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) :
    (model R).denote v g.boolPattern = {g.eval (v 1)} :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.guard_bool_denote R v g

/-- Native val(X) intersect Gen5 requires both independently captured values. -/
theorem as_pattern_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (x : Int) :
    x ∈ (model R).denote v (valuePattern true) ↔ x = v 1 ∧ x = v 2 :=
  Silmaril.Proofs.Logic.Kore.Operational.Conditional.value_mem R v x

/-- Exact source singleton Boolean equality agrees with the compiled ceil. -/
theorem source_guard_iff_compile (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) (c : Config) :
    (model R).denote v g.boolPattern = {true} ↔ c ∈ (model R).denote v g.compile := by
  rw [source_equals_true_iff, guard_compile_mem]

@[simp] theorem environment_valuation (v : Valuation) : environment (valuation v) = v := by
  cases v
  rfl

/-- Exact inversion of the independent guarded relation, retaining every capture. -/
theorem step_iff (rules : List Rule) (c d : Config) :
    Step rules c d ↔ ∃ r ∈ rules, ∃ v : Valuation,
      v.x = v.capturedVal ∧ r.guard.Holds v.x ∧
      c = r.beforeConfig v ∧ d = r.afterConfig v := by
  constructor
  · intro h
    cases h with
    | rule r hr v hc hg => exact ⟨r, hr, v, hc, hg, rfl, rfl⟩
  · rintro ⟨r, hr, v, hc, hg, rfl, rfl⟩
    exact .rule r hr v hc hg

/-- Exact guarded next meaning, including independent as-pattern coherence. -/
theorem nextSentence_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    r.nextSentence.Satisfies (model R) ↔
      ∀ v, v.x = v.capturedVal → r.guard.Holds v.x →
        R (r.beforeConfig v) (r.afterConfig v) := by
  have hmem (v : (i : Fin 4) → Carrier (context i)) (c : Config) :
      c ∈ (model R).denote v (.neg (.conj r.pre (.neg (unary .step r.post)))) ↔
        (v 1 = v 2 → r.guard.Holds (v 1) →
          c = r.beforeConfig (environment v) → R c (r.afterConfig (environment v))) := by
    simp only [Matching.FirstOrder.Model.denote, Set.mem_compl_iff, Set.mem_inter_iff]
    rw [pre_mem, next_mem]
    tauto
  change (∀ v c, c ∈ (model R).denote v (.neg (.conj r.pre (.neg (unary .step r.post))))) ↔ _
  simp_rw [hmem]
  constructor
  · intro h v hc hg
    simpa only [environment_valuation] using h (valuation v) (r.beforeConfig v) hc hg (by simp)
  · intro h v c hc hg he
    subst c
    exact h (environment v) hc hg

/-- The independent guarded operational relation satisfies every installed rule. -/
theorem next_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    r.nextSentence.Satisfies (model (Step rules)) :=
  (nextSentence_satisfies_iff _ _).2 (fun v hc hg => .rule r hr v hc hg)

/-- Exact finite reachability iff, not only a generated-model soundness result. -/
theorem compile_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    r.compile.Satisfies KSort.config (model R) ↔
      ∀ v, v.x = v.capturedVal → r.guard.Holds v.x →
        Reachability.Reaches R (fun c => c = r.afterConfig v) (r.beforeConfig v) := by
  change (∀ v c, c ∈ (model R).denote v r.pre →
    Reachability.Reaches R (fun d => d ∈ (model R).denote v r.post) c) ↔ _
  simp_rw [pre_mem R, post_denote R, Set.mem_singleton_iff]
  constructor
  · intro h v hc hg
    simpa only [environment_valuation] using
      h (valuation v) (r.beforeConfig v) ⟨hc, hg, by simp⟩
  · intro h v c ⟨hc, hg, he⟩
    subst c
    exact h (environment v) hc hg

theorem compile_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    r.compile.Satisfies KSort.config (model (Step rules)) :=
  (compile_satisfies_iff _ _).2 fun v hc hg =>
    .next trivial (.rule r hr v hc hg) (.now rfl)

/-- Existing reachability-to-native-μ translation applied to guarded rules. -/
theorem compiled_matching_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step rules))
      (Reachability.encode KSort.config r.compile) :=
  (Reachability.encode_correct _ _).2 (compile_sound rules r hr)

/-- A successful complete check recovers the original parsed declarations and
successful elaboration of every declaration, including claims. -/
theorem check_source {input : String} {p : CheckedProgram} (h : check input = some p) :
    ∃ tokens, Text.tokenize input = some tokens ∧
      Text.declarations (tokens.length + 1) tokens = some p.declarations ∧
      p.declarations.mapM elaborate = some p.checked := by
  cases ht : Text.tokenize input with
  | none => simp [check, ht] at h
  | some tokens =>
    cases hd : Text.declarations (tokens.length + 1) tokens with
    | none => simp [check, ht, hd] at h
    | some ds =>
      cases he : ds.mapM elaborate with
      | none => simp [check, ht, hd, he] at h
      | some checked =>
        simp [check, ht, hd, he] at h
        subst p
        exact ⟨tokens, rfl, hd, he⟩

/-- Successful checking aligns every checked pair with a real source declaration. -/
theorem checked_iff {input : String} {p : CheckedProgram}
    (h : check input = some p) (pair : Context × Rule) :
    pair ∈ p.checked ↔ ∃ d ∈ p.declarations, elaborate d = some pair := by
  obtain ⟨_, _, _, he⟩ := check_source h
  exact mapM_members he pair

/-- Every installed axiom comes from an actual declaration; claims contribute none. -/
theorem axioms_iff {input : String} {p : CheckedProgram}
    (_h : check input = some p) (r : Rule) :
    r ∈ p.axioms ↔ ∃ d ∈ p.declarations, d.kind = .ruleAxiom ∧
      ∃ Γ, elaborate d = some (Γ, r) ∧ (Γ, r) ∈ p.checked := by
  simp only [CheckedProgram.axioms, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, he⟩
    split at he
    next hk =>
      cases hel : elaborate d with
      | none => simp [hel] at he
      | some pair =>
        rcases pair with ⟨Γ, r'⟩
        simp only [hel, Option.map_some, Option.some.injEq] at he
        subst r'
        exact ⟨d, hd, hk, Γ, hel, (checked_iff _h (Γ, r)).2 ⟨d, hd, hel⟩⟩
    next => simp at he
  · rintro ⟨d, hd, hk, Γ, he, _⟩
    exact ⟨d, hd, by simp [hk, he]⟩

/-- Matching soundness tied to an actual accepted source axiom. -/
theorem declaration_matching_sound {input : String} {p : CheckedProgram}
    (_h : check input = some p) (d : Declaration) (hd : d ∈ p.declarations)
    (hk : d.kind = .ruleAxiom) (Γ : Context) (r : Rule)
    (hr : elaborate d = some (Γ, r)) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step p.axioms))
      (Reachability.encode KSort.config r.compile) :=
  compiled_matching_sound _ r ((axioms_iff _h r).2 ⟨d, hd, hk, Γ, hr, (checked_iff _h (Γ, r)).2 ⟨d, hd, hr⟩⟩)

end Silmaril.Logic.Kore.Operational.Conditional
