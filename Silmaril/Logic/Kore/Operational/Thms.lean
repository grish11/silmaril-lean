module

public import Silmaril.Logic.Kore.Operational.Defs
import Silmaril.Proofs.Logic.Kore.Operational.Denotation

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational

/-- Structural native configuration patterns denote exactly their source data. -/
theorem compile_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (p : ConfigPattern) :
    (model R).denote v p.compile = {⟨p.state :: v 0, v 1⟩} :=
  Silmaril.Proofs.Logic.Kore.Operational.compile_denote R v p

/-- The native step application denotes exactly the predecessor successor set. -/
theorem next_compile_denote (R : Config → Config → Prop)
    (v : (i : Fin 2) → Carrier (context i)) (p : ConfigPattern) :
    (model R).denote v (.app .step (fun _ => p.compile)) =
      nextDenote R {⟨p.state :: v 0, v 1⟩} :=
  Silmaril.Proofs.Logic.Kore.Operational.next_compile_denote R v p

/-- The accepted constructor tree preserves its state token exactly. -/
theorem elaborate_configTree (Γ : Context) (p : ConfigPattern) :
    elaborateConfig Γ (configTree Γ p) = some p := by
  cases p
  simp [configTree, elaborateConfig]

/-- A claim is never installed as an execution rule, even when its body parses. -/
theorem claim_not_transition (Γ : Context) (a : Alias) (d : Declaration)
    (h : d.kind = .claim) : transitionRule Γ a d = none := by
  simp [transitionRule, h]

/-- Exact successor/rewrite meaning, including the captured valuation. -/
theorem rule_holds_iff (R : Config → Config → Prop) (r : Rule) :
    r.Holds R ↔ ∀ v, R (r.before.eval v) (r.after.eval v) := by
  simp only [Rule.Holds, nextDenote, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    exists_eq_right]

/-- Exact global validity of the source one-path-next rewrite encoding. -/
theorem nextSentence_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    r.nextSentence.Satisfies (model R) ↔ r.Holds R := by
  classical
  have encoded (v : (i : Fin 2) → Carrier (context i)) (c : Config) :
      c ∈ (model R).denote v r.nextPattern ↔
        (c = ⟨r.before.state :: v 0, v 1⟩ → R c ⟨r.after.state :: v 0, v 1⟩) := by
    change (¬ (c ∈ (model R).denote v r.before.compile ∧
      ¬ c ∈ (model R).denote v (.app .step (fun _ => r.after.compile)))) ↔ _
    rw [compile_denote, next_compile_denote]
    change (¬ (c = _ ∧ ¬ ∃ d, R c d ∧ d = _)) ↔ _
    simp only [exists_eq_right, not_and, not_not]
  change (∀ (v : (i : Fin 2) → Carrier (context i)) (c : Config),
    c ∈ (model R).denote v r.nextPattern) ↔ _
  simp_rw [encoded]
  rw [rule_holds_iff]
  constructor
  · intro h v
    exact h (valuation v) (r.before.eval v) rfl
  · intro h v c hc
    subst c
    exact h ⟨v 0, v 1⟩

/-- Generated rules satisfy one-path-next, by construction of the independent
operational relation, rather than a stored satisfaction premise. -/
theorem rule_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    r.Holds (Step rules) :=
  (rule_holds_iff _ _).mpr (fun v => .rule r hr v)

/-- The native designated matching operation is precisely the independent
configuration transition relation, in predecessor orientation. -/
theorem model_step (R : Config → Config → Prop) :
    Reachability.step KSort.config (model R) = R := rfl

/-- Exact finite-reachability sentence semantics for the structural compiler. -/
theorem compile_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    r.compile.Satisfies KSort.config (model R) ↔
      ∀ v, Reachability.Reaches R (fun c => c = r.after.eval v) (r.before.eval v) := by
  change (∀ (v : (i : Fin 2) → Carrier (context i)) (c : Config),
    c ∈ (model R).denote v r.before.compile →
      Reachability.Reaches R (fun x => x ∈ (model R).denote v r.after.compile) c) ↔ _
  simp only [compile_denote]
  change (∀ (v : (i : Fin 2) → Carrier (context i)) (c : Config),
    c = ⟨r.before.state :: v 0, v 1⟩ →
      Reachability.Reaches R (fun x => x = ⟨r.after.state :: v 0, v 1⟩) c) ↔ _
  constructor
  · intro h v
    exact h (valuation v) (r.before.eval v) rfl
  · intro h v c hc
    subst c
    exact h ⟨v 0, v 1⟩

/-- One real generated transition gives actual finite reachability. -/
theorem compile_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    r.compile.Satisfies KSort.config (model (Step rules)) := by
  apply (compile_satisfies_iff _ _).mpr
  intro v
  exact .next trivial (.rule r hr v) (.now rfl)

/-- The operational frontend reaches the existing native μ-matching endpoint. -/
theorem compiled_matching_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step rules))
      (Reachability.encode KSort.config r.compile) :=
  (Reachability.encode_correct _ _).mpr (compile_sound rules r hr)

end Silmaril.Logic.Kore.Operational
