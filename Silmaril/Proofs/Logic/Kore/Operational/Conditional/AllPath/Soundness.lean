module

public import Silmaril.Logic.Kore.Operational.Conditional.AllPath.Defs
import Silmaril.Proofs.Logic.Kore.Operational.Conditional.Denotation

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.AllPath
open Silmaril.Proofs.Logic.Kore.Operational.Conditional

theorem guards_disjoint (g h : Guard) (hne : g ≠ h) (x : Int) :
    ¬ (g.Holds x ∧ h.Holds x) := by
  cases g <;> cases h <;> simp_all [Guard.Holds, Guard.eval, intEqual]

theorem syntactic_exclusive (rules : List Rule) (r : Rule)
    (h : SyntacticExclusive rules r) : Exclusive rules r := by
  intro s hs hb x hr hg
  rcases h s hs hb with ha | hne
  · exact ha
  · exact (guards_disjoint s.guard r.guard hne x ⟨hg, hr⟩).elim

/-- Every successor is the exact original captured post, not just a state name. -/
theorem successor_exact (rules : List Rule) (r : Rule) (h : Exclusive rules r)
    (v : Valuation) (coherent : v.x = v.capturedVal) (enabled : r.guard.Holds v.x)
    (d : Config) (step : Step rules (r.beforeConfig v) d) : d = r.afterConfig v := by
  obtain ⟨s, hs, u, hu, hg, he, hd⟩ := (step_iff rules _ _).mp step
  have hcode := congrArg Config.code he
  have hnames : r.before = s.before := (List.cons.inj hcode).1
  have hval : v.x = u.x := congrArg Config.val he
  have hafter : s.after = r.after := h s hs hnames.symm v.x enabled (by simpa only [hval] using hg)
  have htail : v.tail = u.tail := (List.cons.inj hcode).2
  have hcounter : v.counter = u.counter := congrArg Config.counter he
  rw [hd]
  cases v
  cases u
  simp_all [Rule.afterConfig]

/-- Installed progress plus exact successors witnesses position one of every
finite complete path. Infinite paths are outside this partial-correctness mode. -/
theorem allPartial (rules : List Rule) (r : Rule) (hr : r ∈ rules)
    (exclusive : Exclusive rules r) (v : Valuation)
    (coherent : v.x = v.capturedVal) (enabled : r.guard.Holds v.x) :
    Reachability.AllPartial (Step rules) (fun d => d = r.afterConfig v) (r.beforeConfig v) := by
  intro n path start edges terminal
  cases n with
  | zero =>
      exact (terminal (r.afterConfig v) (by simpa only [start] using Step.rule r hr v coherent enabled)).elim
  | succ n =>
      refine ⟨1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
      apply successor_exact rules r exclusive v coherent enabled
      rw [← start]
      exact edges 0 (Nat.zero_lt_succ n)

/-- No installed source head means no operational successor. -/
theorem terminal_of_no_rule (rules : List Rule) (c : Config)
    (none : ∀ r ∈ rules, c.code.head? ≠ some r.before) : ∀ d, ¬ Step rules c d := by
  intro d step
  obtain ⟨r, hr, v, _, _, he, _⟩ := (step_iff rules c d).mp step
  apply none r hr
  rw [he]
  rfl

/-- Exact meaning for every relation on the original configurations. -/
theorem compileAll_satisfies_iff (R : Config → Config → Prop) (r : Rule) :
    (compileAll r).Satisfies KSort.config (model R) ↔
      ∀ v, v.x = v.capturedVal → r.guard.Holds v.x →
        Reachability.AllPartial R (fun c => c = r.afterConfig v) (r.beforeConfig v) := by
  change (∀ v c, c ∈ (model R).denote v r.pre →
    Reachability.AllPartial R (fun d => d ∈ (model R).denote v r.post) c) ↔ _
  simp_rw [pre_mem R, post_denote R, Set.mem_singleton_iff]
  constructor
  · intro h v hc hg
    simpa only [environment_valuation] using
      h (valuation v) (r.beforeConfig v) ⟨hc, hg, by simp⟩
  · intro h v c ⟨hc, hg, he⟩
    subst c
    exact h (environment v) hc hg

theorem compileAll_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules)
    (exclusive : Exclusive rules r) :
    (compileAll r).Satisfies KSort.config (model (Step rules)) :=
  (compileAll_satisfies_iff _ _).2 (allPartial rules r hr exclusive)

theorem compiled_matching_sound (rules : List Rule) (r : Rule) (hr : r ∈ rules)
    (exclusive : Exclusive rules r) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step rules))
      (Reachability.encode KSort.config (compileAll r)) :=
  (Reachability.encode_correct _ _).2 (compileAll_sound rules r hr exclusive)

/-- Actual checked source membership remains necessary alongside exclusivity. -/
theorem declaration_matching_sound {input : String} {p : CheckedProgram}
    (checked : check input = some p) (d : Declaration) (hd : d ∈ p.declarations)
    (hk : d.kind = .ruleAxiom) (Γ : Context) (r : Rule)
    (elaborated : elaborate d = some (Γ, r)) (exclusive : Exclusive p.axioms r) :
    Matching.FixedPoint.Sentence.Satisfies (model (Step p.axioms))
      (Reachability.encode KSort.config (compileAll r)) :=
  compiled_matching_sound _ r
    ((axioms_iff checked r).2 ⟨d, hd, hk, Γ, elaborated,
      (checked_iff checked (Γ, r)).2 ⟨d, hd, elaborated⟩⟩) exclusive

end Silmaril.Logic.Kore.Operational.Conditional.AllPath
