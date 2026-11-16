module

public import Silmaril.Logic.Kore.Operational.Conditional.Defs
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Kore.Operational.Conditional
open Silmaril.Logic Silmaril.Logic.Kore.Operational.Conditional

private theorem unary_mem (M : Matching.FirstOrder.Model signature.algebra) {a b : KSort}
    (op : Operation 1 (fun _ => a) b) (p : Pattern a)
    (v : (i : Fin 4) → M.carrier (context i)) (result : M.carrier b) :
    result ∈ M.denote v (unary op p) ↔
      ∃ x, x ∈ M.denote v p ∧ result ∈ M.operation op (fun _ => x) := by
  constructor
  · rintro ⟨xs, hx, hr⟩
    refine ⟨xs 0, hx 0, ?_⟩
    have he : xs = fun _ => xs 0 := by funext i; fin_cases i; rfl
    simpa only [← he] using hr
  · rintro ⟨x, hx, hr⟩
    exact ⟨fun _ => x, fun _ => hx, hr⟩

private theorem binary_mem (M : Matching.FirstOrder.Model signature.algebra) {a b c : KSort}
    (op : Operation 2 (Fin.cases a (fun _ => b)) c) (p : Pattern a) (q : Pattern b)
    (v : (i : Fin 4) → M.carrier (context i)) (result : M.carrier c) :
    result ∈ M.denote v (binary op p q) ↔
      ∃ x, x ∈ M.denote v p ∧ ∃ y, y ∈ M.denote v q ∧
        result ∈ M.operation op (Fin.cases x (fun _ => y)) := by
  constructor
  · rintro ⟨xs, hx, hr⟩
    refine ⟨xs 0, hx 0, xs 1, hx 1, ?_⟩
    have he : xs = Fin.cases (xs 0) (fun _ => xs 1) := by
      funext i; fin_cases i <;> rfl
    simpa only [← he] using hr
  · rintro ⟨x, hx, y, hy, hr⟩
    refine ⟨Fin.cases x (fun _ => y), ?_, hr⟩
    intro i
    fin_cases i
    · exact hx
    · exact hy

private theorem constant_mem (M : Matching.FirstOrder.Model signature.algebra) {s : KSort}
    (op : Operation 0 Fin.elim0 s) (v : (i : Fin 4) → M.carrier (context i))
    (result : M.carrier s) :
    result ∈ M.denote v (constant op) ↔
      result ∈ M.operation op (fun i => i.elim0) := by
  constructor
  · rintro ⟨xs, _, hr⟩
    have he : xs = fun i => i.elim0 := by funext i; exact i.elim0
    simpa only [he] using hr
  · intro hr
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), hr⟩

private theorem state_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) :
    (model R).denote v (statePattern s) = {s :: v 0} := by
  ext c
  change c ∈ (model R).denote v (binary .sequence
    (unary .injection (constant (.token s))) (.var 0)) ↔ c = s :: v 0
  rw [binary_mem (model R) .sequence _ _ v c]
  simp only [unary_mem (model R), constant_mem (model R), Matching.FirstOrder.Model.denote, Set.mem_singleton_iff]
  simp [Fin.cases, Fin.induction, Fin.induction.go]
  rfl

/-- Both hooked Boolean operations really return exactly one Boolean. -/
theorem guard_bool_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) :
    (model R).denote v g.boolPattern = {g.eval (v 1)} := by
  cases g <;> ext b <;>
    simp only [Guard.boolPattern, binary_mem (model R), unary_mem (model R), constant_mem (model R),
      Matching.FirstOrder.Model.denote, Set.mem_singleton_iff] <;>
    simp [Fin.cases, Fin.induction, Fin.induction.go, Guard.eval] <;> rfl

/-- Source Boolean equality compares the two singleton result sets. -/
theorem source_equals_true_iff (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) :
    (model R).denote v g.boolPattern = {true} ↔ g.Holds (v 1) := by
  rw [guard_bool_denote R]
  constructor
  · intro h
    have ht : g.eval (v 1) ∈ ({true} : Set Bool) := h ▸ (Set.mem_singleton _)
    exact ht
  · intro h
    exact congrArg (fun b : Bool => ({b} : Set Bool)) h

/-- Ceil of the intersection is valid here because the source Boolean result
is singleton; no general set equality is identified with nonempty intersection. -/
theorem guard_compile_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (g : Guard) (c : Config) :
    c ∈ (model R).denote v g.compile ↔ g.Holds (v 1) := by
  simp only [Guard.compile, unary_mem (model R), Matching.FirstOrder.Model.denote,
    guard_bool_denote R, constant_mem (model R), Set.mem_inter_iff, Set.mem_singleton_iff]
  simp [Guard.Holds]

/-- The native intersection preserves the actual as-pattern binding. -/
theorem value_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (x : Int) :
    x ∈ (model R).denote v (valuePattern true) ↔ x = v 1 ∧ x = v 2 := by
  simp [valuePattern, Matching.FirstOrder.Model.denote, unary_mem (model R)]

/-- All original constructor fields and the as-pattern coherence are retained. -/
theorem before_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) (c : Config) :
    c ∈ (model R).denote v (configPattern s true) ↔
      v 1 = v 2 ∧ c = ⟨s :: v 0, v 1, v 3⟩ := by
  simp only [configPattern, binary_mem (model R), unary_mem (model R), state_denote R, value_mem R,
    Matching.FirstOrder.Model.denote, Set.mem_singleton_iff]
  simp [Fin.cases, Fin.induction, Fin.induction.go]
  intro _
  rfl

/-- The RHS uses the captured cell, not a freshly reconstructed val variable. -/
theorem after_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (s : String) :
    (model R).denote v (configPattern s false) = {⟨s :: v 0, v 2, v 3⟩} := by
  ext c
  simp only [configPattern, binary_mem (model R), unary_mem (model R), state_denote R, valuePattern,
    Matching.FirstOrder.Model.denote, Set.mem_singleton_iff]
  simp [Fin.cases, Fin.induction, Fin.induction.go]
  rfl

theorem pre_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) (c : Config) :
    c ∈ (model R).denote v r.pre ↔
      v 1 = v 2 ∧ r.guard.Holds (v 1) ∧ c = r.beforeConfig (environment v) := by
  simp only [Rule.pre, Matching.FirstOrder.Model.denote, Set.mem_inter_iff,
    before_mem R, guard_compile_mem R]
  simp only [Rule.beforeConfig, environment]
  tauto

theorem post_denote (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) :
    (model R).denote v r.post = {r.afterConfig (environment v)} :=
  after_denote R v r.after

theorem next_mem (R : Config → Config → Prop)
    (v : (i : Fin 4) → Carrier (context i)) (r : Rule) (c : Config) :
    c ∈ (model R).denote v (unary .step r.post) ↔
      R c (r.afterConfig (environment v)) := by
  simp [unary_mem (model R), post_denote R]

end Silmaril.Proofs.Logic.Kore.Operational.Conditional
