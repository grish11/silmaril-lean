module

public import Silmaril.Containers.Behaviour.Defs

/-!
# Proofs: behaviours, refinement and noninterference

Proofs for `Silmaril.Containers.Behaviour.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Behaviour

open Silmaril.Containers

theorem traces_singleton_nil_iff {E : Type} (b : Beh E) (hb : ∀ t, b.Prefix t ↔ t = [])
    (t : List E) : Model.Traces (· = b) t ↔ t = [] :=
  ⟨fun ⟨_, h, ht⟩ => (hb t).1 (by cases h; exact ht), fun h => ⟨b, rfl, (hb t).2 h⟩⟩

theorem prefix_nil_iff {E : Type} (t : List E) : t <+: [] ↔ t = [] :=
  ⟨List.eq_nil_of_prefix_nil, fun h => h ▸ List.prefix_refl _⟩

theorem traceRefines_not_total :
    let M : Model Unit := (· = .spins [])
    let N : Model Unit := (· = .done [] (.exited 0))
    M.TraceRefines N ∧ N.Sat (Spec.totalCorrect fun _ _ => True) ∧
      ¬ M.Sat (Spec.totalCorrect fun _ _ => True) := by
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have h₁ := (traces_singleton_nil_iff (.spins []) (fun t => prefix_nil_iff t) t).1 ht
    exact (traces_singleton_nil_iff (.done [] (.exited 0)) (fun t => prefix_nil_iff t) t).2 h₁
  · rintro b rfl; trivial
  · intro h; exact h _ rfl

/-- The two runs of the counterexamples: one event, `true` or `false`, then exit. -/
def leak (x : Bool) : Beh Bool := .done [x] (.exited 0)

theorem noninterference_singleton {α β : Type} (lowIn : List Bool → α) (lowOut : List Bool → β)
    (x : Bool) : Model.Noninterference lowIn lowOut (· = leak x) := by
  intro t t' s s' h h' _
  cases h; cases h'; rfl

theorem not_noninterference_pair :
    ¬ Model.Noninterference (fun _ : List Bool => ()) id (fun b => b = leak true ∨ b = leak false) :=
  fun h => Bool.noConfusion (List.head_eq_of_cons_eq
    (h [true] [false] (.exited 0) (.exited 0) (.inl rfl) (.inr rfl) rfl))

theorem trace_property_not_noninterference (φ : Spec Bool) (h₁ : φ (leak true))
    (h₂ : φ (leak false)) :
    ¬ ∀ M : Model Bool, M.Sat φ → Model.Noninterference (fun _ => ()) id M := by
  intro h
  apply not_noninterference_pair
  apply h
  rintro b (rfl | rfl) <;> assumption

theorem noninterference_not_trace_property :
    ¬ ∃ φ : Spec Bool, ∀ M : Model Bool,
      Model.Noninterference (fun _ => ()) id M ↔ M.Sat φ := by
  rintro ⟨φ, hφ⟩
  have h₁ : φ (leak true) := (hφ _).1 (noninterference_singleton _ _ true) _ rfl
  have h₂ : φ (leak false) := (hφ _).1 (noninterference_singleton _ _ false) _ rfl
  exact trace_property_not_noninterference φ h₁ h₂ fun M hM => (hφ M).2 hM

end Silmaril.Proofs.Containers.Behaviour
