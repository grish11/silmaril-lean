module

public import Silmaril.Logic.Egg.Source.Named.Resolution.Thms
public import Silmaril.Logic.Egg.Source.Named.Parser.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Local.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egglog.Source.Named

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem eraseTerm_resolve {D : Declarations} (Γ : CheckedContext D) {s : D.checked.LocalSort}
    (term : EQ.Term D.signature Γ.profile s) :
    resolveTerm? Γ (eraseTerm Γ term) = some ⟨s, term⟩ := by
  refine EQ.Term.rec (motive := fun s term =>
    resolveTerm? Γ (eraseTerm Γ term) = some ⟨s, term⟩) ?_ ?_ term
  · intro i
    have lookup : (List.finRange Γ.bindings.length).find?
        (fun j => (Γ.bindings.get j).name == (Γ.bindings.get i).name) = some i := by
      cases found : (List.finRange Γ.bindings.length).find?
          (fun j => (Γ.bindings.get j).name == (Γ.bindings.get i).name) with
      | none =>
          have missing := (List.find?_eq_none.mp found) i (by simp)
          simp at missing
      | some j =>
          have named := List.find?_some found
          have equal : j = i := binding_name_injective Γ (by simpa using named)
          subst j
          rfl
    simp only [eraseTerm, resolveTerm?, Silmaril.Logic.Egglog.Source.Named.resolveTerm?, lookup, bind, Option.bind, Option.pure_def]
  · intro n w s symbol arguments ih
    have children : (fun i => do
        let packed ← resolveTerm? Γ (eraseTerm Γ (arguments i))
        termAt? (w i) packed) = (fun i => some (arguments i)) := by
      funext i
      simp [ih i, termAt?]
    simp only [bind, Option.bind] at children
    simp only [eraseTerm, resolveTerm?, constructor?_complete, ↓reduceIte, bind, Option.bind]
    rw [children, sequence_complete]
    rfl

theorem eraseEquality_resolve {D : Declarations} (Γ : CheckedContext D)
    (e : Core.Equality D.signature Γ.profile) :
    resolveEquality? Γ (eraseEquality Γ e) = some e := by
  cases e
  simp [eraseEquality, resolveEquality?, eraseTerm_resolve, termAt?]

theorem eraseEqualities_resolve {D : Declarations} (Γ : CheckedContext D)
    (es : List (Core.Equality D.signature Γ.profile)) :
    (es.map (eraseEquality Γ)).mapM (resolveEquality? Γ) = some es := by
  induction es with
  | nil => rfl
  | cons first rest ih => simp [eraseEquality_resolve, ih]

/-- Complete local syntactic representation; all guards and contexts survive. -/
theorem eraseRule_resolve {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ b ∈ Γ.bindings, Silmaril.Logic.Egglog.Source.Named.LegalName b.name)
    (label : String) (guards : List (Core.Equality D.signature Γ.profile))
    (conclusion : Core.Equality D.signature Γ.profile) :
    resolveRule? D ⟨label, Γ.bindings, guards.map (eraseEquality Γ), eraseEquality Γ conclusion⟩ =
      some ⟨Γ.bindings.length, Γ.profile, guards, conclusion⟩ := by
  simp only [resolveRule?, Silmaril.Logic.Egglog.Source.Named.CheckedContext.check_self Γ legal,
    bind, Option.bind, eraseEqualities_resolve, eraseEquality_resolve, Option.pure_def]

end Silmaril.Logic.Egg.Source.Named
