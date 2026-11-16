module

public import Silmaril.Logic.TypeTheory.CIC.Syntax.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.Syntax

@[expose] public section

/-! # Raw CIC binding laws -/

namespace Silmaril.Logic.TypeTheory.CIC.Term

universe u

@[simp] theorem lift_zero {Level : Type u} (cutoff : ℕ) (t : Term Level) :
    t.lift 0 cutoff = t :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SyntaxLaws.lift_zero cutoff t

@[simp] theorem subst_nil {Level : Type u} (cutoff : ℕ) (t : Term Level) :
    t.subst [] cutoff = t :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SyntaxLaws.subst_nil cutoff t

/-- A mutual block binds all of its function names in every body, but not its types. -/
theorem lift_singleton_fix (amount : ℕ) :
    (Term.fix [{ binder := {}, type := .rel 0, body := .rel 0, recursiveArgument := 0 }] 0 : Term ℕ).lift amount 0 =
    .fix [{ binder := {}, type := .rel amount, body := .rel 0, recursiveArgument := 0 }] 0 := by
  simp [Term.lift]

/-- Cofix has the same mutual-name binding convention as fix. -/
theorem lift_singleton_cofix (amount : ℕ) :
    (Term.cofix [{ binder := {}, type := .rel 0, body := .rel 0, recursiveArgument := 0 }] 0 : Term ℕ).lift amount 0 =
    .cofix [{ binder := {}, type := .rel amount, body := .rel 0, recursiveArgument := 0 }] 0 := by
  simp [Term.lift]

/-- Substitution changes a recursive declaration's type while preserving its bound name. -/
theorem subst_singleton_fix (replacement : Term ℕ) :
    (Term.fix [{ binder := {}, type := .rel 0, body := .rel 0, recursiveArgument := 0 }] 0 : Term ℕ).subst [replacement] 0 =
    .fix [{ binder := {}, type := replacement, body := .rel 0, recursiveArgument := 0 }] 0 := by
  simp [Term.subst]

/-- Case metadata stays in declaration scope; local parameters and bodies use local scope. -/
theorem lift_case_scopes (amount : ℕ) :
    (Term.caseOf
      { inductiveRef := ⟨"I", 0⟩, parameterCount := 0, relevance := .relevant }
      { parameters := [.rel 0], universeInstance := [],
        context := [{ binder := {}, type := .rel 0 }], returnType := .rel 1 }
      (.rel 0) [{ context := [{ binder := {}, type := .rel 0 }], body := .rel 0 }] :
        Term ℕ).lift amount 0 =
    .caseOf
      { inductiveRef := ⟨"I", 0⟩, parameterCount := 0, relevance := .relevant }
      { parameters := [.rel amount], universeInstance := [],
        context := [{ binder := {}, type := .rel 0 }], returnType := .rel (1 + amount) }
      (.rel amount) [{ context := [{ binder := {}, type := .rel 0 }], body := .rel 0 }] := by
  simp [Term.lift]

end Silmaril.Logic.TypeTheory.CIC.Term
