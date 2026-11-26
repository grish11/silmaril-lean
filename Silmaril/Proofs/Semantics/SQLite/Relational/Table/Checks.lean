module

public import Silmaril.Semantics.SQLite.Relational.Table.Defs

public section

namespace Silmaril.Proofs.SQLite.Relational

open Silmaril.SQLite.Relational

variable {Value Affinity Expr : Type}
variable {schema : TableSchema Affinity Expr} {model : ValueModel Value Affinity}
variable {sem : TableSemantics Value Affinity Expr}

theorem materialize_eq_some_iff (supplied : schema.SuppliedCells model) (cells : schema.Cells model) :
    schema.materialize model sem supplied = some cells ↔
      ∀ i, schema.fill model sem supplied i = some (cells i) := by
  constructor
  · intro h
    unfold TableSchema.materialize at h
    split at h
    · next success =>
        cases h
        exact fun i => (Option.some_get (success i)).symm
    · contradiction
  · intro h
    have success : ∀ i, (schema.fill model sem supplied i).isSome = true := by
      intro i
      rw [h i]
      rfl
    rw [TableSchema.materialize, dite_eq_left success]
    apply congrArg some
    funext i
    exact Option.some.inj ((Option.some_get (success i)).trans (h i))

theorem generationValid_iff (cells : schema.Cells model) :
    schema.GenerationValid model sem cells ↔
      (schema.generatedColumns model sem).Valid (fun j => some (cells j.val),
        fun j => some (cells j.val.1)) := by
  constructor
  · intro valid j
    have h := valid j.val.1
    unfold TableSchema.fill at h
    split at h
    · next missing => rw [j.property] at missing; contradiction
    · next spec declared =>
        have eq := Option.some.inj (declared.symm.trans j.property)
        subst spec
        exact h.symm
  · intro valid i
    unfold TableSchema.fill
    split
    · rfl
    · next spec declared =>
        exact (valid ⟨(i, spec), declared⟩).symm

theorem materialize_supplied (supplied : schema.SuppliedCells model) (cells : schema.Cells model)
    (materialized : schema.materialize model sem supplied = some cells) :
    (fun j : schema.Supplied => cells j.val) = supplied := by
  funext j
  have h := (materialize_eq_some_iff supplied cells).mp materialized j.val
  unfold TableSchema.fill at h
  split at h
  · exact (Option.some.inj h).symm
  · next spec declared => rw [j.property] at declared; contradiction

end Silmaril.Proofs.SQLite.Relational
