module

public import Silmaril.Formats.Hive.WritePlan.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.Correctness

public section

namespace Silmaril.Formats.Hive.WritePlan

open Silmaril.Relational
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema)

variable {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

/-- The complete result agrees with the independent directory-order and
payload-filter reference, including the original indexed error on failure. -/
theorem plan_eq_reference (physical : Scan.Schema String Kind) (schema : PartitionSchema Kind)
    (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) :
    plan physical schema options encode rows = reference physical schema options encode rows :=
  Proofs.Formats.Hive.WritePlan.plan_eq_reference physical schema options encode rows

/-- A row error identifies exactly the first failure after schema admission.
The preceding rows all classified successfully, and later rows are immaterial. -/
theorem plan_first_row_error_iff (options : PartitionPath.Options) (encode : Encode Value Failure)
    (rows : Scan.Table (schema.extend physical) Value) (index : Nat) (reason : RowError Failure) :
    plan physical schema options encode rows = .error (.row index reason) ↔
    TypedPartitions.checkSchema (Failure := Failure) physical schema = .ok () ∧
      ∃ before row after,
        rows = before ++ row :: after ∧ index = before.length ∧
        (∀ prior ∈ before, ∃ entry, classifyRow options encode prior = .ok entry) ∧
        classifyRow options encode row = .error reason :=
  Proofs.Formats.Hive.WritePlan.plan_first_row_error_iff options encode rows index reason

end Silmaril.Formats.Hive.WritePlan
