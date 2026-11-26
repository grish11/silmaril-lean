module

public import Silmaril.Semantics.SQLite.Relational.Value.Defs

public section

namespace Silmaril.SQLite.Relational.Proofs.Value

universe u

theorem toSql_dup {P : Type u} {access : Protection} (object : ValueObject P access) :
    object.dup.value.toSql = object.value.toSql := by
  obtain ⟨value⟩ := object
  cases value with
  | sql data subtype => cases data <;> rfl
  | pointer _ _ => rfl

end Silmaril.SQLite.Relational.Proofs.Value
