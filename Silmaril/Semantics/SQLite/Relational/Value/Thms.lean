module

public import Silmaril.Semantics.SQLite.Relational.Value.Defs
import Silmaril.Proofs.Semantics.SQLite.Relational.Value.Projection

/-! Projection and erasure laws for SQLite values. -/

public section

namespace Silmaril.SQLite.Relational

universe u v

namespace Real

@[simp] theorem ofBits_bits (real : Real) : ofBits real.bits = some real := by
  simp [ofBits, real.notNaN]

theorem bits_injective : Function.Injective Real.bits := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  cases h
  rfl

end Real

namespace Value

variable {P : Type u} {Q : Type v}

@[simp] theorem toSql_ofSql (value : SqlValue) : (ofSql (P := P) value).toSql = value := rfl

theorem ofSql_injective : Function.Injective (ofSql (P := P)) :=
  Function.LeftInverse.injective toSql_ofSql

@[simp] theorem toSql_mapPointer (f : P → Q) (value : Value P) :
    (value.mapPointer f).toSql = value.toSql := by cases value <;> rfl

@[simp] theorem toSql_forgetPointers (value : Value P) :
    value.forgetPointers.toSql = value.toSql := by cases value <;> rfl

@[simp] theorem forgetPointers_mapPointer (f : P → Q) (value : Value P) :
    (value.mapPointer f).forgetPointers = value.forgetPointers := by cases value <;> rfl

@[simp] theorem forgetPointers_empty (value : Value Empty) :
    value.forgetPointers = value := by cases value with
  | sql _ _ => rfl
  | pointer _ payload => exact payload.elim

theorem embedEmpty_injective : Function.Injective (mapPointer (Empty.elim : Empty → P)) :=
  Function.LeftInverse.injective (fun value =>
    (forgetPointers_mapPointer _ value).trans (forgetPointers_empty value))

theorem toSql_not_injective : ¬ Function.Injective (toSql (P := P)) := fun inj => by
  have h : (ofSql .null : Value P) = .sql .null (some 0) := inj rfl
  cases h

theorem forgetPointers_not_injective (tag : PointerTag) (payload : P) :
    ¬ Function.Injective (forgetPointers (P := P)) := fun inj => by
  have h : .pointer tag payload = (ofSql .null : Value P) := inj rfl
  cases h

end Value

namespace ValueObject

@[simp] theorem toSql_dup {P : Type u} {access : Protection} (object : ValueObject P access) :
    object.dup.value.toSql = object.value.toSql := Proofs.Value.toSql_dup object

@[simp] theorem pointer?_matching {P : Type u} (tag : PointerTag) (payload : P) :
    pointer? (⟨.pointer tag payload⟩ : ValueObject P .protectedValue) tag = some payload := by
  simp [pointer?]

@[simp] theorem pointer?_different {P : Type u} {tag expected : PointerTag} (h : tag ≠ expected)
    (payload : P) :
    pointer? (⟨.pointer tag payload⟩ : ValueObject P .protectedValue) expected = none := by
  simp [pointer?, h]

end ValueObject

end Silmaril.SQLite.Relational
