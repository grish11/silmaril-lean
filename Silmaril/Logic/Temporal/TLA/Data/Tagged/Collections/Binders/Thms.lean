module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Binders.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Binders

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

theorem Value.untuple_eq_some {arity : Nat} {value : Value.{u}} {xs : List Value.{u}} :
    value.untuple arity = some xs ↔ xs.length = arity ∧ Value.tuple xs = value :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.Binders.untuple_eq_some

@[simp] theorem Value.untuple_tuple (xs : List Value.{u}) :
    (Value.tuple xs).untuple xs.length = some xs :=
  untuple_eq_some.mpr ⟨rfl, rfl⟩

theorem Value.untuple_eq_none {arity : Nat} {value : Value.{u}} :
    value.untuple arity = none ↔ ¬ ∃ xs, xs.length = arity ∧ Value.tuple xs = value := by
  rw [Option.eq_none_iff_forall_ne_some]
  simp only [ne_eq, untuple_eq_some, not_exists]

/-- A member is exactly one tuple with a component in each corresponding bound. -/
theorem SetData.mem_cartesian {bounds : List SetData.{u}} {key : Value.{u}} :
    (SetData.cartesian bounds).mem key ↔
      ∃ xs, List.Forall₂ (fun x (s : SetData.{u}) => s.mem x) xs bounds ∧ Value.tuple xs = key :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.Binders.mem_cartesian

@[simp] theorem Value.cartesian_sets (bounds : List SetData.{u}) :
    Value.cartesian (bounds.map Value.set) = some (Value.set (SetData.cartesian bounds)) :=
  Proofs.Logic.Temporal.TLA.Data.Tagged.Binders.cartesian_sets bounds

end Silmaril.Logic.Temporal.TLA.Data.Tagged
