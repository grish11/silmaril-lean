module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Source

/-! Hook graph transport uses actual source carrier equivalences and all-tuple
hook laws. Source sets are unrestricted; these lemmas do not assume singleton
hook arguments or identify noncanonical source carriers with Int and Bool. -/
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
variable [sorts : SortBindings]
variable {scope : Modules.Scope} {literalPrefix : String}
variable {literals : List LiteralBinding} {hooks : List HookBinding}

/-- The complete relational graph of integer equality transports to the standard
Boolean equality result, including every member of arbitrary argument sets. -/
theorem intEq_graph (M : Model scope literalPrefix literals hooks)
    (binding : HookBinding) (member : binding ∈ hooks) (hook : binding.hook = .intEq)
    (op : scope.signature.operations 2 (fun _ => sorts.intSort) sorts.boolSort)
    (declared : op.val = binding.symbol)
    (p q : Set (M.native.carrier sorts.intSort)) (out : M.native.carrier sorts.boolSort) :
    (∃ x ∈ p, ∃ y ∈ q,
      out ∈ M.native.operation op (Fin.cases x (fun _ => y))) ↔
    ∃ x ∈ p, ∃ y ∈ q,
      M.carriers.boolean out = Operational.Conditional.intEqual
        (M.carriers.integer x) (M.carriers.integer y) := by
  have graph (x y : M.native.carrier sorts.intSort) :=
    M.laws.intEq binding member hook op declared (Fin.cases x (fun _ => y))
  have one : (1 : Fin 2) = Fin.succ 0 := by decide
  simp only [graph, Set.mem_singleton_iff, one, Fin.cases_succ, Fin.cases_zero]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y, hy, by rw [h, Equiv.apply_symm_apply]⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y, hy, by
      apply M.carriers.boolean.injective
      simpa only [Equiv.apply_symm_apply] using h⟩

theorem boolNot_graph (M : Model scope literalPrefix literals hooks)
    (binding : HookBinding) (member : binding ∈ hooks) (hook : binding.hook = .boolNot)
    (op : scope.signature.operations 1 (fun _ => sorts.boolSort) sorts.boolSort)
    (declared : op.val = binding.symbol)
    (p : Set (M.native.carrier sorts.boolSort)) (out : M.native.carrier sorts.boolSort) :
    (∃ x ∈ p, out ∈ M.native.operation op (fun _ => x)) ↔
    ∃ x ∈ p, M.carriers.boolean out = !(M.carriers.boolean x) := by
  have graph (x : M.native.carrier sorts.boolSort) :=
    M.laws.boolNot binding member hook op declared (fun _ => x)
  simp only [graph, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rw [h, Equiv.apply_symm_apply]⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by
      apply M.carriers.boolean.injective
      simpa only [Equiv.apply_symm_apply] using h⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
