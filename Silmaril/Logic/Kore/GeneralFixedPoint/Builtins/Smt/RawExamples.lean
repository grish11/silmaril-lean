module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawInstitution
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Noncanonical

/-! Original-source controls use actual raw syntax, checker equations and legal
finite raw object environments. Argument values remain arbitrary sets. -/
set_option linter.concreteInstances false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples
variable [sorts : SortBindings]
variable {scope : Modules.Scope} {literalPrefix : String}
variable {literals : List LiteralBinding} {hooks : List HookBinding}

/-- Original raw matching complement refutes a variable intersected with its
complement, for every legal set binding, including empty/nonsingleton ones. -/
theorem variable_contradiction (M : Model scope literalPrefix literals hooks)
    (objects : Semantics.Values M.native) (s : ValueSort) (name : String)
    (declared : Modules.Checking.namedSort scope s.name = true)
    (legal : (Semantics.lookupValue M.native objects name s.name).isSome = true) :
    Semantics.denote scope [] M.native M.carriers 3 [] objects s.name
      (.conj s.name (.evar name s.name) (.neg s.name (.evar name s.name))) = some ∅ := by
  let p : Pattern s := .conj (.variable s name) (.neg (.variable s name))
  have accepted : check scope hooks 3 s
      (.conj s.name (.evar name s.name) (.neg s.name (.evar name s.name))) = some p := by
    simp [check, declared, p]
  have bound : LegalObjects objects p := by
    intro binding member
    have same : binding = (s, name) := by simpa [p, Pattern.variables] using member
    subst binding
    exact legal
  have meaning := rawAdequacy scope hooks literalPrefix literals M objects 3 s
    (.conj s.name (.evar name s.name) (.neg s.name (.evar name s.name))) p accepted bound
  simpa [p, Examples.contradiction] using meaning

/-- Two occurrences of the same raw variable may choose different integers.
This is a source-interpreter result, rather than equality of SMT constants. -/
theorem repeated_variable_false (M : Model scope literalPrefix literals hooks)
    (objects : Semantics.Values M.native) (fuel : Nat) (hookName name : String)
    (accepted : check scope hooks fuel .boolean
      (.app hookName [.evar name sorts.intSort, .evar name sorts.intSort]) =
        some (.intEq (.variable .integer name) (.variable .integer name)))
    (legal : (Semantics.lookupValue M.native objects name sorts.intSort).isSome = true)
    (x y : M.native.carrier sorts.intSort)
    (hx : x ∈ (Semantics.lookupValue M.native objects name sorts.intSort).getD ∅)
    (hy : y ∈ (Semantics.lookupValue M.native objects name sorts.intSort).getD ∅)
    (different : M.carriers.integer x ≠ M.carriers.integer y) :
    M.carriers.boolean.symm false ∈
      (Semantics.denote scope [] M.native M.carriers fuel [] objects sorts.boolSort
        (.app hookName [.evar name sorts.intSort, .evar name sorts.intSort])).getD ∅ := by
  have bound : LegalObjects objects
      (.intEq (.variable .integer name) (.variable .integer name)) := by
    intro binding member
    have same : binding = (.integer, name) := by
      simpa [Pattern.variables] using member
    subst binding
    exact legal
  have first : M.carriers.integer x ∈ sourceValuation M.carriers objects .integer name := by
    simpa only [sourceValuation, sourceEquiv, ValueSort.name, Set.mem_ofPred_eq,
      Equiv.symm_apply_apply] using hx
  have second : M.carriers.integer y ∈ sourceValuation M.carriers objects .integer name := by
    simpa only [sourceValuation, sourceEquiv, ValueSort.name, Set.mem_ofPred_eq,
      Equiv.symm_apply_apply] using hy
  have typed := Examples.repeated_variable_false (sourceValuation M.carriers objects)
    name (M.carriers.integer x) (M.carriers.integer y) first second different
  have meaning := rawAdequacy scope hooks literalPrefix literals M objects fuel .boolean
    (.app hookName [.evar name sorts.intSort, .evar name sorts.intSort])
    (.intEq (.variable .integer name) (.variable .integer name)) accepted bound
  simp only [ValueSort.name] at meaning
  rw [meaning]
  simpa only [Option.getD_some, Set.mem_ofPred_eq, sourceEquiv,
    Equiv.apply_symm_apply] using typed

/-- Instantiate the original-source refutation on genuinely lifted native
carriers, with every builtin law supplied by the checked model transport. -/
theorem lifted_variable_contradiction (M : Model scope literalPrefix literals hooks)
    (objects : Semantics.Values (Noncanonical.model M).native) (s : ValueSort) (name : String)
    (declared : Modules.Checking.namedSort scope s.name = true)
    (legal : (Semantics.lookupValue (Noncanonical.model M).native objects name s.name).isSome = true) :
    Semantics.denote scope [] (Noncanonical.model M).native (Noncanonical.model M).carriers
      3 [] objects s.name
      (.conj s.name (.evar name s.name) (.neg s.name (.evar name s.name))) = some ∅ :=
  variable_contradiction (Noncanonical.model M) objects s name declared legal

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.RawExamples
