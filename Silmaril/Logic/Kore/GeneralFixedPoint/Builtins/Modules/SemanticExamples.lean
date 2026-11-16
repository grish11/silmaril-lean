module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Canonical


@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Canonical

def equalityDeclaration : {d : Kore.Modules.NamedSymbol // d ∈ scope.symbols} :=
  ⟨equality, by simp [scope]⟩

theorem find_equality : scope.symbols.attach.find?
    (fun d => d.val.declaration.name == "eqInt") = some equalityDeclaration := by
  simp [scope, equalityDeclaration, equality]

private theorem zero_read : decimalInteger "0" = some (0 : Int) := by decide +kernel
private theorem negative_read : decimalInteger "-2" = some (-2 : Int) := by decide +kernel

def zeroGuard : RawPattern := .app "eqInt" [.domainValue "SortInt" "0", .domainValue "SortInt" "0"]

/-- Independent original source evaluation, rather than global validity of a
singleton-valued Boolean sentence. -/
theorem source_zero_guard :
    Semantics.denote scope [] native carriers 8 [] [] "SortBool" zeroGuard = some {true} := by
  simp [zeroGuard, Semantics.denote, find_equality, equalityDeclaration, equality,
    Literal.parse, zero_read, Carriers.literal, carriers, Equiv.refl,
    Kore.Modules.Checking.collect]
  apply congrArg some
  ext x
  simp [native, equality, negation, zero, negative, truth, falsity, literalDeclaration,
    Literal.sort, Operational.Conditional.intEqual]
  constructor
  · rintro ⟨values, ⟨h0, h1⟩, hx⟩
    change values 1 = (0 : Int) at h1
    simpa [h0, h1] using hx
  · intro hx
    subst x
    refine ⟨(Fin.cases (0 : Int) (Fin.cases (0 : Int) (fun i => i.elim0))), ?_, ?_⟩
    · constructor <;> rfl
    · rfl

def negativeZeroGuard : RawPattern :=
  .app "eqInt" [.domainValue "SortInt" "-2", .domainValue "SortInt" "0"]

theorem source_negative_zero_guard :
    Semantics.denote scope [] native carriers 8 [] [] "SortBool" negativeZeroGuard = some {false} := by
  simp [negativeZeroGuard, Semantics.denote, find_equality, equalityDeclaration, equality,
    Literal.parse, zero_read, negative_read, Carriers.literal, carriers, Equiv.refl,
    Kore.Modules.Checking.collect]
  apply congrArg some
  ext x
  simp [native, equality, negation, zero, negative, truth, falsity, literalDeclaration,
    Literal.sort, Operational.Conditional.intEqual]
  constructor
  · rintro ⟨values, ⟨h0, h1⟩, hx⟩
    change values 1 = (0 : Int) at h1
    simpa [h0, h1] using hx
  · intro hx
    subst x
    refine ⟨(Fin.cases (-2 : Int) (Fin.cases (0 : Int) (fun i => i.elim0))), ?_, ?_⟩
    · constructor <;> rfl
    · rfl

def negationDeclaration : {d : Kore.Modules.NamedSymbol // d ∈ scope.symbols} :=
  ⟨negation, by simp [scope]⟩

theorem find_negation : scope.symbols.attach.find?
    (fun d => d.val.declaration.name == "notBool") = some negationDeclaration := by
  simp [scope, negationDeclaration, equality, negation]

theorem source_negative_nonzero_guard :
    Semantics.denote scope [] native carriers 9 [] [] "SortBool"
      (.app "notBool" [negativeZeroGuard]) = some {true} := by
  simp [Semantics.denote, find_negation, negationDeclaration, negation,
    source_negative_zero_guard, Kore.Modules.Checking.collect]
  ext x
  simp [native, equality, negation, zero, negative, truth, falsity, literalDeclaration, Literal.sort]
  constructor
  · rintro ⟨values, h0, hx⟩
    simpa [h0] using hx
  · intro hx
    subst x
    exact ⟨Fin.cases false (fun i => i.elim0), rfl, rfl⟩

theorem source_zero_nonzero_guard :
    Semantics.denote scope [] native carriers 9 [] [] "SortBool"
      (.app "notBool" [zeroGuard]) = some {false} := by
  simp [Semantics.denote, find_negation, negationDeclaration, negation,
    source_zero_guard, Kore.Modules.Checking.collect]
  ext x
  simp [native, equality, negation, zero, negative, truth, falsity, literalDeclaration, Literal.sort]
  constructor
  · rintro ⟨values, h0, hx⟩
    simpa [h0] using hx
  · intro hx
    subst x
    exact ⟨Fin.cases true (fun i => i.elim0), rfl, rfl⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Canonical
