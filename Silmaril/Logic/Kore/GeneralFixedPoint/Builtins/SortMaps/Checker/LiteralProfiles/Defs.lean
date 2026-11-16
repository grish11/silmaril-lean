module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Lookup.Thms
public import Mathlib.Data.List.Find

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

/-- A literal binding has the nullary profile of its actual literal value.
The check does not constrain origins, printed names or declaration order. -/
def literalProfiles (A : Package) : Bool :=
  A.base.literals.all fun b =>
    b.symbol.declaration.arguments.isEmpty &&
      b.symbol.declaration.result == @Literal.sort A.base.bindings b.literal

private theorem declaration_eq_iff (d e : Kore.Modules.SymbolDeclaration) :
    d = e ↔ d.name = e.name ∧ d.arguments = e.arguments ∧ d.result = e.result := by
  cases d
  cases e
  simp only [Kore.Modules.SymbolDeclaration.mk.injEq]

theorem literalProfiles_member {A : Package} (valid : literalProfiles A = true)
    (b : LiteralBinding) (member : b ∈ A.base.literals) :
    b.symbol.declaration.arguments = [] ∧
      b.symbol.declaration.result = @Literal.sort A.base.bindings b.literal := by
  have h := (List.all_eq_true.mp valid) b member
  simpa only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] using h

theorem literal_sort_map {A B : Signature} (f : A ⟶ B) (l : Literal) :
    @Literal.sort B.bindings l = f.native.sorts (@Literal.sort A.bindings l) := by
  cases l with
  | integer => exact f.integer.symm
  | boolean => exact f.boolean.symm

/-- Profile validation survives all structural steps, including maps that
identify ordinary sorts with a builtin sort. -/
theorem Step.literalProfiles_forward {A B : Package} (f : Step A B)
    (valid : literalProfiles A = true) : literalProfiles B = true := by
  apply List.all_eq_true.mpr
  intro b member
  rw [f.literalDeclarations] at member
  rcases List.mem_map.mp member with ⟨a, sourceMember, rfl⟩
  obtain ⟨arguments, result⟩ := literalProfiles_member valid a sourceMember
  simp only [symbol, declaration, arguments, List.map_nil, List.isEmpty_nil, Bool.true_and]
  exact beq_iff_eq.mpr ((congrArg f.semantic.native.sorts result).trans
    (literal_sort_map f.semantic a.literal).symm)

/-- For validated literal bindings, the exact generated-declaration selection
test is unchanged by a structural step. This rules out a formerly mismatched
earlier binding becoming the first match after sorts are identified. -/
theorem Step.literal_test {A B : Package} (f : Step A B)
    (valid : literalProfiles A = true) (mi : Nat) (l : Literal)
    (b : LiteralBinding) (member : b ∈ A.base.literals) :
    (((symbol f.semantic.native.sorts f.names b.symbol).declaration ==
        @literalDeclaration B.base.bindings B.base.literalPrefix mi l) && b.literal == l) =
      ((b.symbol.declaration == @literalDeclaration A.base.bindings A.base.literalPrefix mi l) &&
        b.literal == l) := by
  by_cases value : b.literal = l
  · subst l
    obtain ⟨arguments, result⟩ := literalProfiles_member valid b member
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, eq_self, and_true]
    rw [declaration_eq_iff, declaration_eq_iff]
    simp only [symbol, declaration, literalDeclaration, f.literalPrefix_eq,
      arguments, List.map_nil, f.literalNames b member, result]
    rw [literal_sort_map f.semantic b.literal]
    simp only [eq_self, and_true]

  · simp only [beq_eq_false_iff_ne.mpr value, Bool.and_false]

/-- The actual first literal binding, retaining its origin, is transported.
No target success equation is an input to this statement. -/
theorem Step.literal_find {A B : Package} (f : Step A B)
    (valid : literalProfiles A = true) (mi : Nat) (l : Literal) :
    (B.base.literals.attach.find?
        (fun b => b.val.symbol.declaration ==
          @literalDeclaration B.base.bindings B.base.literalPrefix mi l && b.val.literal == l)).map
        Subtype.val =
      (A.base.literals.attach.find?
        (fun b => b.val.symbol.declaration ==
          @literalDeclaration A.base.bindings A.base.literalPrefix mi l && b.val.literal == l)).map
        (fun b => (⟨symbol f.semantic.native.sorts f.names b.val.symbol, b.val.literal⟩ : LiteralBinding)) := by
  rw [attached_find_val B.base.literals (fun b => b.symbol.declaration ==
    @literalDeclaration B.base.bindings B.base.literalPrefix mi l && b.literal == l)]
  rw [f.literalDeclarations, List.find?_map]
  have tests :
      A.base.literals.find?
        ((fun b : LiteralBinding => b.symbol.declaration ==
            @literalDeclaration B.base.bindings B.base.literalPrefix mi l && b.literal == l) ∘
          (fun b => (⟨symbol f.semantic.native.sorts f.names b.symbol, b.literal⟩ : LiteralBinding))) =
      A.base.literals.find?
        (fun b => b.symbol.declaration ==
          @literalDeclaration A.base.bindings A.base.literalPrefix mi l && b.literal == l) := by
    apply List.find?_congr
    intro b member
    exact f.literal_test valid mi l b member
  rw [tests, ← attached_find_val A.base.literals (fun b => b.symbol.declaration ==
    @literalDeclaration A.base.bindings A.base.literalPrefix mi l && b.literal == l)]
  rw [Option.map_map]
  rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
