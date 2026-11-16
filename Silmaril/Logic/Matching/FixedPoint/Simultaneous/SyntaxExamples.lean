module

public import Silmaril.Logic.Matching.FixedPoint.Simultaneous.Examples

/-! Literal compiler controls using the original source coordinate family.
The map is the actual Bool-to-Unit collapse, not a one-sort source encoding. -/
@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples
open CategoryTheory
open Examples

theorem collapse_not_injective : ¬ Function.Injective collapse.sorts := by
  intro h
  have bad : false = true := h (show collapse.sorts false = collapse.sorts true from rfl)
  cases bad

/-- Both scalar output terms satisfy literal compiler equality, with the
original source index quantified before applying the noninjective sort map. -/
theorem mutual_compile_literal (i : Fin 2) :
    SortMaps.Hom.fixedPattern collapse (mutual.compile i) =
      collapsedMutual.compile i :=
  mutual.compile_map collapse i

theorem unseeded_compile_literal (i : Fin 2) :
    SortMaps.Hom.fixedPattern collapse (unseeded.compile i) =
      (unseeded.map collapse).compile i :=
  unseeded.compile_map collapse i

/-- An equal-sort source block still has two indexed equations and two
external coordinates; each body selects its corresponding external slot. -/
def sameSort : Fin 2 → Bool := fun _ => false

def separateExternal : System signature sameSort sameSort
    (fun i : Fin 0 => i.elim0) where
  body i := (append_right sameSort sameSort i) ▸ Pattern.setvar (Fin.natAdd 2 i)

theorem same_sort_compile_literal (i : Fin 2) :
    SortMaps.Hom.fixedPattern collapse (separateExternal.compile i) =
      (separateExternal.map collapse).compile i :=
  separateExternal.compile_map collapse i

theorem same_sort_source_indices_distinct : (0 : Fin 2) ≠ 1 := by decide

/-- The empty family has no invented scalar output after mapping. -/
theorem empty_compile_literal {l k : Nat} {Q : Fin l → Bool} {Γ : Fin k → Bool}
    (s : System signature (fun i : Fin 0 => i.elim0) Q Γ) (i : Fin 0) :
    SortMaps.Hom.fixedPattern collapse (s.compile i) = (s.map collapse).compile i :=
  i.elim0

end Silmaril.Logic.Matching.FixedPoint.Simultaneous.SyntaxExamples
