module

public import Silmaril.Logic.Matching.FixedPoint.SortNaturality.Thms

/-! Literal-syntax controls for a noninjective sort map. These controls retain
source indices even when source sorts or their images coincide. -/
@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples
open CategoryTheory

def twoSorted : SortMaps.Signature := ⟨Bool, ⟨fun _ _ _ => Unit⟩⟩
def oneSorted : SortMaps.Signature := ⟨Unit, ⟨fun _ _ _ => Unit⟩⟩
def collapse : twoSorted ⟶ oneSorted := ⟨fun _ => (), fun _ => ()⟩

theorem collapse_not_injective : ¬ Function.Injective collapse.sorts := by
  intro h
  have bad : false = true := h (show collapse.sorts false = collapse.sorts true from rfl)
  cases bad

def coordinates : Fin 2 → Bool := Fin.cases false (Fin.cases true Fin.elim0)
def sameSort : Fin 2 → Bool := fun _ => false
def swap : Ren sameSort sameSort :=
  Fin.cases ⟨1, rfl⟩ (Fin.cases ⟨0, rfl⟩ (fun i => i.elim0))

private def setCoordinate {S : Type} {A : Algebraic.ManySorted.Signature S}
    {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S} :
    Pattern A P Γ s → Option Nat
  | .setvar i => some i.val
  | _ => none

private def objectCoordinate {S : Type} {A : Algebraic.ManySorted.Signature S}
    {k : Nat} {Γ : Fin k → S} {s : S} :
    FirstOrder.Pattern A Γ s → Option Nat
  | .var i => some i.val
  | _ => none

/-- The two differently sorted source recursion indices remain different
literal target variables after their sorts are identified. -/
theorem collapsed_set_coordinates_distinct :
    SortMaps.Hom.fixedPattern collapse
      (.setvar 0 : Pattern twoSorted.symbols coordinates coordinates false) ≠
    SortMaps.Hom.fixedPattern collapse
      (.setvar 1 : Pattern twoSorted.symbols coordinates coordinates true) := by
  intro h
  have bad := congrArg setCoordinate h
  cases bad

/-- The same control for original object-variable coordinates. -/
theorem collapsed_object_coordinates_distinct :
    SortMaps.Hom.pattern collapse
      (.var 0 : FirstOrder.Pattern twoSorted.symbols coordinates false) ≠
    SortMaps.Hom.pattern collapse
      (.var 1 : FirstOrder.Pattern twoSorted.symbols coordinates true) := by
  intro h
  have bad := congrArg objectCoordinate h
  cases bad

/-- Equal source sorts do not identify the original recursion coordinates either. -/
theorem same_sort_set_coordinates_distinct :
    SortMaps.Hom.fixedPattern collapse
      (.setvar 0 : Pattern twoSorted.symbols sameSort sameSort false) ≠
    SortMaps.Hom.fixedPattern collapse
      (.setvar 1 : Pattern twoSorted.symbols sameSort sameSort false) := by
  intro h
  have bad := congrArg setCoordinate h
  cases bad

/-- A nonidentity renaming really moves the selected original coordinate. -/
theorem swap_moves_coordinate :
    (mapRen collapse swap 0).val = (1 : Fin 2) := rfl

theorem same_sort_swap_literal :
    SortMaps.Hom.fixedPattern collapse
      ((.setvar 0 : Pattern twoSorted.symbols sameSort sameSort false).renameSets swap) =
    (SortMaps.Hom.fixedPattern collapse
      (.setvar 0 : Pattern twoSorted.symbols sameSort sameSort false)).renameSets
        (mapRen collapse swap) :=
  fixedPattern_renameSets collapse _ swap

/-- A native fixed point under both object quantifiers. Both the bound set
coordinate and an original recursion coordinate occur in the body. -/
def nested : Pattern twoSorted.symbols coordinates coordinates false :=
  Pattern.mu (P' := Fin.cases false coordinates)
    (.ex true (.all false
      (.conj (.setvar 0) (.disj (.setvar 1) (.base (.var 0))))))

theorem nested_set_shift_literal :
    SortMaps.Hom.fixedPattern collapse (nested.renameSets (Ren.shift coordinates true)) =
      (SortMaps.Hom.fixedPattern collapse nested).renameSets
        (mapRen collapse (Ren.shift coordinates true)) :=
  fixedPattern_renameSets collapse nested _

theorem nested_object_shift_literal :
    SortMaps.Hom.fixedPattern collapse (nested.renameObjects (Ren.shift coordinates true)) =
      (SortMaps.Hom.fixedPattern collapse nested).renameObjects
        (mapRen collapse (Ren.shift coordinates true)) :=
  fixedPattern_renameObjects collapse nested _

def quantified : FirstOrder.Pattern twoSorted.symbols coordinates false :=
  .ex true (.conj (.var 1) (.neg (.var 1)))

theorem quantified_object_shift_literal :
    SortMaps.Hom.pattern collapse (renameFirstOrder quantified (Ren.shift coordinates true)) =
      renameFirstOrder (SortMaps.Hom.pattern collapse quantified)
        (mapRen collapse (Ren.shift coordinates true)) :=
  pattern_renameFirstOrder collapse quantified _

end Silmaril.Logic.Matching.FixedPoint.SortNaturality.Examples
