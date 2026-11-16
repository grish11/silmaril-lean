module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceThms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

def mapNames (sortMap : String → String) : Names → Names
  | [] => []
  | (name, sort) :: tail => (name, sortMap sort) :: mapNames sortMap tail

@[simp] theorem mapNames_length (sortMap : String → String) (names : Names) :
    (mapNames sortMap names).length = names.length := by
  induction names with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨name, sort⟩
    simp only [mapNames, List.length_cons, ih]

theorem mapNames_eq_map (sortMap : String → String) (names : Names) :
    mapNames sortMap names = names.map (fun p => (p.1, sortMap p.2)) := by
  induction names with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨name, sort⟩
    simp only [mapNames, List.map_cons, ih]

def mapIndex (sortMap : String → String) (names : Names) (i : Fin names.length) :
    Fin (mapNames sortMap names).length := Fin.cast (mapNames_length sortMap names).symm i

/-- Actual finite position transport keeps its value; names/namespaces never
change, so a wrong-sort nearest-name shadow never falls through. -/
theorem lookup_mapNames (sortMap : String → String) (names : Names) (wanted : String) :
    FixedPoint.lookup (mapNames sortMap names) wanted =
      (FixedPoint.lookup names wanted).map (mapIndex sortMap names) := by
  induction names with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨name, sort⟩
    by_cases same : wanted = name
    · simp only [mapNames, FixedPoint.lookup, ite_eq_left same]
      apply congrArg some
      apply Fin.ext
      rfl
    · simp only [mapNames, FixedPoint.lookup, ite_eq_right same]
      rw [ih]
      cases found : FixedPoint.lookup tail wanted with
      | none => rfl
      | some i =>
          apply congrArg some
          apply Fin.ext
          rfl

theorem context_mapNames (sortMap : String → String) (names : Names)
    (i : Fin names.length) :
    context (mapNames sortMap names) (mapIndex sortMap names i) = sortMap (context names i) := by
  induction names with
  | nil => exact i.elim0
  | cons head tail ih =>
    rcases head with ⟨name, sort⟩
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change context (mapNames sortMap tail) (mapIndex sortMap tail i) = sortMap (context tail i)
      exact ih i

/-- Both binder namespaces use exactly the same context extension law. -/
theorem mapNames_cons (sortMap : String → String) (name sort : String) (names : Names) :
    mapNames sortMap ((name, sort) :: names) = (name, sortMap sort) :: mapNames sortMap names := rfl

/-- Generic actual attached first-hit lookup, including the proof-carrying
membership records used by the checker. Declaration order is unchanged. -/
theorem attached_find_map {α β : Type} (f : α → β) (xs : List α)
    (source : α → Bool) (target : β → Bool) (coherent : ∀ a, target (f a) = source a) :
    (xs.map f).attach.find? (fun d => target d.val) =
      (xs.attach.find? (fun d => source d.val)).map
        (fun d => ⟨f d.val, List.mem_map_of_mem d.property⟩) := by
  simp only [List.attach_map, List.find?_map, Function.comp_def, coherent]

/-- Boolean equality on printed names is reflected by name injection. Sort
identification remains unrestricted here. -/
theorem mapped_name_test (names : String → String) (injective : Function.Injective names)
    (actual expected : String) : (names actual == names expected) = (actual == expected) := by
  by_cases same : actual = expected
  · simp [same]
  · have mapped : names actual ≠ names expected := fun h => same (injective h)
    simp [same, mapped]

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
