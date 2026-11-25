module

public import Silmaril.Courses.Cambridge.L3.Syntax
public import Mathlib.Data.Fin.Basic

/-! Ordered entry lists for the dependent record fields of the L3 AST. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.RecordLabels

variable {α : Type}

def entries (labels : RecordLabels) (fields : labels.Index → α) : List (Label × α) :=
  List.ofFn (fun i => (labels.label i, fields i))

/-- Check distinct labels before attaching the dependent field indices. -/
def ofEntries (values : List (Label × α)) : Option (Σ labels : RecordLabels, labels.Index → α) :=
  if h : (values.map Prod.fst).Nodup then
    let labels : RecordLabels := ⟨values.map Prod.fst, h⟩
    some ⟨labels, fun i => values[i.val]'(by simpa [labels] using i.isLt) |>.2⟩
  else none

@[simp] theorem entries_labels (labels : RecordLabels) (fields : labels.Index → α) :
    (labels.entries fields).map Prod.fst = labels.names := by
  simp [entries, List.map_ofFn, Function.comp_def, label, List.get_eq_getElem]

@[simp] theorem ofEntries_entries (labels : RecordLabels) (fields : labels.Index → α) :
    ofEntries (labels.entries fields) = some ⟨labels, fields⟩ := by
  have names := entries_labels labels fields
  unfold ofEntries
  simp only [entries_labels, dite_eq_left labels.distinct]
  apply congrArg some
  apply Sigma.ext
  · cases labels with
    | mk names' distinct =>
      change _ = RecordLabels.mk names' distinct
      simpa only [RecordLabels.mk.injEq] using names
  · apply (Fin.heq_fun_iff (congrArg List.length names)).2
    intro i
    simp [entries]

end Silmaril.Courses.Cambridge.L3.RecordLabels
