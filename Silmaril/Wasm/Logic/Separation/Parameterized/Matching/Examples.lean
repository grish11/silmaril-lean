module

public import Silmaril.Logic.Separation.Parameterized.Matching.Defs
public import Silmaril.Wasm.Logic.Separation.Parameterized.Lists.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized.Matching.Examples
open FirstOrder

abbrev Γ : Fin 2 → TargetSort := pointerHeapTargetSorts 1
abbrev σ : Fin 1 → TargetTerm Lists.signature Γ .value := fun _ => .var 1
abbrev heap : TargetTerm Lists.signature Γ .heap := .var 0
abbrev compiledList := compile Lists.list σ heap
abbrev nativeModel := model Lists.Examples.model

def valuation (x : Option Nat) (h : Silmaril.Wasm.Logic.Sep.Heap) :
    Silmaril.Logic.FirstOrderLFP.ObjEnv (FirstOrder.model Lists.Examples.model) Γ :=
  encodeState Lists.Examples.model ((fun _ => x),h)

theorem list_correct (x : Option Nat) (h : Silmaril.Wasm.Logic.Sep.Heap)
    (w : nativeModel.base.carrier (.base .truth)) :
    w ∈ compiledList.denote nativeModel.base (fun i => some (valuation x h i)) (fun i => i.elim0) ↔
      ((fun _ => x),h) ∈ Lists.list.denote Lists.Examples.model (fun i => i.elim0) :=
  compile_correct Lists.Examples.model Lists.list σ heap (valuation x h) w

/-- Actual two-cell native Wasm heap, with 0 pointing to 1 and 1 to null. -/
theorem two_nodes (w : nativeModel.base.carrier (.base .truth)) :
    w ∈ compiledList.denote nativeModel.base
      (fun i => some (valuation (some 0) Lists.Examples.twoNodes i)) (fun i => i.elim0) :=
  (list_correct _ _ w).mpr Lists.Examples.source_two_nodes

theorem null_empty (w : nativeModel.base.carrier (.base .truth)) :
    w ∈ compiledList.denote nativeModel.base
      (fun i => some (valuation none Silmaril.Wasm.Logic.Sep.Heap.empty i)) (fun i => i.elim0) :=
  (list_correct _ _ w).mpr Lists.Examples.source_null_empty

/-- Changing just the pointer on the same empty heap changes native matching
membership, so the parameter is semantically used. -/
theorem nonnull_empty_false (w : nativeModel.base.carrier (.base .truth)) :
    w ∉ compiledList.denote nativeModel.base
      (fun i => some (valuation (some 0) Silmaril.Wasm.Logic.Sep.Heap.empty i)) (fun i => i.elim0) :=
  fun hw => Lists.Examples.source_nonnull_empty_false ((list_correct _ _ w).mp hw)

end Silmaril.Logic.Separation.Parameterized.Matching.Examples
