module

public import Silmaril.Semantics.Region.Tree.CFG.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Tree.Examples

def sparse : SegTree (Fin 3) Unit Nat where
  shape := ⟨0, fun v => match v.val with
    | 0 => none
    | 1 => some 0
    | _ => some 1⟩
  data v := match v.val with
    | 0 => .segment () (some 0)
    | 1 => .segment () none
    | _ => .label 2

def sparseRow : TreeRow (Fin 3) Unit Nat := ⟨0, ∅, sparse⟩

def sparseCFG : SegCFG (Fin 3) Unit Nat := ⟨sparseRow, fun v => {l | v.val = 1 ∧ l = 42}⟩

end Silmaril.Semantics.Region.Tree.Examples
