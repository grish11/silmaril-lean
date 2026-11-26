module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs
public import Mathlib.Logic.Equiv.Prod

/-! Relabel the cells of a fixed initialized heap and its typed addresses. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.CellRelabel

open RVSDG (Tuple)

abbrev Permutation (cells : Nat) := Equiv.Perm (Address cells)

variable {cells : Nat} {args : List ValueSort}

/-- Move the old cell at a to the cell at its renamed address. -/
def heap (σ : Permutation cells) : Equiv.Perm (Heap cells) where
  toFun old address := old (σ.symm address)
  invFun renamed address := renamed (σ address)
  left_inv _ := funext fun address => congrArg _ (σ.symm_apply_apply address)
  right_inv _ := funext fun address => congrArg _ (σ.apply_symm_apply address)

/-- Addresses are renamed and words keep their values. -/
def value (σ : Permutation cells) : (sort : ValueSort) → Val cells sort → Val cells sort
  | .address => σ
  | .word => id

def input (σ : Permutation cells) (values : Tuple (Val cells) args) : Tuple (Val cells) args :=
  values.map (value σ)

def result (σ : Permutation cells) : Equiv.Perm (Word × Heap cells) :=
  Equiv.prodCongr (Equiv.refl _) (heap σ)

end Silmaril.SSA.SeaOfNodes.Memory.CellRelabel
