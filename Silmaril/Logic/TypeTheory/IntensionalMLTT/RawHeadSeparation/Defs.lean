module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Syntax

@[expose] public section

/-! Persistent outer constructors, including actual variable and universe indices. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Outer constructors that no root contraction removes. Component terms are not recorded. -/
inductive RigidHead
  | var (index : ℕ)
  | univ (level : ℕ)
  | empty | unit | star | nat | zero | succ | pi | sigma | lam | pair | absurd | id | refl
  deriving DecidableEq

/-- The persistent outer constructor, when the term has one. Eliminators have no rigid head. -/
def Term.rigidHead : {n : ℕ} → Term n → Option RigidHead
  | _, .var i => some (.var i.val)
  | _, .univ i => some (.univ i)
  | _, .empty => some .empty
  | _, .unit => some .unit
  | _, .star => some .star
  | _, .nat => some .nat
  | _, .zero => some .zero
  | _, .succ _ => some .succ
  | _, .pi _ _ => some .pi
  | _, .sigma _ _ => some .sigma
  | _, .lam _ _ => some .lam
  | _, .pair _ _ => some .pair
  | _, .absurd _ _ => some .absurd
  | _, .id _ _ _ => some .id
  | _, .refl _ => some .refl
  | _, .app _ _ | _, .fst _ | _, .snd _ | _, .natrec _ _ _ _ | _, .j _ _ _ _ _ _ => none

end Silmaril.Logic.TypeTheory.IntensionalMLTT
