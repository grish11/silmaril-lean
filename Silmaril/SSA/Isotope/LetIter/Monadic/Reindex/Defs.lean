module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Substitution.Thms
public import Silmaril.Semantics.ITree.Reindex.Defs

/-! # Reindexing the set interpretation of native LetIter -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Reindex

open Silmaril.Isotope.Semantics

universe u v w

variable {α : Type u} {V W : α → Type v}

/-- Extend base-carrier equivalences through all free type constructors. -/
def typeEquiv (e : ∀ a, V a ≃ W a) : (A : Ty α) → Ty.denote V A ≃ Ty.denote W A
  | .base a => e a
  | .product A B => Equiv.prodCongr (typeEquiv e A) (typeEquiv e B)
  | .coprod A B => Equiv.sumCongr (typeEquiv e A) (typeEquiv e B)
  | .unit => Equiv.refl _
  | .empty => Equiv.refl _

theorem typeEquiv_symm (e : ∀ a, V a ≃ W a) (A : Ty α) :
    (typeEquiv e A).symm = typeEquiv (fun a => (e a).symm) A := by
  induction A with
  | base | unit | empty => rfl
  | product _ _ ihA ihB => exact congrArg₂ Equiv.prodCongr ihA ihB
  | coprod _ _ ihA ihB => exact congrArg₂ Equiv.sumCongr ihA ihB

variable {ν : Type w} [DecidableEq ν]

/-- Transport the value of each visible free variable at its declared type. -/
def freeEnvEquiv (e : ∀ a, V a ≃ W a) (Γ : Ctx ν (Ty α)) :
    FreeEnv (Ty.denote V) Γ ≃ FreeEnv (Ty.denote W) Γ :=
  Equiv.piCongrRight fun _ => Equiv.piCongrRight fun A =>
    Equiv.piCongrRight fun _ => typeEquiv e A

/-- Transport every bound slot at the type determined by its index. -/
def boundEnvEquiv (e : ∀ a, V a ≃ W a) {n : Nat} (β : BoundCtx (Ty α) n) :
    BoundEnv (Ty.denote V) β ≃ BoundEnv (Ty.denote W) β :=
  Equiv.piCongrRight fun i => typeEquiv e (β.get i)

end Silmaril.Isotope.LetIter.Reindex
