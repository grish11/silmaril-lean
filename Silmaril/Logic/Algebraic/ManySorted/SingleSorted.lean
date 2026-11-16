module

public import Silmaril.Logic.Algebraic.ManySorted.Defs

@[expose] public section
namespace Silmaril.Logic.Algebraic.SingleSorted
open ManySorted

/-- The one-sort specialization is the same institution, without a parallel logic API. -/
abbrev Signature := ManySorted.Signature PUnit
abbrev institution := ManySorted.institution PUnit
abbrev Model (A : Signature) := ManySorted.Model A
abbrev Equation (A : Signature) := ManySorted.Equation A
abbrev Presentation := ManySorted.Presentation PUnit

/-- Ordinary arity-indexed operations inject into the unique sorted profile. -/
def ofArity (operations : Nat → Type) : Signature where
  operations n _ _ := operations n

/-- Every ordinary algebra is a sorted algebra on the one sort. -/
def ofAlgebra {operations : Nat → Type} (carrier : Type)
    (interpret : ∀ {n}, operations n → (Fin n → carrier) → carrier) :
    Model (ofArity operations) where
  carrier _ := carrier
  operation op args := interpret op args

/-- Ordinary operation renamings induce genuine many-sorted signature maps. -/
def ofRenaming {operations operations' : Nat → Type}
    (rename : ∀ {n}, operations n → operations' n) :
    Signature.Hom PUnit (ofArity operations) (ofArity operations') :=
  ⟨fun op => rename op⟩
end Silmaril.Logic.Algebraic.SingleSorted
