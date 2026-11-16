module

public import Silmaril.Logic.Egg.Core.Defs

@[expose] public section

namespace Silmaril.Logic.Egg.Core

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S T : Signature} {n : Nat} {Γ : Fin n → S.S}

def guardConjunction : List (Equality S Γ) → FOL.Formula (EQtoFOL.sig S) Γ
  | [] => .tt
  | e :: es => .and e.formula (guardConjunction es)

theorem guardConjunction_holds (M : FOL.Structure (EQtoFOL.sig S))
    (ρ : ∀ i, M.carrier (Γ i)) (es : List (Equality S Γ)) :
    (guardConjunction es).Holds M ρ ↔ ∀ e ∈ es, e.Holds M.toAlgebra ρ := by
  induction es with
  | nil =>
    constructor
    · intro _ e he
      cases he
    · intro _
      trivial
  | cons e es ih =>
    constructor
    · intro h g hg
      rcases List.mem_cons.mp hg with rfl | hm
      · exact h.1
      · exact ih.mp h.2 g hm
    · intro h
      exact ⟨h e (.head _), ih.mpr (fun g hg => h g (.tail _ hg))⟩

theorem guardConjunction_map (f : S ⟶ T) (es : List (Equality S Γ)) :
    guardConjunction (es.map (Equality.map f)) =
      (guardConjunction es).map (EQtoFOL.sigFunctor.map f) := by
  induction es with
  | nil => rfl
  | cons e es ih => exact congrArg₂ FOL.Formula.and rfl ih

def Rule.encode (r : Rule S) : FOL.Sentence (EQtoFOL.sig S) :=
  EQtoFOL.closeAll r.context (.not (.and (guardConjunction r.guards) (.not r.conclusion.formula)))

theorem Rule.encode_holds (M : FOL.Structure (EQtoFOL.sig S)) (r : Rule S) :
    r.encode.Holds M ↔ r.Holds M.toAlgebra := by
  rw [Rule.encode, EQtoFOL.holds_closeAll]
  change (∀ ρ, ¬ ((guardConjunction r.guards).Holds M ρ ∧ ¬ r.conclusion.Holds M.toAlgebra ρ)) ↔ _
  simp only [not_and, not_not, guardConjunction_holds, Rule.Holds]
  rfl

theorem Rule.encode_map (f : S ⟶ T) (r : Rule S) :
    (r.map f).encode = r.encode.map (EQtoFOL.sigFunctor.map f) := by
  dsimp only [Rule.encode, Rule.map]
  rw [EQtoFOL.map_closeAll]
  apply congrArg (EQtoFOL.closeAll (Sg := EQtoFOL.sig T) (f.sorts ∘ r.context))
  rw [guardConjunction_map]
  rfl

/-- Conditional equality rules translate exactly to universally closed first-order implications. -/
def toFirstOrder : Inst.CoHom inst FOL.inst where
  Φ := EQtoFOL.sigFunctor
  ρ :=
    { app := fun S => ⟨Rule.encode, EQtoFOL.mod S, Rule.encode_holds⟩
      naturality := by intro S T f; exact Room.hom_ext (funext (Rule.encode_map f)) rfl }

theorem toFirstOrder_modelExpansive : toFirstOrder.ModelExpansive :=
  fun _ M => ⟨EQtoFOL.expansion M, rfl⟩

theorem entails_iff_firstOrder (S : Signature) (H : Set (Rule S)) (r : Rule S) :
    (room S).Entails H r ↔ (FOL.room (EQtoFOL.sig S)).Entails (Rule.encode '' H) r.encode :=
  toFirstOrder.entails_iff toFirstOrder_modelExpansive S H r

end Silmaril.Logic.Egg.Core
