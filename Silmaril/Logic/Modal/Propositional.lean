module

public import Silmaril.Logic.Modal.Thms
public import Silmaril.Logic.Institution.Examples.Propositional
public import Mathlib.Tactic.Tauto

@[expose] public section

namespace Silmaril.Logic.Modal
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- The propositional fragment uses classical implication/bottom encodings. -/
def encodePropositional {P : Type} : PL.Formula P → Formula ⟨P⟩
  | .var a => .atom a
  | .bot => .bot
  | .imp p q => .imp (encodePropositional p) (encodePropositional q)
  | .and p q => .imp (.imp (encodePropositional p) (.imp (encodePropositional q) .bot)) .bot
  | .or p q => .imp (.imp (encodePropositional p) .bot) (encodePropositional q)

theorem encodePropositional_holds {P : Type} (M : Model ⟨P⟩) (p : PL.Formula P)
    (w : M.World) : (encodePropositional p).Holds M w ↔ PL.Formula.eval (fun a => M.valuation a w) p := by
  classical
  induction p with
  | var _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr hp hq
  | and p q hp hq =>
    simp only [encodePropositional, Formula.Holds, PL.Formula.eval] at *
    tauto
  | or p q hp hq =>
    simp only [encodePropositional, Formula.Holds, PL.Formula.eval] at *
    tauto

/-- Extract the distinguished world's valuation, functorially on bounded morphisms. -/
def pointValuation (P : Type) : Model ⟨P⟩ ⥤ PL.Model P where
  obj M := ULift.up (fun a => M.valuation a M.point)
  map h := ⟨fun a ha => by
    have ht := (h.atoms a _).mp ha
    rw [h.point] at ht
    exact ht⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Actual satisfaction-preserving propositional-to-modal corridor. -/
def propositionalCorridor (P : Type) : PL.room P ⟶ institution.obj ⟨P⟩ where
  sen := encodePropositional
  mod := pointValuation P
  sat := fun M p => encodePropositional_holds M p M.point

def propositionalSignatures : Type ⥤ Signature where
  obj P := ⟨P⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

theorem encodePropositional_rename {P Q : Type} (f : P → Q) (p : PL.Formula P) :
    encodePropositional (p.rename f) = (encodePropositional p).map f := by
  induction p <;> simp_all [PL.Formula.rename, encodePropositional, Formula.map]

/-- The propositional embedding commutes with all atom renamings. -/
def propositionalNatural : PL.institution ⟶ propositionalSignatures ⋙ institution where
  app := propositionalCorridor
  naturality := by
    intro P Q f
    exact Room.hom_ext (funext (encodePropositional_rename f)) rfl

/-- A shared institution comorphism, usable directly by Hets graph APIs. -/
def propositionalToModal : Inst.CoHom PL.inst ⟨Signature, institution⟩ :=
  ⟨propositionalSignatures, propositionalNatural⟩

end Silmaril.Logic.Modal
