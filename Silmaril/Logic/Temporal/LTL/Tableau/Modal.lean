module

public import Silmaril.Logic.Temporal.LTL.Tableau.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.LTL.Tableau
open ModalMu Buchi.Automaton

/-- Actual scalar modal μ syntax on the original signature and world type. -/
def formula {S : Signature} (p : NNF.Formula S.Atom) (a : S.Action) : ModalMu.Formula S 0 :=
  (automaton p).formula a

theorem pack_formula_transport {S : Signature} {s t : Shape} (h : s = t)
    (edge : State s → State s → Guard S.Atom) (accept : State s → Occ s → Prop)
    (edge' : State t → State t → Guard S.Atom) (accept' : State t → Occ t → Prop)
    (he : ∀ X Y, edge' (castState h X) (castState h Y) = edge X Y)
    (ha : ∀ X i, accept' (castState h X) (castOcc h i) = accept X i) (a : S.Action) :
    (pack t edge' accept').formula a = (pack s edge accept).formula a := by
  cases h
  have he' : edge' = edge := funext fun X => funext fun Y => he X Y
  have ha' : accept' = accept := funext fun X => funext fun i => ha X i
  cases he'; cases ha'; rfl

/-- Syntactic naturality of the actual scalar output, including atom collapse. -/
theorem formula_map {S T : Signature} (f : S ⟶ T) (p : NNF.Formula S.Atom)
    (a : S.Action) : (formula p a).map f = formula (p.map f.atom) (f.action a) := by
  rw [formula, Generalized.formula_map, formula, automaton, automaton, ← pack_map]
  exact (pack_formula_transport (shape_map f.atom p).symm _ _ _ _
    (transition_map f.atom p) (discharged_map f.atom p) (f.action a)).symm

/-- Exactly one infinite original graph path, with source-world letters. -/
theorem formula_correct {S : Signature} (p : NNF.Formula S.Atom) (a : S.Action)
    (M : ModalMu.Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (formula p a).denote M ρ ↔ ∃ path : Nat → M.World,
      IsPath (M.step a) w path ∧ p.Holds (fun t => modelLabel M (path t)) 0 := by
  rw [formula, Generalized.formula_correct]
  simp only [Generalized.Symbolic.AcceptsPath, accepts_iff, Function.comp_def]

/-- Full LTL syntax compiles for an existential infinite path. This does not
claim an institution comorphism from trace models to arbitrary branching graphs. -/
def ltlFormula {S : Signature} (p : LTL.Formula S.Atom) (a : S.Action) : ModalMu.Formula S 0 :=
  formula (NNF.normalize false p) a

theorem ltlFormula_map {S T : Signature} (f : S ⟶ T) (p : LTL.Formula S.Atom)
    (a : S.Action) : (ltlFormula p a).map f = ltlFormula (p.map f.atom) (f.action a) := by
  simp only [ltlFormula, formula_map, NNF.normalize_map]

theorem ltlFormula_correct {S : Signature} (p : LTL.Formula S.Atom) (a : S.Action)
    (M : ModalMu.Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (ltlFormula p a).denote M ρ ↔ ∃ path : Nat → M.World,
      IsPath (M.step a) w path ∧
        p.Holds (ULift.up (fun t => modelLabel M (path t))) 0 := by
  rw [ltlFormula, formula_correct]
  exact exists_congr fun path => and_congr_right fun _ =>
    NNF.normalize_positive (ULift.up (fun t => modelLabel M (path t))) p 0

end Silmaril.Logic.Temporal.LTL.Tableau
