module

public import Silmaril.Logic.Egglog.Core.Graph.Functional.Thms
public import Silmaril.Logic.Egglog.Core.Graph.Examples.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Graph.Functional.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- An independently supplied signature with tables of every arity, including zero. -/
def tables : Core.Signature where
  S := Unit
  Op _ _ _ := PEmpty
  Rel _ _ := PEmpty
  Function _ _ _ := Unit

/-- An actual ordinary FOL structure; no Egglog-model constructor is used. -/
def absent : FOL.Structure (Graph.signature tables) where
  carrier _ := Nat
  op o := o.elim
  rel _ _ := False

theorem absent_fd : FD tables absent := by
  intro n w f args x y hx
  exact False.elim hx

def absentIndependent : IndependentModel tables := ⟨absent, absent_fd⟩

theorem absent_reconstruction : model (reconstruct absentIndependent) = absent :=
  graph_reconstruct absentIndependent

/-- A row may be absent even for the nullary table. -/
theorem nullary_absent :
    ¬ (reconstruct absentIndependent).row (n := 0) (w := Fin.elim0) (s := ())
      () (fun i => i.elim0) (0 : Nat) := by
  exact fun h => h

/-- Every output is a row: this independently supplied FOL structure violates FD. -/
def multiple : FOL.Structure (Graph.signature tables) where
  carrier _ := Nat
  op o := o.elim
  rel _ _ := True

theorem nullary_multiple_rejected : ¬ FD tables multiple := by
  intro h
  have impossible : (0 : Nat) = 1 := h (n := 0) (w := fun _ => ())
    () (fun i => i.elim0) (0 : Nat) (1 : Nat) trivial trivial
  exact Nat.zero_ne_one impossible

theorem fd_axioms_reject_multiple :
    ¬ (∀ p ∈ fdTheory tables, p.Holds multiple) :=
  fun h => nullary_multiple_rejected ((fdTheory_holds_iff multiple).mp h)

theorem restriction_not_modelExpansive : ¬ restriction.ModelExpansive := by
  intro h
  obtain ⟨M,he⟩ := h tables multiple
  exact nullary_multiple_rejected (he ▸ M.property)

/-- A directly supplied populated FOL structure: every table has output seven. -/
def seven : FOL.Structure (Graph.signature tables) where
  carrier _ := Nat
  op o := o.elim
  rel r := match r with
    | .predicate p => p.elim
    | .row _ => fun args => args 0 = 7

theorem seven_fd : FD tables seven := by
  intro n w f args x y hx hy
  change x = (7 : Nat) at hx
  change y = (7 : Nat) at hy
  exact hx.trans hy.symm

def sevenIndependent : IndependentModel tables := ⟨seven, seven_fd⟩

theorem seven_unary_lookup :
    (reconstruct sevenIndependent).row (n := 1) (w := fun _ => ()) (s := ())
      () (fun _ => (3 : Nat)) (7 : Nat) := rfl

theorem seven_nullary_lookup :
    (reconstruct sevenIndependent).row (n := 0) (w := Fin.elim0) (s := ())
      () (fun i => i.elim0) (7 : Nat) := rfl

theorem seven_wrong_output :
    ¬ (reconstruct sevenIndependent).row (n := 1) (w := fun _ => ()) (s := ())
      () (fun _ => (3 : Nat)) (8 : Nat) := by
  change ¬ ((8 : Nat) = 7)
  decide

/-- Entirely empty carriers remain legitimate; FD requires no existence witness. -/
def empty : FOL.Structure (Graph.signature tables) where
  carrier _ := Empty
  op o := o.elim
  rel _ _ := False

theorem empty_fd : FD tables empty := by
  intro n w f args x
  exact x.elim

/-- A second independently supplied structure receives a genuinely noninjective hom. -/
def singleton : FOL.Structure (Graph.signature tables) where
  carrier _ := Unit
  op o := o.elim
  rel _ _ := False

theorem singleton_fd : FD tables singleton := by
  intro n w f args x y
  change Unit at x y
  exact fun _ _ => Subsingleton.elim x y

def collapseHom : absentIndependent ⟶ (⟨singleton,singleton_fd⟩ : IndependentModel tables) :=
  ⟨{ map := fun _ _ => ()
     map_op := fun o => o.elim
     map_rel := fun _ _ h => h.elim }⟩

theorem collapseHom_noninjective :
    ¬ Function.Injective (collapseHom.hom.map ()) := by
  intro h
  exact Nat.zero_ne_one (h (show collapseHom.hom.map () (0 : Nat) = collapseHom.hom.map () (1 : Nat) from rfl))

theorem reconstruction_keeps_collapse :
    ((models tables).map collapseHom).map () (0 : Nat) =
      ((models tables).map collapseHom).map () (1 : Nat) := rfl

/-- The original sort-identifying map still induces a reduct on independent models. -/
def collapsed : IndependentModel Graph.Examples.twoSorts :=
  (reduct Graph.Examples.collapseSorts).obj
    ((embed Core.Examples.signature).obj Core.Examples.populatedModel)

theorem collapse_reconstruct :
    reconstruct collapsed =
      (Core.Model.reduct Graph.Examples.collapseSorts).obj
        (reconstruct ((embed Core.Examples.signature).obj Core.Examples.populatedModel)) := rfl

end Silmaril.Logic.Egglog.Core.Graph.Functional.Examples
