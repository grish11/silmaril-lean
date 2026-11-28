module

import Silmaril.Logic.Abstraction

namespace Silmaril.Logic.Abstraction.Regression

open CategoryTheory

private abbrev probeShape : Shape where
  valence := 2
  arity := 3
  scope i := if i = 0 then {1} else if i = 1 then {0, 1} else ∅
  covers := by decide

private abbrev everyShape : Shape where
  valence := 1
  arity := 1
  scope _ := {0}
  covers := by decide

private inductive Symbol : Shape → Type
  | probe : Symbol probeShape
  | every : Symbol everyShape

private def sig : Signature := ⟨Symbol⟩

private abbrev algebra : Algebra sig where
  Carrier := Bool
  nonempty := ⟨false⟩
  op
    | .probe, args =>
      args 0 (fun _ => true) && !(args 0 (fun _ => false)) &&
        args 1 (fun i => i.val == 1) && args 2 Fin.elim0
    | .every, args => args 0 (fun _ => false) && args 0 (fun _ => true)

private noncomputable abbrev model : Model sig where
  algebra := algebra
  truth := {
    Truth := Prop
    lattice := inferInstance
    includeValue := fun p => @decide p (Classical.propDecidable p)
    classify := fun b => b = true
    classify_include := fun p => @decide_eq_true_eq p (Classical.propDecidable p)
  }
  space := ValuationSpace.full algebra

private def ν : Valuation Bool := fun _ _ _ => false

example : probeShape.slot 0 ⟨0, by decide⟩ = 1 :=
  Finset.orderEmbOfFin_singleton (1 : Fin 2) 0

example : (Term.var 0 : Term sig 0).eval algebra (ν.update 0 true) Fin.elim0 = true := by decide
example : (ν.update 0 true) 1 0 (fun _ => true) = false := rfl

-- The first argument binds slot 1, the second binds slots 0 and 1, and the third
-- refers to the surrounding parameter. Both binding arguments read slot 1.
private def probe : Term sig 1 :=
  .app (.probe : Symbol probeShape) (Fin.cases (.bound 1)
    (Fin.cases (.bound 2) (Fin.cases (.bound 0) (fun i => i.elim0))))

example : probe.eval algebra ν (fun _ => true) = true := by decide
example : probe.eval algebra ν (fun _ => false) = false := by decide

private def F : Template sig 1 :=
  .free (n := 1) 0 (fun _ => .bound 0)

private def every (t : Template sig 1) : Term sig 0 :=
  .app (.every : Symbol everyShape) (fun _ => t)

-- The pointwise schematic premise licenses truth of its universal abstraction.
private def introRule : Sentence sig := ⟨[⟨1, F⟩], every F⟩

example : model.Sat introRule := by
  intro v _ b premises hb
  have atFalse := premises ⟨1, F⟩ (by simp [introRule]) (fun _ => false) hb
  have atTrue := premises ⟨1, F⟩ (by simp [introRule]) (fun _ => true) hb
  change v 1 0 (fun _ => false) = true at atFalse
  change v 1 0 (fun _ => true) = true at atTrue
  change (v 1 0 (fun _ => false) && v 1 0 (fun _ => true)) = true
  simp [atFalse, atTrue]

-- Removing the premise changes validity, as F can be constantly false.
example : ¬ model.Sat (Rule.formula (every F)) := by
  intro h
  have bad := h ν (Set.mem_univ _) True (by simp [Rule.formula]) trivial
  change false = true at bad
  contradiction

-- Substitute a template with its own binder for F: its formal parameter must
-- still refer to the outer argument after instantiation under that binder.
private def σ : Substitution sig
  | 1, 0 => some (.app (.every : Symbol everyShape) (fun _ => .bound 0))
  | _, _ => none

example : (F.subst σ).eval algebra ν (fun _ => true) = true := by decide
example : (F.subst σ).eval algebra ν (fun _ => false) = false := by decide

private def renamed : Signature := ⟨fun s => ULift (Symbol s)⟩
private def intoRenamed : sig ⟶ renamed := ⟨fun a => ⟨a⟩⟩

-- Exercise the public corridor on a nonidentity signature map and a rule with a bound premise.
example (M : Model renamed) :
    M.Sat (introRule.map intoRenamed) ↔ (M.reduct intoRenamed).Sat introRule :=
  (institution.map intoRenamed).sat M introRule

end Silmaril.Logic.Abstraction.Regression
