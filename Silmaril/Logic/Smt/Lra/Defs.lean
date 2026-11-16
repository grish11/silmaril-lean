module

public import Mathlib.Basic.Real.Basic
public import Silmaril.Logic.Inst.Builders.Core.Defs

/-! A separate intrinsically typed nullary Bool/Real piecewise-affine language.
Coefficients are rational, but term values are actual mathematical reals. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Lra
open CategoryTheory Silmaril.Inst

mutual
inductive Term where
  | literal (value : ℚ)
  | variable (name : String)
  | add (left right : Term)
  | neg (arg : Term)
  | scale (coefficient : ℚ) (arg : Term)
  | ite (guard : Formula) (yes no : Term)
  deriving DecidableEq

inductive Formula where
  | boolean (value : Bool)
  | variable (name : String)
  | equal (left right : Term)
  | le (left right : Term)
  | lt (left right : Term)
  | not (arg : Formula)
  | and (left right : Formula)
  | or (left right : Formula)
  | iff (left right : Formula)
  deriving DecidableEq
end

/-- Fixed global typed-name semantics; declarations constrain source decoding.
The Bool and Real namespaces are distinct abstractly, and source declarations
forbid reusing a name at either sort. -/
structure Model where
  real : String → ℝ
  boolean : String → Bool

/-- One fixed classical conditional on actual reals. Source semantics uses this helper
so proof renderers can share its exact interpretation, independently of local decision instances. -/
noncomputable def chooseReal (guard : Prop) (yes no : ℝ) : ℝ :=
  @ite ℝ guard (Classical.propDecidable guard) yes no

mutual
noncomputable def Term.eval (M : Model) : Term → ℝ
  | .literal q => q
  | .variable n => M.real n
  | .add a b => a.eval M + b.eval M
  | .neg a => -a.eval M
  | .scale q a => (q : ℝ) * a.eval M
  | .ite guard yes no => chooseReal (guard.Holds M) (yes.eval M) (no.eval M)

noncomputable def Formula.Holds (M : Model) : Formula → Prop
  | .boolean b => b = true
  | .variable n => M.boolean n = true
  | .equal a b => a.eval M = b.eval M
  | .le a b => a.eval M ≤ b.eval M
  | .lt a b => a.eval M < b.eval M
  | .not p => ¬ p.Holds M
  | .and p q => p.Holds M ∧ q.Holds M
  | .or p q => p.Holds M ∨ q.Holds M
  | .iff p q => (p.Holds M ↔ q.Holds M)
end

abbrev Problem := List Formula
noncomputable def Problem.Holds (P : Problem) (M : Model) : Prop := ∀ p ∈ P, p.Holds M
noncomputable def Problem.Sat (P : Problem) : Prop := ∃ M, P.Holds M
noncomputable def Problem.Unsat (P : Problem) : Prop := ¬ P.Sat
noncomputable def Problem.Entails (P : Problem) (p : Formula) : Prop :=
  ∀ M, P.Holds M → p.Holds M

/-- One fixed signature of typed global names. No symbol-renaming naturality
or full SMT-LIB source correspondence is claimed by this room. -/
noncomputable def plain : Plain (Disc Unit) where
  Sen _ := Problem
  map _ := id
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Model
  reduct _ := id
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat M P := P.Holds M
  sat_map _ _ _ := Iff.rfl
noncomputable abbrev institution := plain.toInst
noncomputable abbrev room := plain.room ()
end Silmaril.Logic.Smt.Lra
