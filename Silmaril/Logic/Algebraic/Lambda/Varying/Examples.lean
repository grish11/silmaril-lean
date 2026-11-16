module

public import Silmaril.Logic.Algebraic.Lambda.Varying.Institution

/-! Controls for noninjective maps, variable positions, empty unused sorts,
sort permutations, nullary operators and the raw-typing boundary. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda.Varying.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

def split : EQ.Signature := ⟨Bool, fun _ _ _ => Empty⟩
def merged : EQ.Signature := ⟨Unit, fun _ _ _ => Empty⟩
def collapse : split ⟶ merged := ⟨fun _ => (), fun o => nomatch o⟩
def swap : split ⟶ split := ⟨Bool.not, fun o => nomatch o⟩

theorem collapse_not_injective : ¬ Function.Injective collapse.sorts := by
  intro h
  have bad := h (a₁ := false) (a₂ := true) rfl
  cases bad

theorem swap_twice (b : Bool) : (swap ≫ swap).sorts b = b := by
  cases b <;> rfl

def splitContext (i : Fin 3) : Bool := decide (i.val = 1)

/-- The first and third variables have the same source type but different positions. -/
def separated : EQ.Equation split :=
  ⟨3, splitContext, false, .var 0, .var 2⟩

def boolModel : EQ.Algebra merged := ⟨fun _ => Bool, fun o => nomatch o⟩

theorem collapsed_equation_false : ¬ (separated.map collapse).Holds boolModel := by
  intro h
  have bad := h (fun i => decide (i.val = 2))
  change false = true at bad
  cases bad

theorem compiled_collapsed_equation_false :
    ¬ STLCEquations.Holds (expand boolModel) (compile (separated.map collapse)) := by
  intro h
  apply collapsed_equation_false
  have hh := (satisfaction (expand boolModel) (separated.map collapse)).mp h
  simpa only [reduct_expand] using hh

theorem compiled_reflexive_true :
    STLCEquations.Holds (expand boolModel)
      (compile ⟨3, fun _ => (), (), EQ.Term.var 0, EQ.Term.var 0⟩) := by
  intro ρ
  rfl

/-- Every pure equation theory has a singleton model, regardless of its signature. -/
theorem pure_theory_sat (A : EQ.Signature) (H : Set (EQ.Equation A)) :
    ∃ M : EQ.Algebra A, ∀ e ∈ H, e.Holds M := by
  refine ⟨⟨fun _ => PUnit, fun _ _ => ⟨⟩⟩, ?_⟩
  intro e _ ρ
  exact Subsingleton.elim _ _

def extra : EQ.Signature := ⟨Option Unit, fun _ _ _ => Empty⟩
def includeUsed : merged ⟶ extra := ⟨some, fun o => nomatch o⟩

def extraModel : EQ.Algebra extra where
  carrier
    | none => Empty
    | some _ => Bool
  op o := nomatch o

theorem unused_sort_empty : (expand extraModel).base none = Empty := rfl
theorem used_sort_retained :
    (STLCEquations.reduct (signatureMap includeUsed) (expand extraModel)).base () = Bool := rfl

inductive NullaryOp : (n : Nat) → (Fin n → Bool) → Bool → Type where
  | left : NullaryOp 0 Fin.elim0 false
  | right : NullaryOp 0 Fin.elim0 true

def constants : EQ.Signature := ⟨Bool, NullaryOp⟩
def constantsTarget : EQ.Signature := ⟨Unit, fun _ _ _ => PUnit⟩
def collapseConstants : constants ⟶ constantsTarget := ⟨fun _ => (), fun _ => ⟨⟩⟩
def constantsModel : EQ.Algebra constantsTarget := ⟨fun _ => Bool, fun _ _ => false⟩

def constantLeft : EQ.Term constants (fun i : Fin 0 => i.elim0) false :=
  .app .left (fun i => i.elim0)

theorem nullary_evaluates :
    STLC.eval (expand constantsModel) (term (constantLeft.map collapseConstants)) Tuple.nil = false := rfl

local instance : DecidableEq (signature split).Base := inferInstanceAs (DecidableEq Bool)
local instance : DecidableEq (signature merged).Base := inferInstanceAs (DecidableEq Unit)

/-- This raw application uses an argument of the wrong source type. -/
def illTyped : Raw (signature split) := .app (.var 0) (.var 1)
def illTypedContext : Ctx Bool := [.arrow (.base false) (.base false), .base true]

theorem source_inference_fails : Raw.infer illTypedContext illTyped = none := by decide

/-- Identifying the two base types makes the same application well-typed. -/
def collapsedRaw : Raw (signature merged) := .app (.var 0) (.var 1)

theorem collapsed_inference_succeeds :
    Raw.infer (illTypedContext.map (STLC.mapTy collapse.sorts)) collapsedRaw =
      some (.base ()) := by decide

end Silmaril.Logic.Algebraic.Lambda.Varying.Examples
