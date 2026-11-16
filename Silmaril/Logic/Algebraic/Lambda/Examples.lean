module

public import Silmaril.Logic.Algebraic.Lambda.Institution

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Two operation names at each first-order profile. -/
abbrev tagged : FixedSignature Unit := ⟨fun _ _ _ => Bool⟩

abbrev arithmetic : EQ.Algebra tagged.equational where
  carrier _ := Nat
  op o args := (List.ofFn args).sum + if o then 1 else 0

def zero : EQ.Term tagged.equational ((fun i => i.elim0) : Fin 0 → Unit) () :=
  .app (n := 0) (w := (fun i => i.elim0)) false (fun i => i.elim0)

def one : EQ.Term tagged.equational ((fun i => i.elim0) : Fin 0 → Unit) () :=
  .app (n := 0) (w := (fun i => i.elim0)) true (fun i => i.elim0)

def two : EQ.Term tagged.equational ((fun i => i.elim0) : Fin 0 → Unit) () :=
  .app (n := 2) (w := fun _ => ()) false (fun _ => one)

theorem actual_lambda_arithmetic :
    STLC.eval (expand arithmetic) (term two) Tuple.nil = (2 : Nat) := rfl

def falseEquation : EQ.Equation tagged.equational :=
  ⟨0, (fun i => i.elim0), (), zero, one⟩

theorem false_equation_rejected :
    ¬ STLC.Sat (expand arithmetic) (equation falseEquation) := by
  rw [satisfies_equation, reduct_expand]
  intro h
  have impossible := h (fun i => i.elim0)
  change (0 : Nat) = 1 at impossible
  exact Nat.zero_ne_one impossible

/-- Full lambda semantics remains available in the expanded first-order model. -/
theorem actual_beta (x : Nat) :
    STLC.eval (expand arithmetic)
      (Term.app (Term.lam (Term.var .zero)) (Term.var .zero) :
        Term (signature tagged.equational) [.base ()] (.base ()))
      (Tuple.cons x Tuple.nil) = x := rfl

/-- Operator names can collapse, despite the fixed base-sort restriction. -/
def collapsed : FixedSignature Unit := ⟨fun _ _ _ => Unit⟩
def collapse : tagged ⟶ collapsed := ⟨fun _ => ()⟩

theorem operator_collapse :
    collapse.operations (n := 0) (w := (fun i => i.elim0)) (s := ()) false =
      collapse.operations (n := 0) (w := (fun i => i.elim0)) (s := ()) true := rfl

def openSum : EQ.Term tagged.equational (fun _ : Fin 2 => ()) () :=
  .app (n := 2) (w := fun _ => ()) false (fun i => .var i)

def openSwap : EQ.Term tagged.equational (fun _ : Fin 2 => ()) () :=
  .app (n := 2) (w := fun _ => ()) false (fun i => .var (Fin.rev i))

theorem open_equation : STLC.Sat (expand arithmetic)
    (.equation (term openSum) (term openSwap)) := by
  change STLC.Sat (expand arithmetic)
    (equation (⟨2, fun _ => (), (), openSum, openSwap⟩ : EQ.Equation tagged.equational))
  rw [satisfies_equation, reduct_expand]
  intro ρ
  change ρ 0 + ρ 1 = ρ 1 + ρ 0
  exact Nat.add_comm _ _

def emptySignature : FixedSignature Bool := ⟨fun _ _ _ => Empty⟩

def emptyAlgebra : EQ.Algebra emptySignature.equational where
  carrier b := if b then Unit else Empty
  op o := o.elim

theorem empty_base_preserved : (expand emptyAlgebra).base false = Empty := rfl

theorem exact_empty_expansion : reduct (expand emptyAlgebra) = emptyAlgebra :=
  reduct_expand emptyAlgebra

/-- An actually empty used variable sort gives the same vacuous equation. -/
abbrev emptyEquation : EQ.Equation emptySignature.equational :=
  ⟨2, fun _ => false, false, .var 0, .var 1⟩

theorem empty_used_context : STLC.Sat (expand emptyAlgebra) (equation emptyEquation) := by
  apply (satisfies_equation _ _).2
  intro ρ
  exact (ρ 0 : Empty).elim

/-- The source model category retains its actual algebra homomorphisms. -/
def emptyEndomorphism : emptyAlgebra ⟶ emptyAlgebra where
  map _ := id
  map_op o := o.elim

abbrev booleanAlgebra : EQ.Algebra emptySignature.equational where
  carrier _ := Bool
  op o := o.elim

/-- The same open equation is false when the used carriers admit distinct values. -/
theorem nonempty_equation_rejected :
    ¬ STLC.Sat (expand booleanAlgebra) (equation emptyEquation) := by
  rw [satisfies_equation, reduct_expand]
  intro h
  have impossible := h (fun i => decide (i = 0))
  change true = false at impossible
  cases impossible

def complementHom : booleanAlgebra ⟶ booleanAlgebra where
  map _ := Bool.not
  map_op o := o.elim

theorem complementHom_not_identity : complementHom ≠ 𝟙 booleanAlgebra := by
  intro h
  have impossible := congrArg (fun f : booleanAlgebra ⟶ booleanAlgebra => f.map true false) h
  change true = false at impossible
  cases impossible

end Silmaril.Logic.Algebraic.Lambda.Examples
