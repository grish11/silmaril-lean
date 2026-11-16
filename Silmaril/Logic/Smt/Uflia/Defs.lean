module

public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.Logic.Algebraic.ManySorted.Defs

/-!
# Abstract quantifier-free UF and linear integer arithmetic

This is an independent, sorted abstract language, not a claim about the existing
SMT script decoder. The set of uninterpreted sorts is fixed; signature maps
preserve sorts and operation profiles. Bool and Int have their standard carriers,
and uninterpreted carriers are nonempty. Free SMT constants are nullary symbols.
There are no bound variables or quantifiers. Integer multiplication is by an
integer literal only. Boolean-valued function symbols and Boolean arguments are
allowed. Terms reuse the many-sorted algebraic term API.

Parsing, `let` elimination, a variable-sort-map institution and external proof
reconstruction are separate work. No SMT-LIB division or modulo is included.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia

open CategoryTheory
open Silmaril.Inst
open Silmaril.Logic.Algebraic

/-- Built-in sorts and a fixed family of uninterpreted sorts. -/
inductive SortCode (U : Type) where
  | bool
  | int
  | user (name : U)
  deriving DecidableEq

/-- Uninterpreted function symbols, including nullary constants. -/
abbrev Signature (U : Type) := ManySorted.Signature (SortCode U)

/-- Operations of the linear arithmetic and Boolean core, together with UF. -/
inductive Operation {U : Type} (A : Signature U) :
    (n : Nat) → (Fin n → SortCode U) → SortCode U → Type where
  | uf {n inputs output} (symbol : A.operations n inputs output) :
      Operation A n inputs output
  | boolean (value : Bool) : Operation A 0 Fin.elim0 .bool
  | integer (value : Int) : Operation A 0 Fin.elim0 .int
  | add : Operation A 2 (fun _ => .int) .int
  | sub : Operation A 2 (fun _ => .int) .int
  | scale (coefficient : Int) : Operation A 1 (fun _ => .int) .int
  | le : Operation A 2 (fun _ => .int) .bool
  | lt : Operation A 2 (fun _ => .int) .bool
  | eq (sort : SortCode U) : Operation A 2 (fun _ => sort) .bool
  | not : Operation A 1 (fun _ => .bool) .bool
  | and : Operation A 2 (fun _ => .bool) .bool
  | or : Operation A 2 (fun _ => .bool) .bool
  | ite (sort : SortCode U) : Operation A 3 (Fin.cases .bool (fun _ => sort)) sort

/-- Add the fixed interpreted core to the uninterpreted signature. -/
abbrev Signature.expanded {U : Type} (A : Signature U) : ManySorted.Signature (SortCode U) :=
  ⟨Operation A⟩

/-- Ground, sort-correct terms. Constants are supplied by the signature. -/
abbrev Term {U : Type} (A : Signature U) (sort : SortCode U) :=
  ManySorted.Term A.expanded (fun i : Fin 0 => Fin.elim0 i) sort

/-- Assertions are Boolean terms, including Boolean UF applications. -/
abbrev Formula {U : Type} (A : Signature U) := Term A .bool

/-- Standard SMT carriers; uninterpreted sorts are explicitly nonempty. -/
structure Carriers (U : Type) where
  user : U → Type
  nonempty : ∀ u, Nonempty (user u)

/-- Bool and Int are fixed, rather than arbitrary algebraic carriers. -/
abbrev Carriers.value {U : Type} (C : Carriers U) : SortCode U → Type
  | .bool => Bool
  | .int => Int
  | .user u => C.user u

/-- A concrete nonempty carrier family for every sort name. -/
def Carriers.trivial (U : Type) : Carriers U :=
  ⟨fun _ => Unit, fun _ => ⟨()⟩⟩

def Carriers.trivialValue {U : Type} : (s : SortCode U) → (Carriers.trivial U).value s
  | .bool => false
  | .int => 0
  | .user _ => ()

/-- An interpretation of the uninterpreted operations over standard carriers. -/
structure Model {U : Type} (A : Signature U) where
  carriers : Carriers U
  operation : ∀ {n inputs output}, A.operations n inputs output →
    ((i : Fin n) → carriers.value (inputs i)) → carriers.value output

/-- Interpret every UF operation by a constant value of its output sort.
This witnesses that the model class is nonempty for every signature. -/
def Model.trivial {U : Type} (A : Signature U) : Model A :=
  ⟨Carriers.trivial U, fun {_ _ output} _ _ => Carriers.trivialValue output⟩

/-- Boolean literals as ground terms. -/
def Term.boolean {U : Type} {A : Signature U} (b : Bool) : Formula A :=
  .app (.boolean b) (fun i => Fin.elim0 i)

/-- Integer literals as ground terms. -/
def Term.integer {U : Type} {A : Signature U} (i : Int) : Term A .int :=
  .app (.integer i) (fun j => Fin.elim0 j)

/-- Interpret built-ins with their fixed meanings. Equality is classical on
uninterpreted carriers; its use does not postulate an SMT solver result. -/
noncomputable def Model.apply {U : Type} {A : Signature U} (M : Model A) :
    {n : Nat} → {inputs : Fin n → SortCode U} → {output : SortCode U} →
    Operation A n inputs output →
    ((i : Fin n) → M.carriers.value (inputs i)) → M.carriers.value output := by
  classical
  intro n inputs output op args
  cases op with
  | uf symbol => exact M.operation symbol args
  | boolean b => exact b
  | integer i => exact i
  | add => exact args 0 + args 1
  | sub => exact args 0 - args 1
  | scale c => exact c * args 0
  | le => exact decide (args 0 ≤ args 1)
  | lt => exact decide (args 0 < args 1)
  | eq _ => exact decide (args 0 = args 1)
  | not => exact !(args 0)
  | and => exact args 0 && args 1
  | or => exact args 0 || args 1
  | ite _ => exact if (args 0 : Bool) = true then args 1 else args 2

/-- Forget the restriction on models to use the existing sorted evaluation API. -/
noncomputable def Model.algebra {U : Type} {A : Signature U} (M : Model A) :
    ManySorted.Model A.expanded := ⟨M.carriers.value, M.apply⟩

/-- Evaluation uses the existing structurally recursive many-sorted evaluator. -/
noncomputable def Model.eval {U : Type} {A : Signature U} (M : Model A)
    {s : SortCode U} (t : Term A s) : M.carriers.value s :=
  M.algebra.eval (fun i => Fin.elim0 i) t

/-- Satisfaction of an assertion. -/
noncomputable def Model.Holds {U : Type} {A : Signature U} (M : Model A)
    (φ : Formula A) : Prop := M.eval φ = true

/-- A finite problem with a fixed signature. -/
abbrev Problem {U : Type} (A : Signature U) := List (Formula A)

noncomputable def Problem.Holds {U : Type} {A : Signature U} (Γ : Problem A)
    (M : Model A) : Prop := ∀ φ ∈ Γ, M.Holds φ

noncomputable def Problem.Sat {U : Type} {A : Signature U} (Γ : Problem A) : Prop :=
  ∃ M, Γ.Holds M

noncomputable def Problem.Unsat {U : Type} {A : Signature U} (Γ : Problem A) : Prop :=
  ¬ Γ.Sat

end Silmaril.Logic.Smt.Uflia
