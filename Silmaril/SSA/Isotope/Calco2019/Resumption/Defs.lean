module

public import Silmaril.SSA.Isotope.Thms
public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs
public import Silmaril.Semantics.Calco2019.ResumptionGuardThms

/-!
# Guarded instruction boundaries for LambdaSSA

One observation follows silent administrative steps to a final answer or
executes one primitive instruction and suspends at its continuation.
A configuration without either boundary has no observation. The encoding
keeps a recursive call under a suspension, so it needs only CALCO's least
guard on first observations.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Calco2019.Resumption

open CategoryTheory Silmaril.Calco2019

/-- A boundary with no result either stops or suspends at the next state.
Naturality renames the suspended state. -/
abbrev Suspensions (M : ParametrizedMonad (Type u)) :=
  ofTypeFunctor Option ⟶ M.parameter (PEmpty : Type u)

variable {M : ParametrizedMonad (Type u)} (B : Suspensions M)

/-- View a boundary at any result type by eliminating its empty return type. -/
def suspend {W Y : Type u} (next : Option W) : (M.obj W).obj Y :=
  (M.obj W).map (↾(PEmpty.elim : PEmpty → Y)) (B.app W next)

/-- A reader for the three heads used by the encoding. -/
structure ReadHeads where
  read {W Y : Type u} : (M.obj W).obj Y → Option (Y ⊕ W)
  read_return {W Y : Type u} (y : Y) : read ((M.obj W).η.app Y y) = some (.inl y)
  read_suspend {W Y : Type u} (next : Option W) :
    read (suspend (Y := Y) B next) = next.map Sum.inr

/-- Finite successful observations of a deterministic resumption. -/
inductive FiniteReturn {S : Type u} {Y : Type v} (read : S → Option (Y ⊕ S)) : S → Y → Prop where
  | done {s y} : read s = some (.inl y) → FiniteReturn read s y
  | next {s t y} : read s = some (.inr t) → FiniteReturn read t y → FiniteReturn read s y

/-- A coalgebra makes the next state a suspension; completion returns purely. -/
def body {S Y : Type u} (step : S → Option (Y ⊕ S)) : S ⟶ (M.obj S).obj Y :=
  ↾fun s => match step s with
    | none => suspend B none
    | some (.inl y) => (M.obj S).η.app Y y
    | some (.inr t) => suspend B (some t)

/-- The first layer of a loop keeps a recursive call under the parameter.
The continuation returns the right summand only when observed. -/
def loopBody {C : Type u} [Category.{v} C] {M : ParametrizedMonad C}
    (P : Coproducts C) (R : FinalResumptions M)
    {S Y : C} (coalgebra : S ⟶ (M.obj S).obj Y) : S ⟶ R.obj (P.sum Y S) :=
  coalgebra ≫ (M.parameter Y).map (P.inr ≫ R.unit (P.sum Y S)) ≫
    (M.obj (R.obj (P.sum Y S))).map P.inl ≫ R.roll (P.sum Y S)

namespace Machine

open Isotope.LambdaSSA.Semantics Isotope.LambdaSSA.Resumption

variable {α : Type u} {Φ : Type v} {σ : Type w}

/-- The next observation includes the external state after the instruction or at return. -/
abbrev Configuration (α : Type u) (Φ : Type v) (σ : Type w) := Control α Φ × σ
abbrev Answer (α : Type u) (σ : Type w) := Result α × σ

/-- Follow administrative steps up to a terminal answer or a successful primitive
transition. The latter is the only rule that exposes a next configuration. -/
inductive Boundary (instr : Φ → Value α → σ → Value α → σ → Prop) :
    Configuration α Φ σ → Answer α σ ⊕ Configuration α Φ σ → Prop where
  | term {x s} : Boundary instr (doneTerm x, s) (.inl (.term x, s))
  | region {l x s} : Boundary instr (doneRegion l x, s) (.inl (.region l x, s))
  | instruction {f a k x s t} : instr f a s x t →
      Boundary instr (.request f a k, s) (.inr (.value x k, t))
  | admin {c d s o} : Admin c d → Boundary instr (d, s) o → Boundary instr (c, s) o

/-- Deterministic in the presence of deterministic instructions. Using a
propositional boundary also handles unbounded silent administrative execution. -/
noncomputable def observe (instr : Φ → Value α → σ → Value α → σ → Prop)
    (s : Configuration α Φ σ) : Option (Answer α σ ⊕ Configuration α Φ σ) :=
  open Classical in
  if h : ∃ o, Boundary instr s o then some h.choose else none

end Machine

end Silmaril.Isotope.Calco2019.Resumption
