module

public import Silmaril.SSA.RVSDG.LambdaSSA.Defs
public import Silmaril.SSA.RVSDG.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Categorical interface for the λSSA ↔ RVSDG correspondence -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (lift toUnit)
open scoped MonoidalCategory

open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj)

universe u v d h
variable {τ : Type u} {Φ : Type v} [HasTy Φ τ] [TypeFormers τ]
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
  [HasFiniteCoproducts D]

/-- Interpret λSSA opcodes as pure value arrows. The RVSDG singleton product
adds a trailing unit on each side of the primitive. -/
def valueModel (M : TypeModel τ D) (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f)) : Categorical.Model (Opcode (τ := τ) Φ) D where
  selectors := sel
  value := M.obj
  snapshot s := s.elim
  primitive
    | .instr f => (ρ_ _).hom ≫ prim f ≫ (ρ_ _).inv

variable (M : TypeModel τ D) {X : D}

/-- Reassemble a λSSA context from its projections in de Bruijn order.
The newest λSSA variable is the right tensor factor. -/
def gather : (Γ : List τ) → (∀ {A : τ}, Port Γ A → (X ⟶ M.obj A)) → (X ⟶ ctxObj M Γ)
  | [], _ => toUnit X
  | A :: Γ, project => lift (gather Γ (fun p => project (.tail p))) (project (.head (t := A)))

/-- Compare the live RVSDG scope with the λSSA context through the typed
origin assigned to each variable. -/
def Scope.contextMap {root Γ : List τ} {past : List (Ports (Ty τ))}
    (s : Scope root past Γ) (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f)) :
    (valueModel M sel prim).scope (inputs root) past ⟶ ctxObj M Γ :=
  gather M Γ (fun p => Categorical.readOrigin (valueModel M sel prim) (s.origin p))

/-- Insert the empty local store and compare the two conventions for the
ordered input context. -/
def entryMap (Γ : List τ) (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f)) :
    (valueModel M sel prim).ports (inputs Γ) ⟶ ctxObj M Γ :=
  (ρ_ _).inv ≫ (Scope.initial (root := Γ)).contextMap M sel prim

end Silmaril.SSA.RVSDG.LambdaSSA
