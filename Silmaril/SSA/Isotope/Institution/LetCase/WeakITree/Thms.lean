module

public import Silmaril.SSA.Isotope.Institution.LetCase.WeakITree.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.LetCase.WeakITree

public section

namespace Silmaril.Isotope.Institution.LetCase.WeakITree

open CategoryTheory
open Silmaril.Logic.Metatheory.TheoryModel (Algebra)
open Isotope.LetCase.LocallyNameless
open Isotope.Semantics (BoundEnv)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u

variable {κ : Type (u + 1)} [AtomValues κ] {Events : Type u → Type u}
  {P Q : FlatInstitution.Signature.{u, u+1} κ}

local notation "D" => Ty.denote (AtomValues.carrier (κ := κ))
local notation "Γ₀" => (emptyContext (κ := κ))

/-- Presenting the closed-name operand at the institution's universe
preserves the native typed weak tree, in every bound environment. -/
theorem denote_closedOperand (M : Model (κ := κ) Events P.Instr)
    {n : Nat} {β : BoundCtx (Ty κ) n} {t : Tm Empty P.Instr n} {A : Ty κ}
    (d : Derivation P.Instr .nil β t A) (env : BoundEnv D β) :
    Models.denote (algebra (P := P) M) (closedOperand (P := P) d).2 env =
      d.denote D ⟨M.instructions.denote⟩ (fun x => x.elim) env :=
  congrFun (Proofs.SSA.Isotope.Institution.LetCase.WeakITree.denote_closedOperand M d) env

/-- The existing LetCase algebra reduct agrees with the compatible
weak-tree model reduct along effect-preserving opcode relabellings. -/
theorem algebra_reduct (g : P ⟶ Q) (effects : g.toSignatureMap.eff = id)
    (M : Model (κ := κ) Events Q.Instr) :
    Algebra.reductObj (LetCase.sigHom Γ₀ (signatureHom g effects)) (algebra (P := Q) M) =
      algebra (P := P) (FlatInstitution.reduct Events g M) :=
  Proofs.SSA.Isotope.Institution.LetCase.WeakITree.algebra_reduct g effects M

/-- The existing sentence translation and satisfaction law, in these models. -/
theorem satisfaction (g : P ⟶ Q) (effects : g.toSignatureMap.eff = id)
    (M : Model (κ := κ) Events Q.Instr) (e : Equation P) :
    ((LetCase.inst Γ₀).obj (signature Q)).Sat (algebra (P := Q) M)
      (((LetCase.inst Γ₀).map (signatureHom g effects)).sen e) ↔
    ((LetCase.inst Γ₀).obj (signature P)).Sat
      (algebra (P := P) (FlatInstitution.reduct Events g M)) e := by
  rw [← algebra_reduct g effects M]
  exact LetCase.satisfaction Γ₀ (signatureHom g effects) (algebra M) e

end Silmaril.Isotope.Institution.LetCase.WeakITree
