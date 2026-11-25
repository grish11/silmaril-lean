module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Centrality.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Distributivity

/-! # The distributive Freyd structure of exact λiter -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open LocallyNameless

variable {S : Sig.{u}}

/-- A computation whose newest variable has a coproduct type can be recovered
by specializing it to the two injections and branching on that variable. -/
theorem splitSum {n : Nat} {β : BoundCtx S.Ty n} {A B D : S.Ty} {t : Tm Empty S.Instr (n + 1)}
    (h : HasType S.Instr Ctx.nil (.snoc β (coprod A B)) t D) :
    Eqv S.pureEff Ctx.nil (.snoc β (coprod A B)) t
      (.case (.bv 0)
        (Tm.bsubst (Fin.cases (.inl (.bv 0)) (fun i => .bv i.succ.succ)) t)
        (Tm.bsubst (Fin.cases (.inr (.bv 0)) (fun i => .bv i.succ.succ)) t)) D :=
  splitSum_proof h

/-- The tensored syntax injections jointly determine any computation arrow. -/
theorem tensorLeft_coprod_hom_ext (R A B : SynCat S) {D : SynCat S}
    {f g : productObj R (cop A B) ⟶ D}
    (left : tensorLeft R (injl A B) ≫ f = tensorLeft R (injl A B) ≫ g)
    (right : tensorLeft R (injr A B) ≫ f = tensorLeft R (injr A B) ≫ g) : f = g :=
  tensorLeft_coprod_hom_ext_proof R A B left right

/-- Computation tensoring distributes over binary coproducts. -/
instance computationDistributive (S : Sig.{u}) : DistributiveTensor (SynCat S) :=
  by exact computationDistributive_proof S

/-- The Cartesian value tensor distributes over binary coproducts. -/
instance valuesDistributive (S : Sig.{u}) : DistributiveTensor (ValueCat S) :=
  by exact valuesDistributive_proof S

/-- The syntactic value inclusion is distributive and preserves finite coproducts. -/
instance valuesDistributiveFreyd (S : Sig.{u}) : DistributiveFreydCategory (values S) where
  preservesFiniteCoproducts := valuesPreservesFiniteCoproducts S

end Silmaril.Thesis.LambdaIter.Syn.SynCat
