module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Region

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot
open TwoBlock.TwoExit (Carrier callCase)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A M Y E D : τ}

/-- Disjoint relocation preserves the denotation of each selected arm,
including iteration inside that arm. -/
theorem denote_fork (p : Fragment Φ M E D) (q : Fragment Φ Y E D)
    (gate : TwoBlock.Instruction Φ A (Carrier Y M M))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (fork p q gate).typing env =
      callCase (ε := ε) gate env.2 >>= fun
        | .inl x => Region.denote (ε := ε) (m := m) p.typing
            (PUnit.unit, Sum.elim id id (TypeModel.coprodEquiv M M x))
        | .inr y => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit, y) :=
  Proofs.flat_fork_denote p q gate coherent env

/-- The actual flat case executes only the selected relocated arm. -/
theorem denote_forkCase (p : Fragment Φ M E D) (q : Fragment Φ Y E D)
    (gate : TwoBlock.Instruction Φ A (Silmaril.coprod M Y))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (forkCase p q gate).typing env =
      callCase (ε := ε) gate env.2 >>= fun
        | .inl x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x)
        | .inr y => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,y) :=
  Proofs.flat_forkCase_denote p q gate coherent env

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
