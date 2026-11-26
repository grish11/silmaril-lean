module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Region

/-! # The actual flat linked CFG denotes ordered composition -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A P Q M E D : τ}

/-- A routed producer exit either returns its typed payload immediately or
starts the relocated consumer. Ordered bind carries the state across the cut. -/
theorem denote_linkBy (p : Fragment Φ A P Q) (q : Fragment Φ M E D) (routing : ExitRouting P Q M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (linkBy p q routing).typing env =
      Region.denote (ε := ε) (m := m) p.typing env >>= fun y =>
        Sum.elim pure (fun input => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,input))
          (routing.select y) :=
  Proofs.flat_linkBy_denote p q routing coherent env

/-- The two original exit labels of the producer converge at the consumer
entry. Both dispatchers are interpreted by the repository's region denotation. -/
theorem denote_link (p : Fragment Φ A M M) (q : Fragment Φ M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (link p q).typing env =
      Region.denote (ε := ε) (m := m) p.typing env >>= fun y =>
        Region.denote (ε := ε) (m := m) q.typing (PUnit.unit, merge y) :=
  Proofs.flat_link_denote p q coherent env

omit [LawfulMonad m] [LawfulElgotMonad m] in
private theorem denote_congr {r s : Region Φ} {Γ L : List τ} (h : r = s)
    (dr : Region.HasType Γ r L) (ds : Region.HasType Γ s L) :
    Region.denote (ε := ε) (m := m) dr = Region.denote (ε := ε) (m := m) ds := by
  subst s
  rfl

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem Fragment.loop_denote {B K : τ} (s : Loop Φ A B K E D) :
    Region.denote (ε := ε) (m := m) (Fragment.loop s).typing =
      Region.denote (ε := ε) (m := m) (Theta.regionTyping s) :=
  denote_congr (Fragment.loop_region s) _ _

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem Fragment.guarded_denote {I B K : τ} (s : Conditional.Guarded Φ A I B K E D) :
    Region.denote (ε := ε) (m := m) (Fragment.guarded s).typing =
      Region.denote (ε := ε) (m := m) (Conditional.regionTyping s) :=
  denote_congr (Fragment.guarded_region s) _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
