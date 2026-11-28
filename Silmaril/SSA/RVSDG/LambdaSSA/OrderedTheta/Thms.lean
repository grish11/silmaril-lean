module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Soundness
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Iteration
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Region

/-! # Preservation of ordered tail-controlled loops -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta

open CategoryTheory
open Silmaril.Elgot Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedRuntime.Structured

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A : τ} {r : Region Φ} {g : Loop Φ A}

section Monad

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

omit [InstructionModel Φ τ ε m] in
/-- Transport Elgot iteration along pure input and output boundary maps. -/
theorem iter_boundary {I O X Y : Type u} (f : I → m (O ⊕ I)) (g : X → m (Y ⊕ X))
    (input : I → X) (output : O → Y)
    (comm : ∀ x, g (input x) = f x >>= fun result => pure (Sum.map output input result))
    (x : I) : iter g (input x) = iter f x >>= fun b => pure (output b) :=
  Proofs.iter_boundary f g input output comm x

/-- Factor a singleton flat CFG through its typed body computation. The
block's local label carries feedback, and its other label is the exit. -/
theorem region_iterates_of_body {b : Region Φ} (typing : Region.HasType [A,A] b [A,A])
    (step : TyDen A → m (TyDen A ⊕ TyDen A))
    (body : RegionDenotes (m := m) ε typing
      (fun env => step env.2 >>= fun result => pure (bodyTarget result))) :
    RegionDenotes (m := m) ε (.cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (fun _ => typing))
      (fun env => iter step env.2 >>= fun a => pure (exit a)) :=
  Proofs.region_iterates_of_body typing step body

/-- Every translation witness gives the structural region denotation in the common Kleisli Elgot model. -/
theorem Related.preserves (rel : Related A r g) :
    RegionDenotes (m := m) ε rel.typing (fun env =>
      (OrderedRuntime.Structured.Theta.denote.{u,u,u}
        (orderedModel (stepMap (m := m) (ε := ε))) g rel.checked).of (pack env.2) >>=
          fun output => pure (exit (unpack output))) :=
  Proofs.preserves rel

/-- The normalized iteration computes a structural ΛSSA region denotation. -/
theorem Related.ssa_denotes (rel : Related A r g) :
    RegionDenotes (m := m) ε rel.typing (fun env =>
      iter (stepMap (m := m) (ε := ε) rel.step) env.2 >>= fun a => pure (exit a)) :=
  Proofs.ssa_denotes rel

end Monad

section State

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- The total-body specialization preserves the partial result and final runtime. -/
theorem Related.preservesState (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step)
    (a : TyDen A) (state : σ) :
    (iter (stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step) a).run state =
      observe <$> OrderedRuntime.Structured.Theta.denoteTotal.{u,u,u}
        (orderedModel f) g rel.checked (point a state) :=
  Proofs.preservesState rel f agrees a state

/-- The ordered loop itself supplies a structural StateT region denotation
at the typed external label. -/
theorem Related.state_denotes (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step) :
    RegionDenotes (m := StateT σ Part.{u}) ε rel.typing (rel.stateDenotation f) :=
  Proofs.state_denotes rel f agrees

/-- A finite ΛSSA result and its observed state agree with the numbered graph return. -/
theorem Related.returns_iff (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step)
    (a b : TyDen A) (initial final : σ) :
    (iter (stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step) a).run initial = Part.some (b, final) ↔
      g.Returns (orderedModel f).toRVSDG (point a initial) (point b final) :=
  Proofs.returns_iff rel f agrees a b initial final

/-- For a total body, an undefined ΛSSA observation corresponds to infinite graph continuation. -/
theorem Related.diverges_iff (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step)
    (a : TyDen A) (initial : σ) :
    (iter (stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step) a).run initial = Part.none ↔
      g.Diverges (orderedModel f).toRVSDG (point a initial) :=
  Proofs.diverges_iff rel f agrees a initial

end State

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta
