module

public import Silmaril.SSA.Isotope.Calco2019.Resumption.Defs
public import Silmaril.SSA.Isotope.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.Calco2019.Resumption.Coalgebra
import Silmaril.Proofs.SSA.Isotope.Calco2019.Resumption.Machine

/-! # CALCO guarded resumptions and LambdaSSA finite returns -/

public section

universe u v w

namespace Silmaril.Isotope.Calco2019.Resumption

open CategoryTheory Silmaril.Calco2019

section Coalgebra

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P)
  (R : FinalResumptions M.toParametrizedMonad)
  {S Y : C} (coalgebra : S ⟶ (M.toParametrizedMonad.obj S).obj Y)

/-- A delayed coalgebra is guarded by the trivial guard axiom at the first
observation. The next control is placed under the parameter of the monad. -/
theorem loopBody_guarded :
    M.ResumptionGuard R (Y := Y) (Z := S) (loopBody P R coalgebra) :=
  Proofs.loopBody_guarded M R coalgebra

/-- CALCO's actual guarded iteration of the delayed coalgebra is its
final-coalgebra unfolding. This uses the chosen guarded iteration and finality. -/
theorem iterate_eq_unfold
    (guard : M.ResumptionGuard R (Y := Y) (Z := S) (loopBody P R coalgebra)) :
    M.iterateResumption R (loopBody P R coalgebra) guard = R.unfold coalgebra :=
  Proofs.iterate_eq_unfold M R coalgebra guard

end Coalgebra

/-- Finite returned observations of the final coalgebra agree exactly with the
finite returned observations of the encoded transition function. -/
theorem finite_return_unfold {M : ParametrizedMonad (Type u)} (B : Suspensions M)
    (D : ReadHeads B) (R : FinalResumptions M)
    {S Y : Type u} (step : S → Option (Y ⊕ S)) (s : S) (y : Y) :
    FiniteReturn (fun r => D.read (R.out Y r)) (R.unfold (body B step) s) y ↔
      FiniteReturn step s y :=
  Proofs.finite_return_unfold B D R step s y

namespace Machine

open Isotope.LambdaSSA.Semantics Isotope.LambdaSSA.Resumption

section FiniteRuns

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- Every selected next configuration comes from a successful primitive
transition preceded by a finite administrative prefix. -/
theorem observe_eq_iff (det : InstrDeterministic instr)
    {s : Configuration α Φ σ} {o : Answer α σ ⊕ Configuration α Φ σ} :
    observe instr s = some o ↔ Boundary instr s o :=
  Proofs.observe_eq_iff det

theorem finite_return_iff_run (det : InstrDeterministic instr) {c : Control α Φ}
    {s t : σ} {r : Result α} :
    FiniteReturn (observe instr) (c, s) (r, t) ↔ Run instr c s r.control t :=
  Proofs.finite_return_iff_run det

end FiniteRuns

variable (M : ParametrizedGuardedElgotMonad (typeCoproducts : Coproducts (Type u)))
  (R : FinalResumptions M.toParametrizedMonad) (B : Suspensions M.toParametrizedMonad)
  {α Φ σ : Type u} (instr : Φ → Value α → σ → Value α → σ → Prop)

/-- Interpret a LambdaSSA machine in the guarded resumption monad. Each
successful primitive instruction exposes the next configuration as a suspension. -/
@[expose] noncomputable def denote : Configuration α Φ σ ⟶ R.obj (Answer α σ) :=
  M.iterateResumption R (loopBody typeCoproducts R (body B (observe instr)))
    (loopBody_guarded M R (body B (observe instr)))

variable (D : ReadHeads B)

/-- One observation of the guarded solution is exactly the machine's selected
boundary, with each successor replaced by its guarded denotation. -/
theorem denote_observe (c : Configuration α Φ σ) :
    D.read (R.out (Answer α σ) (denote M R B instr c)) =
      (observe instr c).map (Sum.map id (denote M R B instr)) := by
  have eq : denote M R B instr = R.unfold (body B (observe instr)) := iterate_eq_unfold M R _ _
  rw [eq]
  exact Proofs.read_unfold B D R (observe instr) c

/-- Guarded iteration preserves and reflects finite machine returns, including the
final state in the answer. The reader specifies how the chosen parameter monad
exposes returns and instruction suspensions. -/
theorem denote_return_iff_run (det : InstrDeterministic instr) {c : Control α Φ}
    {s t : σ} {r : Result α} :
    FiniteReturn (fun q => D.read (R.out (Answer α σ) q))
      (denote M R B instr (c, s)) (r, t) ↔ Run instr c s r.control t := by
  rw [denote, iterate_eq_unfold]
  exact (finite_return_unfold B D R (observe instr) (c, s) (r, t)).trans
    (finite_return_iff_run det)

/-- In a deterministic instruction model, the returned guarded observations
agree with the existing LambdaSSA region semantics at every exit. -/
theorem denote_region_return_iff (det : InstrDeterministic instr)
    {env : Env α} {region : Isotope.LambdaSSA.Region Φ} {s t : σ} {l : Nat} {x : Value α} :
    FiniteReturn (fun q => D.read (R.out (Answer α σ) q))
      (denote M R B instr (startRegion env region, s)) (.region l x, t) ↔
      Isotope.LambdaSSA.Semantics.Region.Eval instr env region s l x t :=
  (denote_return_iff_run M R B instr D det).trans region_adequacy

open Isotope.Institution.Observational
open Isotope.Morphism.SSAIter (ScopedRegion envOfBound)

/-- The observational room's existing return observations agree with guarded
resumptions for every scoped region in a deterministic instruction model. -/
theorem room_return_iff {n labels : Nat} (model : Model.{u, u, u} Φ n)
    (det : InstrDeterministic model.instr) (r : ScopedRegion Φ labels n)
    (s t : model.σ) (l : Nat) (x : Value model.α) :
    Observation.ret s (l, x) t ∈ ssaBeh labels model r ↔
      FiniteReturn (fun q => D.read (R.out (Answer model.α model.σ) q))
        (denote M R B model.instr (startRegion (envOfBound model.bound) r.val, s))
        (.region l x, t) :=
  ret_mem_ssaBeh.trans (denote_region_return_iff M R B model.instr D det).symm

end Machine

end Silmaril.Isotope.Calco2019.Resumption
