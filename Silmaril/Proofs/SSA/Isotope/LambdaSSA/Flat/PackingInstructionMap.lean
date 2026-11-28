module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open FiniteCFG Region
open Region.SyntacticCategory (iterationBody iterationDispatch)

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

private theorem map_liftSubst (σ : Nat → Tm Φ) :
    (fun i => (Tm.liftSubst σ i).mapInstr f) =
      Tm.liftSubst (fun i => (σ i).mapInstr f) := by
  funext i
  cases i <;> simp [Tm.liftSubst, Tm.mapInstr, Tm.mapInstr_rename]

private theorem map_liftSubstN (n : Nat) (σ : Nat → Tm Φ) :
    (fun i => (Tm.liftSubstN n σ i).mapInstr f) =
      Tm.liftSubstN n (fun i => (σ i).mapInstr f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Tm.liftSubstN, map_liftSubst, ih]

private theorem map_subst (t : Tm Φ) (σ : Nat → Tm Φ) :
    (t.subst σ).mapInstr f = (t.mapInstr f).subst (fun i => (σ i).mapInstr f) := by
  induction t generalizing σ <;> simp_all [Tm.subst, Tm.mapInstr, map_liftSubst, map_liftSubstN]

private theorem map_substVars (r : Region Φ) (σ : Nat → Tm Φ) :
    (r.substVars σ).mapInstr f = (r.mapInstr f).substVars (fun i => (σ i).mapInstr f) := by
  induction r generalizing σ <;> simp_all [Region.substVars, Region.mapInstr, map_subst,
    map_liftSubst, map_liftSubstN]

private theorem map_single (a : Tm Φ) :
    (fun i => (Tm.singleSubst a i).mapInstr f) = Tm.singleSubst (a.mapInstr f) := by
  funext i
  cases i <;> rfl

private theorem map_liftVars (σ : Nat → Region Φ) :
    (fun i => (liftLSubstVars σ i).mapInstr f) =
      liftLSubstVars (fun i => (σ i).mapInstr f) :=
  funext fun _ => Region.mapInstr_renameVars f _ _

private theorem map_lift (σ : Nat → Region Φ) :
    (fun i => (liftLSubst σ i).mapInstr f) =
      liftLSubst (fun i => (σ i).mapInstr f) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact Region.mapInstr_renameLabels f _ _

private theorem map_liftN (n : Nat) (σ : Nat → Region Φ) :
    (fun i => (liftLSubstN n σ i).mapInstr f) =
      liftLSubstN n (fun i => (σ i).mapInstr f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, map_lift, ih]

private theorem map_lsubst (r : Region Φ) (σ : Nat → Region Φ) :
    (r.lsubst σ).mapInstr f = (r.mapInstr f).lsubst (fun i => (σ i).mapInstr f) := by
  induction r generalizing σ <;> simp_all [lsubst, Region.mapInstr, map_substVars,
    map_single, map_liftVars, map_liftN]

private theorem map_compLSubst (σ υ : Nat → Region Φ) :
    (fun i => (compLSubst σ υ i).mapInstr f) =
      compLSubst (fun i => (σ i).mapInstr f) (fun i => (υ i).mapInstr f) := by
  funext i
  simp only [compLSubst, map_lsubst, map_liftVars]

private theorem map_bindBranchArguments (r : Region Φ) :
    r.bindBranchArguments.mapInstr f = (r.mapInstr f).bindBranchArguments := by
  induction r <;> simp_all [bindBranchArguments, Region.mapInstr, Tm.mapInstr]

private theorem map_packedExitArg (i : Nat) (a : Tm Φ) :
    (packedExitArg i a).mapInstr f = packedExitArg i (a.mapInstr f) := by
  induction i <;> simp_all [packedExitArg, Tm.mapInstr]

private theorem map_routeExit (blocks i : Nat) :
    (routeExit (Φ := Φ) blocks i).mapInstr f = routeExit blocks i := by
  unfold routeExit
  split <;> simp only [Region.mapInstr, Tm.mapInstr, map_packedExitArg]

private theorem map_unpackExits {τ : Type w} (L : LCtx τ) :
    (unpackExits (Φ := Φ) L).mapInstr f = unpackExits L := by
  induction L <;> simp_all [unpackExits, Region.mapInstr, Tm.mapInstr, Region.mapInstr_renameLabels]

theorem routedFlat_mapInstr {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n) :
    routedFlat blocks (r.mapInstr f) = (routedFlat blocks r).mapInstr f := by
  simp only [routedFlat, Flat.erase_mapInstr, map_lsubst, map_bindBranchArguments, map_routeExit]

private theorem map_iterationBody (r : Region Φ) :
    (iterationBody r).mapInstr f = iterationBody (r.mapInstr f) := by
  rw [iterationBody, map_lsubst]
  rfl

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]
  (profiles : InstructionMap.PreservesTypes (τ := τ) f)
  {blocks exits : Nat} {R : Fin blocks → τ} {L : Fin exits → τ}
  {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n} (hg : g.HasType β R L)

private theorem map_blockFamily :
    (fun i => ((blockFamily hg).val i).mapInstr f) =
      (blockFamily (hg.mapInstr profiles)).val := by
  funext i
  simp only [blockFamily, ContinuationFamily.ofTyped, map_bindBranchArguments]
  split <;> simp_all [FiniteCFG.mapInstr, Region.labelId, Region.mapInstr, Tm.mapInstr]

theorem packedDispatcherRegion_mapInstr :
    packedDispatcherRegion (hg.mapInstr profiles) = (packedDispatcherRegion hg).mapInstr f := by
  have routes : (fun i => ((routeFamily (Φ := Φ) (List.ofFn R) (List.ofFn L) β.toList).val i).mapInstr f) =
      (routeFamily (Φ := Ψ) (List.ofFn R) (List.ofFn L) β.toList).val :=
    funext (map_routeExit f _)
  have blocksMap := map_compLSubst f (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn L) β.toList).val
  rw [map_blockFamily f profiles hg, routes] at blocksMap
  have dispatcher := map_compLSubst f (fun _ => unpackExits (List.ofFn R))
    (compLSubst (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn L) β.toList).val)
  rw [blocksMap] at dispatcher
  simp only [map_unpackExits] at dispatcher
  exact (congrFun dispatcher 0).symm

theorem packedExecutionRegion_mapInstr :
    packedExecutionRegion (hg.mapInstr profiles) = (packedExecutionRegion hg).mapInstr f := by
  simp only [packedExecutionRegion, Region.mapInstr, map_iterationBody,
    ← routedFlat_mapInstr, ← packedDispatcherRegion_mapInstr f profiles hg]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat
