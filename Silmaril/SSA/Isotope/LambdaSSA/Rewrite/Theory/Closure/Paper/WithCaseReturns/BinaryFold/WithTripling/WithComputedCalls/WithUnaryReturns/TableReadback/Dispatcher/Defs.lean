module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # A guarded representative for the actual captured dispatcher -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (seqValueBranches caseValueBranches productSndBranches)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The empty dispatcher has no possible packed input. -/
noncomputable def emptyDispatchRep (D : τ) :
    {r : Region Φ // ValueBranches [Silmaril.empty] r [D]} :=
  let h := Paper.TypeCategory.exists_ofRegion
    ((Paper.TypeCategory.emptyIsInitial (Φ := Φ)).to (Paper.TypeCategory.ofType D))
  ⟨h.choose, h.choose_spec.choose⟩

/-- Distribute the capture over the exact input sum, selecting the head row
or the dispatcher for the remaining labels. -/
noncomputable def dispatcherRep (X : τ) {D : τ} :
    (L : LCtx τ) →
      (∀ i : Fin L.length, {r : Region Φ // ValueBranches [product X (L.get i)] r [D]}) →
      {r : Region Φ // ValueBranches [product X (packedExitType L)] r [D]}
  | [], _ => ⟨_, seqValueBranches (productSndBranches X Silmaril.empty) (emptyDispatchRep D).property⟩
  | A :: L, rows => ⟨_, seqValueBranches (distributorRegion_typed X A (packedExitType L))
      (caseValueBranches (rows 0).property (dispatcherRep X L (fun i => rows i.succ)).property)⟩

/-- A single guarded region for the exact captured readback assembly. It
uses one local feedback label around the typed ordered dispatcher. -/
noncomputable def packedReadbackRep {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    {r : Region Φ // ValueBranches [X] r [D]} :=
  let dispatcher := dispatcherRep X (List.ofFn R) (orderedRow R hb)
  ⟨_, seqValueBranches (entry_route R he)
    (caseValueBranches (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      (SyntacticCategory.iterateRegion_valueBranches dispatcher.property))⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
