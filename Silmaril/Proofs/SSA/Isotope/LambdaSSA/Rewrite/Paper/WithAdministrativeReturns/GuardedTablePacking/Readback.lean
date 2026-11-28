module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.CfgEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithAdministrativeReturns.WithGuardedTablePacking
open Paper.WithCaseReturns.BinaryFold.WithTripling (capturedDispatcher)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (entry_route orderedRow orderedRows capturedDispatcher_ofRep dispatcherRep packedReadbackRep)
open CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff ofType projection iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "N" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion N

set_option backward.isDefEq.respectTransparency false

/-- The assembled side is the literal packed representative. This uses
only inherited equations, at any arity. -/
theorem readback_iff_eqv {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R he hb ↔ Eqv pe [X] (.cfg e n blocks) (packedReadbackRep R he hb).val [D] := by
  let dispatcher := dispatcherRep X (List.ofFn R) (orderedRow R hb)
  let hid : ValueBranches [D] (.br 0 (.var 0) : Region Φ) [D] :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  let loop := SyntacticCategory.iterateRegion_valueBranches dispatcher.property
  have hId : 𝟙 (ofType N D) = Lit hid :=
    ((projection N).map_id (Paper.TypeCategory.ofType D)).symm.trans
      (congrArg (projection N).map (Paper.TypeCategory.ofRegion_id (Φ := Φ) D).symm)
  have hIter : iterateSum N (Lit dispatcher.property) = Lit loop :=
    (iterateSum_map N (Paper.TypeCategory.ofRegion dispatcher.property)).trans
      (congrArg (projection N).map (Paper.TypeCategory.iterateSum_ofRegion dispatcher.property))
  have rhs : Lit (entry_route R he) ≫ exactCopair N (Lit hid) (Lit loop) =
      Lit (packedReadbackRep R he hb).property := by
    rw [exactCopair_ofRegion]
    exact ((projection N).map_comp
      (Paper.TypeCategory.ofRegion (entry_route R he))
      (Paper.TypeCategory.ofRegion (caseValueBranches hid loop))).symm.trans
      (congrArg (projection N).map
        (Paper.TypeCategory.ofRegion_comp (entry_route R he) (caseValueBranches hid loop)
          (seqValueBranches (entry_route R he) (caseValueBranches hid loop))))
  have hStep : (fromTripling pe).map
      (capturedDispatcher pe X (List.ofFn R) (orderedRows pe R hb)) = Lit dispatcher.property :=
    congrArg (fromTripling pe).map
      (capturedDispatcher_ofRep pe X _ (List.ofFn R) (orderedRow R hb))
  dsimp only [Readback]
  rw [hStep]
  change (Lit (.cfg R he hb) = Lit (entry_route R he) ≫
    exactCopair N (𝟙 (ofType N D)) (iterateSum N (Lit dispatcher.property))) ↔ _
  rw [hId, hIter, rhs]
  exact ofRegion_eq_iff N _ _

variable {n : Nat} (R : Fin n → τ) {X : τ} {L : LCtx τ} {e : Region Φ} {blocks : Fin n → Region Φ}

theorem tagExits_family (Γ : VCtx τ) :
    LSubst.ValueFamily Γ (List.ofFn R ++ L) (List.ofFn R ++ [packedExitType L])
      (tagExits n : Nat → Region Φ) := by
  simpa only [tagExits, List.length_ofFn] using (packExits_valueFamily Γ L).append (List.ofFn R)

theorem tagExits_entry (he : ValueBranches [X] e (List.ofFn R ++ L)) :
    ValueBranches [X] (e.lsubst (tagExits n)) (List.ofFn R ++ [packedExitType L]) :=
  he.lsubst (tagExits_family R [X])

theorem tagExits_row (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L)) (i : Fin n) :
    ValueBranches [R i, X] ((blocks i).lsubst (liftLSubstVars (tagExits n)))
      (List.ofFn R ++ [packedExitType L]) :=
  (hb i).lsubst ((tagExits_family R [X]).liftVars (R i))

theorem tagExits_local : ∀ (n i : Nat), i < n → (tagExits n i : Region Φ) = .br i (.var 0)
  | n + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    change ((tagExits n i : Region Φ)).renameLabels Nat.succ = _
    rw [tagExits_local n i (Nat.lt_of_succ_lt_succ h)]
    rfl

theorem tagExits_outward : ∀ (n j : Nat),
    (tagExits n (n + j) : Region Φ) = .br n (packedExitArg j (.var 0))
  | 0, j => by rw [Nat.zero_add]; rfl
  | n + 1, j => by
    rw [Nat.add_right_comm]
    change ((tagExits n (n + j) : Region Φ)).renameLabels Nat.succ = _
    rw [tagExits_outward n j]
    rfl

/-- Tag the exits, apply the one added equation, and decode. The native
packing retraction returns the first region to the written table. -/
theorem retraction {n : Nat} (R : Fin (n + 1) → τ) {X : τ} {L : LCtx τ} {e : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ L))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ L)) :
    Eqv pe [X] (.cfg e (n + 1) blocks)
      ((packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).val.lsubst
        (fun _ => unpackExits L)) L := by
  have native : Eqv pe [X]
      ((Region.cfg e (n + 1) blocks).packExits.lsubst (fun _ => unpackExits L))
      (.cfg e (n + 1) blocks) L :=
    .paper (.cfgEta (.native (ValueBranches.cfg R he hb).unpack_packExits))
  have packed := Paper.Extension.Eqv.lsubstPost
    (pack pe R (tagExits_entry R he) (tagExits_row R hb))
    (.cfg R (tagExits_entry R he) (tagExits_row R hb))
    (packedReadbackRep R (tagExits_entry R he) (tagExits_row R hb)).property
    (fun _ _ hi => (unpackExits_valueFamily [X] L hi).hasType)
  exact native.symm.trans packed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
