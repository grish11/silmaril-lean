module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns (Step Eqv)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (carryExit carryExit_typed entry_route Readback outwardEntry)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff ofType projection sumCofan sumCofanIsColimit)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion S

set_option backward.isDefEq.respectTransparency false

private theorem outward_cfg {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ} {blocks : Fin n → Region Φ}
    (he : ValueBranches [X] e [D])
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Paper.Eqv [X] (.cfg (e.renameLabels (n + ·)) n blocks) e [D] := by
  cases n with
  | zero =>
    rw [show (fun j : Nat => 0 + j) = id from funext Nat.zero_add, renameLabels_id]
    exact .cfgEta (.native (.base (.entry (.cfgZero he.hasType blocks))))
  | succ n => exact .cfgEta (.native (.cfgOutward R he.hasType (fun i => (hb i).hasType)))

private theorem outward_route {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    (he : ValueBranches [X] e [D]) :
    Lit (entry_route R (outwardEntry R he)) =
      Lit he ≫ (sumCofan S D (product X (packedExitType (List.ofFn R)))).inl := by
  let state := product X (packedExitType (List.ofFn R))
  let inject : ValueBranches [D] (.br 0 (.inl (.var 0)) : Region Φ) [coprod D state] :=
    .br (ℓ := 0) rfl (.inl (.var rfl))
  have shape : (e.renameLabels (n + ·)).lsubst (carryExit 0 n) =
      compLSubst (fun _ => e) (fun _ => .br 0 (.inl (.var 0))) 0 := by
    rw [lsubst_renameLabels]
    congr 1
    funext j
    exact ite_eq_right (Nat.not_lt_of_ge (Nat.le_add_right n j))
  have hh : ValueBranches [X] (compLSubst (fun _ => e) (fun _ => .br 0 (.inl (.var 0))) 0)
      [coprod D state] := shape ▸ entry_route R (outwardEntry R he)
  have injected : (sumCofan S D state).inl = Lit inject :=
    congrArg (projection S).map (Paper.TypeCategory.sumCofan_inl (Φ := Φ) D state)
  have composition : Lit he ≫ Lit inject = Lit hh :=
    ((projection S).map_comp (Paper.TypeCategory.ofRegion he) (Paper.TypeCategory.ofRegion inject)).symm.trans
      (congrArg (projection S).map (Paper.TypeCategory.ofRegion_comp he inject hh))
  rw [injected, composition]
  apply (ofRegion_eq_iff S _ _).2
  rw [← shape]
  exact .paper (.refl (entry_route R (outwardEntry R he)).hasType)

theorem readback_outward
  {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ} {blocks : Fin n → Region Φ}
    (he : ValueBranches [X] e [D])
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R (outwardEntry R he) hb := by
  dsimp only [Readback]
  rw [outward_route pe R he]
  have remove : Lit (.cfg R (outwardEntry R he) hb) = Lit he :=
    (ofRegion_eq_iff S _ _).2 (.paper (outward_cfg R he hb))
  rw [remove, Category.assoc]
  let state := product X (packedExitType (List.ofFn R))
  let exit := 𝟙 (ofType S D)
  have route (k : ofType S state ⟶ ofType S D) :
      (sumCofan S D state).inl ≫ exactCopair S exit k = exit :=
    (sumCofanIsColimit S D state).fac (BinaryCofan.mk exit k) ⟨WalkingPair.left⟩
  rw [route, Category.comp_id]

theorem readback_of_outward_eqv
    {n : Nat} (R : Fin n → τ) {X D : τ} {written e : Region Φ} {blocks : Fin n → Region Φ}
    (hw : ValueBranches [X] written (List.ofFn R ++ [D])) (he : ValueBranches [X] e [D])
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (route : Eqv pe [X] written (e.renameLabels (n + ·)) (List.ofFn R ++ [D])) :
    Readback pe R hw hb := by
  have routed : LSubst.ValueFamily [X] (List.ofFn R ++ [D])
      [coprod D (product X (packedExitType (List.ofFn R)))] (carryExit 0 n : Nat → Region Φ) := by
    simpa only [List.length_ofFn] using carryExit_typed (List.ofFn R) (rfl : At [X] 0 X)
  have start := (ofRegion_eq_iff S (entry_route R hw) (entry_route R (outwardEntry R he))).2
    (.lsubstPost route hw (outwardEntry R he) (fun _ _ hi => (routed hi).hasType))
  have table := (ofRegion_eq_iff S (.cfg R hw hb) (.cfg R (outwardEntry R he) hb)).2
    (.cfg R route (fun i => .paper (.refl (hb i).hasType)))
  dsimp only [Readback]
  rw [start, table]
  exact readback_outward pe R he hb

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.TableReadback
