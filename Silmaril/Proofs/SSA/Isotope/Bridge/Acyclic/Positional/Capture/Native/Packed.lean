module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Graph
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Join.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Region (HasType ValueBranches packedExitType packedExitArg)
open Region.Paper
open Region.Paper.RetainedLet (returnOnce)
open Native.SumBind
open Morphism.CaseSSA (erase erase_hasType)
open Silmaril.DeBruijn (lift)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {d n : Nat} {β : BoundCtx (Ty α) d} {L : LCtx (Ty α)}

omit [HasTy Φ (Ty α)] in
private theorem lift_agrees {σ υ : Nat → Region Φ} (K : LCtx (Ty α))
    (same : ∀ i A, At L i A → σ i = υ i) :
    ∀ i A, At (K ++ L) i A → Region.liftLSubstN K.length σ i = Region.liftLSubstN K.length υ i := by
  induction K with
  | nil => exact same
  | cons _ _ ih =>
    intro i A hit
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Region.renameLabels Nat.succ) (ih i A hit)

private theorem lsubst_agrees {Γ : VCtx (Ty α)} {r : Region Φ} (typed : HasType Γ r L)
    {σ υ : Nat → Region Φ} (same : ∀ i A, At L i A → σ i = υ i) :
    r.lsubst σ = r.lsubst υ := by
  have under {σ υ : Nat → Region Φ} {K : LCtx (Ty α)} (h : ∀ i A, At K i A → σ i = υ i) :
      ∀ i A, At K i A → Region.liftLSubstVars σ i = Region.liftLSubstVars υ i :=
    fun i A hi => congrArg (Region.renameVars (lift Nat.succ)) (h i A hi)
  induction typed generalizing σ υ with
  | @br _ _ i _ A hi _ => simp only [Region.lsubst, same i A hi]
  | let₁ _ _ ih => rw [Region.lsubst, Region.lsubst, ih (under same)]
  | let₂ _ _ ih => rw [Region.lsubst, Region.lsubst, ih (under (under same))]
  | case _ _ _ ihl ihr => rw [Region.lsubst, Region.lsubst, ihl (under same), ihr (under same)]
  | cfg R _ _ ihe ihb =>
    have moved := lift_agrees (List.ofFn R) same
    simp only [List.length_ofFn] at moved
    simp only [Region.lsubst, ihe moved, ihb _ (under moved)]

private abbrev packing (Φ : Type v) : Nat → Region Φ :=
  fun i => .br 0 (packedExitArg i (.var 0))

private theorem packing_lift : Region.liftLSubstVars (packing Φ) = packing Φ := by
  funext i
  change Region.br 0 ((packedExitArg i (.var 0 : Tm Φ)).rename (lift Nat.succ)) = _
  congr 1
  induction i <;> simp_all [packedExitArg, Tm.rename, lift]

private theorem packing_shift :
    Region.liftLSubstVars (Region.liftLSubst (packing Φ)) ∘ Nat.succ =
      Region.mapLSubstLabels Nat.succ (packing Φ) := by
  funext i
  change ((packing Φ i).renameLabels Nat.succ).renameVars (lift Nat.succ) = (packing Φ i).renameLabels Nat.succ
  rw [Region.renameVars_renameLabels]
  exact congrArg (Region.renameLabels Nat.succ) (congrFun (packing_lift (Φ := Φ)) i)

private theorem guarded_label {A : Ty α} (c : Code Φ β A) (i : Nat) (ρ : Nat → Nat) :
    (c.guardedSSA i).renameLabels ρ = c.guardedSSA (ρ i) := by
  rw [Code.guardedSSA, ← Region.bindBranchArguments_renameLabels, Code.toSSA_renameLabels]
  rfl

private theorem tag_replay {A : Ty α} {i : Nat} (out : At L i A) (a : Operand Φ β A) :
    Continuation.Eqv pe β.toList (returnOnce (erase (FiniteExit.tag L i out a).1))
      (.let₁ (erase a.1) (.br 0 (packedExitArg i (.var 0)))) [packedExitType L] := by
  induction L generalizing i with
  | nil => cases out
  | cons B L ih =>
    cases i with
    | zero =>
      cases Option.some.inj out
      exact Continuation.split_inl (erase_hasType a.2.toHasType)
    | succ i =>
      have inner := ih (i := i) out
      have typed := erase_hasType (FiniteExit.tag L i out a).2.toHasType
      have source := UnaryReturn.returnOnce_valueBranches typed
      have target := ValueBranches.let₁ (erase_hasType a.2.toHasType)
        (Region.packExits_valueFamily β.toList L out)
      let inject : Region Φ := .br 0 (.inr (.var 0))
      have injectTyped : HasType (packedExitType L :: β.toList) inject [Ty.coprod B (packedExitType L)] :=
        .br (ℓ := 0) rfl (.inr (.var (i := 0) rfl))
      have post := inner.lsubstPost (K := [Ty.coprod B (packedExitType L)]) (σ := fun _ => inject) source target
        (by
          intro j T hit
          have type_eq := List.mem_singleton.mp (List.mem_of_getElem? hit)
          cases type_eq
          exact injectTyped)
      change Continuation.Eqv pe β.toList
        ((Region.br 0 (erase (FiniteExit.tag L i out a).1)).bindBranchArguments.lsubst (fun _ => inject))
        _ _ at post
      rw [Region.lsubst_bindBranchArguments_br] at post
      exact (Continuation.split_inr typed).trans post

private theorem finite_pack (c : FiniteExit Φ L β) :
    Continuation.Eqv pe β.toList c.toSSA.bindBranchArguments.packExits (c.encode.guardedSSA 0) [packedExitType L] := by
  induction c with
  | @br _ γ i A out a =>
    change Continuation.Eqv pe γ.toList
      (.let₁ (erase a.1) ((Region.br i (.var 0)).lsubst (Region.liftLSubstVars (packing Φ))))
      (returnOnce (erase (FiniteExit.tag L i out a).1)) [packedExitType L]
    rw [packing_lift, show (Region.br i (.var 0 : Tm Φ)).lsubst (packing Φ) = _ from Region.packExits_br i (.var 0)]
    exact (tag_replay (pe := pe) out a).symm
  | case a _ _ ihl ihr =>
    simp only [FiniteExit.toSSA, Region.bindBranchArguments, Region.packExits, Region.lsubst, packing_lift,
      FiniteExit.encode, Code.guardedSSA, Code.toSSA] at ihl ihr ⊢
    exact .case (erase_hasType a.2.toHasType) ihl ihr
  | @join _ γ A entry body ih =>
    let R : Fin 1 → Ty α := fun _ => A
    have rows : List.ofFn R ++ [packedExitType L] = A :: [packedExitType L] := by
      simp [R, List.ofFn_succ]
    have kept := entry.guardedSSA_valueBranches (rfl : At [A] 0 A)
    have noOuter : (entry.guardedSSA 0).lsubst (Region.liftLSubst (packing Φ)) = entry.guardedSSA 0 := by
      rw [lsubst_agrees kept.hasType (υ := Region.labelId) (by
        intro i T hit
        cases i with
        | zero => rfl
        | succ i => simp [At] at hit), Region.lsubst_labelId]
    have shifted := ih.renameLabels (Ren.wk [packedExitType L] A)
    have head := Extension.Eqv.refl (Seed := Continuation.Seed pe)
      (entry.guardedSSA_valueBranches (rfl : At (A :: [packedExitType L]) 0 A)).hasType
    have blockPack :
        ((body.toSSA.renameLabels Nat.succ).bindBranchArguments).lsubst
            (Region.liftLSubstVars (Region.liftLSubst (packing Φ))) =
          body.toSSA.bindBranchArguments.packExits.renameLabels Nat.succ := by
      rw [Region.bindBranchArguments_renameLabels, Region.lsubst_renameLabels, packing_shift,
        Region.packExits, Region.renameLabels_lsubst]
    have h : Continuation.Eqv pe γ.toList
        (.cfg (entry.guardedSSA 0) 1 (fun _ => body.toSSA.bindBranchArguments.packExits.renameLabels Nat.succ))
        (.cfg (entry.guardedSSA 0) 1 (fun _ => (body.encode.guardedSSA 0).renameLabels Nat.succ))
        [packedExitType L] :=
      .cfg R (rows.symm ▸ head) (fun _ => rows.symm ▸ shifted)
    change Continuation.Eqv pe γ.toList
      (.cfg ((entry.guardedSSA 0).lsubst (Region.liftLSubst (packing Φ))) 1
        (fun _ => (body.toSSA.renameLabels (fun j => 1 + j)).bindBranchArguments.lsubst
          (Region.liftLSubstVars (Region.liftLSubst (packing Φ)))))
      (.cfg (entry.guardedSSA 0) 1 (fun _ => body.encode.guardedSSA 1)) [packedExitType L]
    have shift : (fun j : Nat => 1 + j) = Nat.succ := funext Nat.one_add
    rw [shift, noOuter, blockPack]
    rw [guarded_label] at h
    exact h

private theorem admitted (a : Tm Φ) : Recursive.Admitted a := by
  induction a <;> simp_all [Recursive.Admitted]

private theorem code_reify {A : Ty α} (c : Code Φ β A) {i : Nat} (out : At L i A) :
    Continuation.Eqv pe β.toList (c.guardedSSA i) ((Code.ofLetCase c.toLetCase.2).guardedSSA i) L := by
  induction c generalizing L i with
  | br a =>
    obtain ⟨_, _, _, written, reified⟩ := Recursive.normalize (pe := pe) out a (admitted (erase a.1))
    exact written.trans reified.symm
  | let₂ a _ ih => exact .let₂ (erase_hasType a.2.toHasType) (ih out)
  | case a _ _ ihl ihr => exact .case (erase_hasType a.2.toHasType) (ihl out) (ihr out)
  | @join _ _ B _ entry body ihe ihb =>
    let R : Fin 1 → Ty α := fun _ => B
    have rows : List.ofFn R ++ L = B :: L := by simp [R, List.ofFn_succ]
    exact .cfg R (rows.symm ▸ ihe (rfl : At (B :: L) 0 B))
      (fun _ => rows.symm ▸ ihb ((Ren.wk L B) out))
  | @let₁ _ _ B _ a body ih =>
    let tail := (Code.ofLetCase body.toLetCase.2).guardedSSA i
    let R : Fin 1 → Ty α := fun _ => B
    have rows : List.ofFn R ++ L = B :: L := by simp [R, List.ofFn_succ]
    obtain ⟨_, _, _, written, reified⟩ := Recursive.normalize (pe := pe)
      (rfl : At (B :: L) 0 B) a (admitted (erase a.1))
    have hb := (Code.ofLetCase body.toLetCase.2).guardedSSA_valueBranches out
    have one := (Code.br a).guardedSSA_valueBranches (rfl : At [B] 0 B)
    have linked := Region.Paper.linkedJoin one hb
    change Region.Paper.Eqv _ _ ((Region.br 0 (erase a.1)).bindBranchArguments.lsubst (fun _ => tail)) _ at linked
    rw [Region.lsubst_bindBranchArguments_br, guarded_label] at linked
    have moved := Extension.Eqv.let₁ (erase_hasType a.2.toHasType) (ih out)
    exact moved.trans ((Extension.Eqv.paper linked.symm).trans (.cfg R (rows.symm ▸ written.trans reified.symm)
      (fun _ => rows.symm ▸ Extension.Eqv.refl
        ((Code.ofLetCase body.toLetCase.2).guardedSSA_valueBranches ((Ren.wk L B) out)).hasType)))

theorem packed_reify_proof (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    ReplayEqv pe β.toList (p.toSSA i a).bindBranchArguments.packExits
      ((Code.ofLetCase (p.toLetCase ok i a).2).guardedSSA 0) [packedExitType L] := by
  let c := p.toFiniteExit ok i a
  have shape := bind_pack_eq_proof (toFiniteExit_replay_proof p ok i a)
  have finish := (finite_pack (pe := pe) c).trans (code_reify (pe := pe) c.encode (rfl : At [packedExitType L] 0 _))
  open Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding in
  exact (mapSeed Or.inl shape).trans (mapSeed Or.inr finish)

theorem packed_recompile_proof (p : Table Φ β L n) (ok : p.check = true)
    (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    ReplayEqv pe β.toList ((Code.ofLetCase (p.toLetCase ok i a).2).guardedSSA 0)
      (Reverse.tableGrammar p ok i a).toTable.toSSA.bindBranchArguments.packExits [packedExitType L] := by
  have replay := packed_reify_proof (pe := pe) p ok i a
  have rebuild := bind_pack_eq_proof (native_roundTrip_proof p ok i a)
  open Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding in
  exact replay.symm.trans (mapSeed Or.inl rebuild)

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂

theorem replay_sound_proof {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (M : TypeModel (Ty α) V) [InstructionModel J M Φ]
    [RegionTypingCoherent (Φ := Φ) J M]
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx (Ty α)} {r s : Region Φ}
    (h : ReplayEqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  apply Extension.Eqv.sound J M shared _ h hr hs
  intro _ _ _ _ step p q
  cases step with
  | inl graph => exact WithBoundEntryEta.seedDenotes J M shared graph p q
  | inr operand =>
    have eq := Continuation.sound J M shared (Extension.Eqv.extra p q operand) p q
    exact ⟨_, denoteRegion_spec J M p, eq.symm ▸ denoteRegion_spec J M q⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
