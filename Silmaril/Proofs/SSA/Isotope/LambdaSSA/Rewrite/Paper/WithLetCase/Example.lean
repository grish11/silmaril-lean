module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Thms

/-! # Execution at the exact packed endpoints -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithLetCase Paper.WithLetCase.Example
open Paper.WithCaseBind.BitQuery hiding denote
open Paper.WithCaseBind.BitQuery.Execution
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open CategoryTheory CategoryTheory.Limits

theorem packed_eq :
    Paper.Extension.Singleton.ofRegion Step source_typed.packExits =
      Paper.Extension.Singleton.ofRegion Step target_typed.packExits := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).2
  exact Paper.Extension.Eqv.lsubstPost
    (distribute test_typed left_typed right_typed next_typed.hasType) source_typed target_typed
    (fun _ _ h => ((packExits_valueFamily [Bit] Exits) h).hasType)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false in
private theorem ask_run {Γ : VCtx (Ty Empty)} {i : Nat} (label : Bool) (hi : At Γ i Bit)
    {l r : Region signature.Instr} (hl : ValueBranches (Bit :: Γ) l Exits)
    (hr : ValueBranches (Bit :: Γ) r Exits) (x : ctxObj M Γ) :
    runAt (.case (.op (f := (show signature.Instr from .ask label)) (.var hi)) hl hr) x =
      (request label ((lookup M i hi) x) >>= fun
        | .inl a => runAt hl (x, a)
        | .inr a => runAt hr (x, a)) := by
  let op : signature.Instr := .ask label
  have d : Denotes J M (.op (f := op) (.var hi))
      ((J).map (lookup M i hi) ≫ (Kleisli.instructions model).denote op) := .op (.var hi)
  rw [case_run d hl hr x]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace)
    (Bind.bind (m := Trace) (pure ((lookup M i hi) x)) (request label)) _ = _
  rw [pure_bind]
  congr 1
  funext v
  cases v <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem branch_run {Γ : VCtx (Ty Empty)} {i ℓ : Nat}
    (hi : At Γ i Bit) (hℓ : At Exits ℓ Bit) (x : ctxObj M Γ) :
    runAt (.br hℓ (.var hi)) x = pure ((packedLabelInject M ℓ hℓ) ((lookup M i hi) x)) := by
  unfold runAt
  erw [← (RegionDenotes.br (h := hℓ) (Denotes.var («J» := J) («M» := M)
    (Φ := signature.Instr) hi)).eq_denote J M]
  have comp := (J).map_comp (labelInject M ℓ hℓ) (packLabel M Exits)
  erw [Category.assoc, ← comp, labelInject_packLabel, Kleisli.Type.comp_of_eq_kleisliRight]
  exact pure_bind _ _

private theorem exitZero (a : value Bit) :
    (packedLabelInject M 0 (rfl : At Exits 0 Bit)) a = Sum.inl a :=
  ConcreteCategory.congr_hom
    (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType [Bit]))) a

private theorem exitOne (a : value Bit) :
    (packedLabelInject M 1 (rfl : At Exits 1 Bit)) a = Sum.inr (Sum.inl a) := by
  simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
  have inner := ConcreteCategory.congr_hom
    (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType []))) a
  have outer := ConcreteCategory.congr_hom
    (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit])))
      (Sum.inl a : value (packedExitType [Bit]))
  change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
    ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType []))).hom) a) = _
  rw [inner]
  exact outer

private theorem keepCapture :
    ValueBranches [Bit, Bit, Bit] (.br 0 (.var 2) : Region signature.Instr) Exits :=
  .br (ℓ := 0) rfl (.var (i := 2) rfl)

private theorem keepReply :
    ValueBranches [Bit, Bit, Bit] (.br 1 (.var 0) : Region signature.Instr) Exits :=
  .br (ℓ := 1) rfl (.var (i := 0) rfl)

private theorem arm_typed {t : Tm signature.Instr} (ht : Tm.HasType [Bit, Bit] t Answer) :
    ValueBranches [Bit, Bit] (.let₁ t (next.renameVars (Silmaril.DeBruijn.lift Nat.succ))) Exits :=
  .let₁ ht (Paper.RetainedCase.boundCase_typed keepCapture keepReply)

set_option backward.isDefEq.respectTransparency false in
private theorem arm_run {i : Nat} (label : Bool) (hi : At [Bit, Bit] i Bit)
    (g : Bool) (payload : value Bit) :
    runAt (arm_typed (.op (f := (show signature.Instr from .ask label)) (.var hi)))
      ((PUnit.unit, bit g), payload) =
        (request label ((lookup M i hi) ((PUnit.unit, bit g), payload)) >>= finish g) := by
  let ht : Tm.HasType [Bit, Bit] (.op (.ask label) (.var i) : Tm signature.Instr) Answer := .op (.var hi)
  let h := Paper.WithCaseBind.Step.bind ht keepCapture keepReply
  obtain ⟨_, dl, dr⟩ := Paper.WithCaseBind.step_denotes J M h
    h.valueBranches.1.hasType h.valueBranches.2.hasType
  calc
    _ = runAt (.case ht keepCapture keepReply) ((PUnit.unit, bit g), payload) := by
      unfold runAt
      rw [(dr.eq_denote J M).symm.trans (dl.eq_denote J M)]
    _ = _ := by
      rw [ask_run label hi keepCapture keepReply]
      apply congrArg (Bind.bind (m := Trace) _)
      funext reply
      cases reply with
      | inl a =>
        change runAt keepCapture (((PUnit.unit, bit g), payload), a) = _
        rw [branch_run (rfl : At [Bit, Bit, Bit] 2 Bit) (rfl : At Exits 0 Bit), exitZero]
        rfl
      | inr a =>
        change runAt keepReply (((PUnit.unit, bit g), payload), a) = _
        rw [branch_run (rfl : At [Bit, Bit, Bit] 0 Bit) (rfl : At Exits 1 Bit), exitOne]
        rfl

set_option backward.isDefEq.respectTransparency false in
private theorem run_target (g : Bool) :
    runAt target_typed (PUnit.unit, bit g) = expected g := by
  change runAt (.case test_typed (arm_typed left_typed) (arm_typed right_typed)) _ = _
  rw [ask_run false (rfl : At [Bit] 0 Bit) (arm_typed left_typed) (arm_typed right_typed)]
  change Bind.bind (m := Trace) (request false (bit g)) _ = expected g
  unfold expected
  apply congrArg (Bind.bind (m := Trace) (request false (bit g)))
  funext reply
  cases reply with
  | inl a => exact arm_run false (rfl : At [Bit, Bit] 1 Bit) g a
  | inr a => exact arm_run true (rfl : At [Bit, Bit] 0 Bit) g a

theorem packed_execution (g : Bool) :
    ((denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)).map
      (Paper.Extension.Singleton.ofRegion Step source_typed.packExits)).of (bit g) = expected g := by
  rw [packed_eq]
  unfold denoteFunctor
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  refine Eq.trans ?_ (run_target g)
  have h := run_packed target_typed g
  let sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M :=
    Paper.WithCaseBind.joined_seedDenotes J M
      (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩) sound).map
    (Paper.Extension.Singleton.ofRegion Seed target_typed.packExits)).of (bit g) = _ at h
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion (sound := sound)] at h
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithLetCase
