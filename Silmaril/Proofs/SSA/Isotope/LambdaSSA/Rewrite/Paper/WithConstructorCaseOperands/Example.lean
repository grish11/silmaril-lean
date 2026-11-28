module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.WithCaseOperandBeta.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Native replay and evaluation of the effectful packed fixture -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithConstructorCaseOperands
open Paper.WithConstructorCaseOperands.Example
open Paper.WithCaseBind.BitQuery hiding denote
open Paper.WithCaseBind.BitQuery.Execution
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext_of)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

theorem focused_replay {Γ L : VCtx (Ty Empty)} {r s : Region signature.Instr}
    (h : Paper.WithCaseBind.BitQuery.RequestTree.Readback.WithCaseOperandBeta.Step Γ r s L) :
    Eqv Γ r s L := by
  cases h with
  | @reduce Γ _ label b _ _ hl hr =>
    have ht (b : Bool) : Tm.HasType (Ty.unit :: Ty.unit :: Γ) (constructorBit b .unit) Bit :=
      (constructorBit_value b .unit).hasType
    cases b
    · exact (Step.caseCall (.ask label) (.left (.var (i := 0) rfl) (ht false) (ht true))
        rfl hl hr).replay
    · exact (Step.caseCall (.ask label) (.right (.var (i := 0) rfl) (ht false) (ht true))
        rfl hl hr).replay

theorem replay : Eqv [Bit] source target Exits := by
  apply Paper.Extension.Eqv.let₁ (.unit : Tm.HasType [Bit] .unit U)
  exact (Step.caseCall (.ask true)
    (.left (.var (i := 1) rfl) (selected_typed (i := 0) rfl) dead_typed) rfl exitLeft exitRight).replay

theorem packed_eq :
    Paper.Extension.Singleton.ofRegion Step source_typed.packExits =
      Paper.Extension.Singleton.ofRegion Step target_typed.packExits := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).2
  exact Paper.Extension.Eqv.lsubstPost replay source_typed target_typed
    (fun _ _ h => ((packExits_valueFamily [Bit] Exits) h).hasType)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false in
private theorem run_letUnit {r : Region signature.Instr} (hr : ValueBranches [U, Bit] r Exits)
    (g : Bool) : runAt (.let₁ .unit hr) (PUnit.unit, bit g) =
      runAt hr ((PUnit.unit, bit g), PUnit.unit) := by
  have d := RegionDenotes.let₁ Denotes.unit (denoteRegion_spec J M hr.hasType)
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map] at d
  unfold runAt
  rw [← d.eq_denote J M, Category.assoc]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure ((PUnit.unit, bit g), PUnit.unit))
    (fun x => runAt hr x) = _
  rw [pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem selected_execution (g : Bool) :
    ∃ f, Denotes J M (selected_typed (Γ := [U, Bit]) (i := 1) rfl) f ∧
      f.of ((PUnit.unit, bit g), PUnit.unit) =
        (request false (bit g) >>= fun | .inl a | .inr a => pure a) := by
  let op : signature.Instr := .ask false
  let arg : At [U, Bit] 1 Bit := rfl
  let reply : At [Bit, U, Bit] 0 Bit := rfl
  have ask : Denotes J M (.op (f := op) (.var arg))
      ((J).map (lookup M 1 arg) ≫ (Kleisli.instructions model).denote op) := .op (.var arg)
  have d := Denotes.case ask
    (Denotes.var (Φ := signature.Instr) (i := 0) reply) (Denotes.var (i := 0) reply)
  refine ⟨_, d, ?_⟩
  erw [caseWithContext_of (m := Trace)]
  simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  have coord (v : value Answer) :
      (Types.binaryCoproductIso (value Bit) (value Bit)).hom (((M).coprodIso Bit Bit).hom v) = v :=
    ConcreteCategory.congr_hom (Types.binaryCoproductIso (value Bit) (value Bit)).inv_hom_id v
  have initial : ((J).map (lookup M 1 arg)).of ((PUnit.unit, bit g), PUnit.unit) =
      (pure (bit g) : Trace (value Bit)) := rfl
  have instruction : (TypeCat.Hom.hom ((Kleisli.instructions model).denote op).of) (bit g) =
      request false (bit g) := rfl
  have injection (v : value Answer) : ((J).map ((M).coprodIso Bit Bit).hom).of v =
      (pure (((M).coprodIso Bit Bit).hom v) : Trace _) := rfl
  have read (a : value Bit) :
      ((J).map (lookup M 0 reply)).of (((PUnit.unit, bit g), PUnit.unit), a) =
        (pure a : Trace (value Bit)) := rfl
  rw [initial]
  change Bind.bind (m := Trace) (Bind.bind (m := Trace)
    (Bind.bind (m := Trace) (pure (bit g)) ((Kleisli.instructions model).denote op).of.hom)
    (fun v => ((J).map ((M).coprodIso Bit Bit).hom).of v)) _ = _
  simp only [injection, bind_assoc, pure_bind]
  rw [instruction]
  apply congrArg (Bind.bind (m := Trace) (request false (bit g)))
  funext v
  erw [coord v]
  cases v <;> apply read

set_option backward.isDefEq.respectTransparency false in
private theorem exit_execution (x : ctxObj M [Bit, U, Bit]) (b : Bool) :
    (if b then runAt exitRight x else runAt exitLeft x) =
      pure (if b then Sum.inr (Sum.inl x.2) else Sum.inl x.2) := by
  have finish (ℓ : Nat) (h : At Exits ℓ Bit) :
      runAt (.br h (.var (i := 0) (rfl : At [Bit, U, Bit] 0 Bit))) x =
        pure ((packedLabelInject M ℓ h) x.2) := by
    unfold runAt
    erw [← (RegionDenotes.br (h := h) (Denotes.var («J» := J) («M» := M)
      (Φ := signature.Instr) (i := 0) (rfl : At [Bit, U, Bit] 0 Bit))).eq_denote J M]
    have comp := (J).map_comp (labelInject M ℓ h) (packLabel M Exits)
    erw [Category.assoc, ← comp, labelInject_packLabel, Kleisli.Type.comp_of_eq_kleisliRight]
    exact pure_bind _ _
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [finish 0 rfl]
    apply congrArg (pure (f := Trace))
    exact ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType [Bit]))) x.2
  · simp only [ite_true]
    rw [finish 1 rfl]
    apply congrArg (pure (f := Trace))
    simp only [packedLabelInject, eqToHom_refl, Category.id_comp, Category.assoc]
    have inner := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_hom (value Bit) (value (packedExitType []))) x.2
    have outer := ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_hom (value Bit) (value (packedExitType [Bit])))
        (Sum.inl x.2 : value (packedExitType [Bit]))
    change (coprod.inr ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType [Bit]))).hom)
      ((coprod.inl ≫ (Types.binaryCoproductIso (value Bit) (value (packedExitType []))).hom) x.2) = _
    rw [inner]
    exact outer

set_option backward.isDefEq.respectTransparency false in
private theorem target_execution (g : Bool) :
    runAt target_typed (PUnit.unit, bit g) =
      (request false (bit g) >>= fun first =>
        let q := match first with | .inl a | .inr a => a
        request true q >>= fun
          | .inl a => pure (Sum.inl a)
          | .inr a => pure (Sum.inr (Sum.inl a))) := by
  change runAt (.let₁ .unit (.case (.op (f := (show signature.Instr from .ask true))
    (selected_typed (i := 1) rfl)) exitLeft exitRight)) _ = _
  rw [run_letUnit (.case (.op (f := (show signature.Instr from .ask true))
    (selected_typed (i := 1) rfl)) exitLeft exitRight)]
  obtain ⟨f, d, hf⟩ := selected_execution g
  let op : signature.Instr := .ask true
  have call : Denotes J M (.op (f := op) (selected_typed (i := 1) rfl))
      (f ≫ (Kleisli.instructions model).denote op) := .op d
  rw [case_run call exitLeft exitRight]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (Bind.bind (m := Trace)
    (f.of ((PUnit.unit, bit g), PUnit.unit)) (request true)) _ = _
  rw [hf]
  simp only [bind_assoc]
  apply congrArg (Bind.bind (m := Trace) (request false (bit g)))
  funext first
  cases first with
  | inl a =>
    rw [pure_bind]
    apply congrArg (Bind.bind (m := Trace) (request true a))
    funext reply
    cases reply
    · exact exit_execution _ false
    · exact exit_execution _ true
  | inr a =>
    rw [pure_bind]
    apply congrArg (Bind.bind (m := Trace) (request true a))
    funext reply
    cases reply
    · exact exit_execution _ false
    · exact exit_execution _ true

theorem packed_execution (g : Bool) :
    ((denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)).map
      (Paper.Extension.Singleton.ofRegion Step source_typed.packExits)).of (bit g) =
      (request false (bit g) >>= fun first =>
        let q := match first with | .inl a | .inr a => a
        request true q >>= fun
          | .inl a => pure (Sum.inl a)
          | .inr a => pure (Sum.inr (Sum.inl a))) := by
  rw [packed_eq]
  unfold denoteFunctor
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  refine Eq.trans ?_ (target_execution g)
  have h := run_packed target_typed g
  let sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M :=
    Paper.WithCaseBind.joined_seedDenotes J M
      (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩) sound).map
    (Paper.Extension.Singleton.ofRegion Seed target_typed.packExits)).of (bit g) = _ at h
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion (sound := sound)] at h
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorCaseOperands
