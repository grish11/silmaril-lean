module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.Execution.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryExecution

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer bit answer)
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open scoped MonoidalCategory

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types
local notation "U" => (Ty.unit : Ty Empty)

noncomputable local instance : InstructionModel J M signature.Instr := Kleisli.instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

open Paper.WithCaseBind.BitQuery.Execution
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext_of)
open Silmaril.Isotope.LetIter.Semantics.Categorical (case_postcomp)

set_option backward.isDefEq.respectTransparency false in
theorem case_run {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm signature.Instr}
    {l r : Region signature.Instr} {ha : Tm.HasType Γ a (coprod A B)}
    {sa : (J).obj (ctxObj M Γ) ⟶ (J).obj (value (coprod A B))}
    (d : Denotes J M ha sa) (hl : ValueBranches (A :: Γ) l Exits)
    (hr : ValueBranches (B :: Γ) r Exits) (x : ctxObj M Γ) :
    runAt (.case ha hl hr) x =
      Bind.bind (m := Trace) (sa.of x)
        (fun | .inl a => runAt hl (x, a) | .inr b => runAt hr (x, b)) := by
  have h := RegionDenotes.eq_denote J M
    (.case d (denoteRegion_spec J M hl.hasType) (denoteRegion_spec J M hr.hasType))
  unfold runAt
  erw [← h, case_postcomp J, caseWithContext_of (m := Trace)]
  simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  have coord (v : value (coprod A B)) :
      (Types.binaryCoproductIso ((M).obj A) ((M).obj B)).hom (((M).coprodIso A B).hom v) = v :=
    ConcreteCategory.congr_hom (Types.binaryCoproductIso (value A) (value B)).inv_hom_id v
  change Bind.bind (m := Trace) (Bind.bind (m := Trace) (sa.of x)
    (fun v => pure (((M).coprodIso A B).hom v))) _ = _
  simp only [bind_assoc, pure_bind, coord]
  congr 1
  funext reply
  cases reply <;> rfl

private noncomputable abbrev queryConst (Γ : VCtx (Ty Empty)) (b : Bool) :
    ctxObj M Γ ⟶ value Bit := TypeCat.ofHom (fun _ => bit b)

set_option backward.isDefEq.respectTransparency false in
private theorem literal_denotes (Γ : VCtx (Ty Empty)) (b : Bool) :
    Denotes J M ((constructorBit_value (Γ := Γ) b .unit).hasType) ((J).map (queryConst Γ b)) := by
  cases b
  · have eq : queryConst Γ false =
        (SemiCartesianMonoidalCategory.toUnit (ctxObj M Γ) ≫ (M).unitIso.inv) ≫
          coprod.inl ≫ ((M).coprodIso U U).inv := by
      have coordinate := Types.binaryCoproductIso_inl_comp_hom (value U) (value U)
      change queryConst Γ false = (_ ≫ coprod.inl ≫
        (Types.binaryCoproductIso (value U) (value U)).hom)
      rw [coordinate]
      rfl
    rw [eq, (J).map_comp]
    exact .inl .unit
  · have eq : queryConst Γ true =
        (SemiCartesianMonoidalCategory.toUnit (ctxObj M Γ) ≫ (M).unitIso.inv) ≫
          coprod.inr ≫ ((M).coprodIso U U).inv := by
      have coordinate := Types.binaryCoproductIso_inr_comp_hom (value U) (value U)
      change queryConst Γ true = (_ ≫ coprod.inr ≫
        (Types.binaryCoproductIso (value U) (value U)).hom)
      rw [coordinate]
      rfl
    rw [eq, (J).map_comp]
    exact .inr .unit

set_option backward.isDefEq.respectTransparency false in
theorem request_case_run {Γ : VCtx (Ty Empty)} {l r : Region signature.Instr}
    (label b : Bool) (hl : ValueBranches (Bit :: Γ) l Exits) (hr : ValueBranches (Bit :: Γ) r Exits)
    (x : ctxObj M Γ) :
    runAt (.case (.op (f := (show signature.Instr from .ask label))
      (constructorBit_value b .unit).hasType) hl hr) x =
      (request label (bit b) >>= fun | .inl a => runAt hl (x, a) | .inr a => runAt hr (x, a)) := by
  let op : signature.Instr := .ask label
  have d : Denotes J M (.op (f := op) (constructorBit_value b .unit).hasType)
      ((J).map (queryConst Γ b) ≫ (Kleisli.instructions model).denote op) :=
    .op (literal_denotes Γ b)
  rw [case_run d hl hr x]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (Bind.bind (m := Trace) (pure (bit b)) (request label)) _ = _
  rw [pure_bind]
  congr 1
  funext reply
  cases reply <;> rfl

theorem run_packed {r : Region signature.Instr} (hr : ValueBranches [Bit] r Exits) (g : Bool) :
    (denote.map (Paper.Extension.Singleton.ofRegion Seed hr.packExits)).of (bit g) =
      runAt hr (PUnit.unit, bit g) := by
  let sound : Paper.Extension.Singleton.SeedDenotes (Seed := Seed) J M :=
    Paper.WithCaseBind.joined_seedDenotes J M
      (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩) sound).map
    (Paper.Extension.Singleton.ofRegion Seed hr.packExits)).of (bit g) = _
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  unfold denoteSingletonRegion
  change (((J).map _ ≫ denoteRegion J M hr.hasType.packExits ≫ (J).map _)).of (bit g) = _
  rw [denoteRegion_packExits_valueBranches J M (fun _ _ => ⟨rfl, rfl⟩) hr]
  have combine : packLabelExit M Exits ≫ singletonLabelPayload M (packedExitType Exits) = packLabel M Exits := by
    unfold packLabelExit
    rw [Category.assoc, SingletonDispatcher.labelInject_payload, Category.comp_id]
  simp only [Category.assoc, ← (J).map_comp, combine]
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Trace) (pure (PUnit.unit, bit g))
    (fun x => runAt hr x) = _
  rw [pure_bind]
  rfl

private theorem queryBit_bit (b : Bool) : queryBit (bit b) = b := by cases b <;> rfl

theorem bind_request {A : Type} (label b : Bool) (next : value Answer → Trace A)
    (result : Except Bool A) (word : FreeMonoid Event) :
    (result, word) ∈ (request label (bit b) >>= next).outcomes ↔
      ∃ (reply : Bool × Bool) (tail : FreeMonoid Event), (result, tail) ∈ (next (answer reply.1 reply.2)).outcomes ∧
        FreeMonoid.of ⟨label, b, reply.1, reply.2⟩ * tail = word := by
  rw [Tagged.mem_bind]
  simp only [request, Tagged.outcomes_ofOutcomes, queryBit_bit]
  constructor
  · rintro (⟨fault, _, ⟨reply, bad⟩⟩ | ⟨a, u, v, ⟨reply, h⟩, hv, hw⟩)
    · cases (congrArg Prod.fst bad : Except.ok (answer reply.1 reply.2) = Except.error fault)
    · rcases Prod.mk.inj h with ⟨ha, hu⟩
      exact ⟨reply, v, Except.ok.inj ha ▸ hv, hu.symm ▸ hw⟩
  · rintro ⟨reply, v, hv, hw⟩
    exact Or.inr ⟨answer reply.1 reply.2, _, v, ⟨reply, rfl⟩, hv, hw⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryExecution
