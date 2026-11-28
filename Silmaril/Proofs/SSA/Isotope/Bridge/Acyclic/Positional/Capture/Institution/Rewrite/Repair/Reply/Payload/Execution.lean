module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Replay

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Kleisli (value)
open Isotope.Semantics (BoundEnv InstructionModel UnitModel)
open Isotope.LetCase.LocallyNameless (Derivation)
open LambdaSSA (At)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

theorem model_pure_proof : InstructionModel.RespectsPure (ε := Bool) model := by
  intro f h
  cases f <;> cases h

private theorem ask_bind {A : Type} (req : Bool) (k : value Answer → Trace A) :
    (model.eval (.ask req) PUnit.unit >>= k).outcomes =
      ⋃ right : Bool, ⋃ b : Bool,
        prepend (.answer req right) '' (prepend (.answer req b) '' (k (answer right b)).outcomes) := by
  ext ⟨r, w⟩
  rw [Tagged.mem_bind]
  simp only [model, Tagged.outcomes_ofOutcomes, Set.mem_range, Prod.mk.injEq, Set.mem_iUnion]
  constructor
  · rintro (⟨t, _, ⟨reply, h, _⟩⟩ | ⟨a, u, v, ⟨⟨right, b⟩, ha, hw⟩, hv, rfl⟩)
    · cases h
    · cases ha
      cases hw
      refine ⟨right, b, prepend (.answer req b) (r, v), ⟨(r, v), hv, rfl⟩, ?_⟩
      simp only [prepend, replyLog, mul_assoc]
  · rintro ⟨right, b, _, ⟨⟨r', v⟩, hv, rfl⟩, h⟩
    cases h
    exact Or.inr ⟨answer right b, replyLog req right b, v, ⟨(right, b), rfl, rfl⟩, hv,
      mul_assoc _ _ _⟩

theorem bit_operand_run_proof {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) (b : Bool) :
    Kleisli.run model (bitOperand β b).2 ρ = pure (bit b) := by
  cases b <;> simp [bitOperand, bit, Kleisli.run, Derivation.denote] <;> rfl

theorem read_payload_run_proof {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β)
    (i : Fin n) (h : β.get i = Bit) (b : Bool) (hi : h ▸ ρ i = bit b) :
    Kleisli.run model (readPayload β i h).2 ρ = pure (bit b) := by
  have transport (A : Sorts) (e : β.get i = A) :
      Kleisli.run model (e ▸ (.bv : Derivation signature.Instr Γ₀ β (.bv i) (β.get i))) ρ =
        pure (e ▸ ρ i) := by
    cases e
    rfl
  exact (transport Bit h).trans (congrArg pure hi)

private theorem table_run {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) (i : Fin n)
    (h : β.get i = Bit) (b l r : Bool) (hi : h ▸ ρ i = bit b) :
    Kleisli.run model ((Expr.table l r).operand β i h).2 ρ = pure (bit (if b then r else l)) := by
  have read := read_payload_run_proof ρ i h b hi
  change Kleisli.run model (.case (readPayload β i h).2
    (bitOperand (β.snoc U) l).2 (bitOperand (β.snoc U) r).2) ρ = _
  simp only [Kleisli.run, Derivation.denote]
  unfold Kleisli.run at read
  rw [read, pure_bind]
  cases b
  · exact bit_operand_run_proof (ρ.snoc (A := U) PUnit.unit) l
  · exact bit_operand_run_proof (ρ.snoc (A := U) PUnit.unit) r

theorem position_pack_result_proof {L : List Sorts} (p : Position L) (b : Bool) :
    Exits.packAt L p.1 p.typed (bit b) = (p.result b).packed := by
  have packReturn (A : Sorts) (e : L.get p.1 = A) (x : value A) :
      Exits.packAt L p.1 (e ▸ LambdaSSA.Semantics.Categorical.labelAt_get L p.1) x =
        Exits.Exit.packed (L := L) ⟨p.1, e.symm ▸ x⟩ := by
    cases e
    rfl
  exact packReturn Bit p.2 (bit b)

theorem arm_run_at_proof {L : List Sorts} (a : ArmNormal L) (effects : List Bool)
    {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) (i : Fin n)
    (h : β.get i = Bit) (b : Bool) (hi : h ▸ ρ i = bit b)
    (finish : value (packedExitType L) → Trace (value (packedExitType L)))
    (onReturn : finish (a.result b).packed = pure (a.result b).packed) :
    (Kleisli.run model (a.render.renderPrefix effects β i h).2 ρ >>= finish).outcomes =
      (effects.foldr Reply.Normal.emit (.ret (a.result b))).outcomesWith Exits.Exit.packed := by
  induction effects generalizing n with
  | nil =>
    have ht := Exits.run_tag model ρ L _ a.position.typed _
      ((Expr.table a.whenFalse a.whenTrue).operand β i h) (table_run ρ i h b _ _ hi)
    change Kleisli.run model (a.render.renderPrefix [] β i h).2 ρ = _ at ht
    have packed := position_pack_result_proof a.position (if b then a.whenTrue else a.whenFalse)
    change _ = (a.result b).packed at packed
    rw [ht, packed, pure_bind, onReturn]
    rfl
  | cons e es ih =>
    simp only [Arm.renderPrefix, Kleisli.run, Derivation.denote, pure_bind, bind_assoc]
    change ((Reply.model.eval (.emit e) PUnit.unit >>= fun u =>
      Kleisli.run model (a.render.renderPrefix es (β.snoc U) i.succ h).2 (ρ.snoc (A := U) u) >>= finish).outcomes) = _
    rw [Reply.model_emit_bind, ih (ρ := ρ.snoc (A := U) PUnit.unit) (i := i.succ) (h := h) hi]
    rfl

set_option maxHeartbeats 600000 in
theorem request_run_proof {n : Nat} {β : BoundCtx Sorts n} {T : Sorts} {R A : Type}
    (req : Bool) (l r : Operand signature.Instr (β.snoc Bit) T)
    (ρ : BoundEnv value β) (finish : value T → Trace A) (success : R → A)
    (left right : Bool → Reply.Normal R)
    (hl : ∀ b, (Kleisli.run model l.2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes =
      (left b).outcomesWith success)
    (hr : ∀ b, (Kleisli.run model r.2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes =
      (right b).outcomesWith success) :
    (Kleisli.run model (requestOperand req false l r).2 ρ >>= finish).outcomes =
      (requestTree req left right).outcomesWith success := by
  let query : Derivation signature.Instr Γ₀ β (.op (.ask req) .unit) Answer := .op .unit
  change (Kleisli.run model (.case query l.2 r.2) ρ >>= finish).outcomes = _
  simp only [Kleisli.run, query, Derivation.denote, pure_bind, bind_assoc]
  have unitValue : (UnitModel.unitEquiv (D := value)).symm PUnit.unit = PUnit.unit := rfl
  rw [unitValue, ask_bind]
  have unionBool {B : Type} (s : Bool → Set B) : (⋃ b, s b) = s false ∪ s true := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, Bool.exists_bool]
  simp only [unionBool, answer, Bool.false_eq_true, ite_false, ite_true,
    requestTree, Reply.Normal.outcomesWith]
  let observed (branch : Operand signature.Instr (β.snoc Bit) T) (b : Bool) :=
    (Kleisli.run model branch.2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes
  let pair (tag : Bool) (branch : Operand signature.Instr (β.snoc Bit) T) :=
    prepend (.answer req tag) '' (prepend (.answer req false) '' observed branch false) ∪
      prepend (.answer req tag) '' (prepend (.answer req true) '' observed branch true)
  change pair false l ∪ pair true r = _
  simp only [pair, observed, hl, hr, Set.image_union]

set_option maxHeartbeats 600000 in
private theorem packed_normal_run (H : Sorts) (L : List Sorts) (p : Normal (H :: L)) :
    programOutcomes H L p.render = p.outcomes := by
  let T := packedExitType (H :: L)
  let ρ := boundEnv value (β := .nil) PUnit.unit
  let body := ((program H L p.render).body.render .base).encode.toLetCase.2
  let finish (x : value T) := Kleisli.run model body (ρ.snoc (A := T) x)
  change (Kleisli.run model
    (requestOperand p.request false (p.left.render.operand .nil) (p.right.render.operand .nil)).2
    ρ >>= finish).outcomes = _
  have branch (a : ArmNormal (H :: L)) (b : Bool) :
      (Kleisli.run model (a.render.operand .nil).2 (ρ.snoc (A := Bit) (bit b)) >>= finish).outcomes =
        (a.traceTree b).outcomesWith Exits.Exit.packed := by
    let x := a.result b
    have ret : finish x.packed = pure x.packed :=
      Exits.run_router model (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))
        .base ρ x.1 (LambdaSSA.Semantics.Categorical.labelAt_get (H :: L) x.1) x.2
    exact arm_run_at_proof a a.emits (ρ.snoc (A := Bit) (bit b)) 0 rfl b rfl finish ret
  exact request_run_proof _ _ _ ρ finish _ _ _ (branch p.left) (branch p.right)

theorem programOutcomes_eq_of_sat_proof (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase (equation H L p q))) :
    programOutcomes H L p = programOutcomes H L q :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation H L p q) h PUnit.unit)

theorem programOutcomes_proof (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    programOutcomes H L p = p.normal.outcomes :=
  (programOutcomes_eq_of_sat_proof H L p p.normal.render
    (Kleisli.sat_of_repaired model model_pure_proof _ (Repaired.ofNative (derive_render_proof H L p)))).trans
    (packed_normal_run H L p.normal)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
