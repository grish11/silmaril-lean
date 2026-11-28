module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Kleisli (value)
open Isotope.Semantics (BoundEnv InstructionModel)
open Isotope.LetCase.LocallyNameless (Derivation)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

local notation "U" => (Ty.unit : Sorts)
local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

theorem model_pure_proof : InstructionModel.RespectsPure (ε := Bool) model := by
  intro f h
  cases f <;> cases h

theorem model_emit_bind_proof {A : Type} (bit : Bool) (k : value U → Trace A) :
    (model.eval (.emit bit) PUnit.unit >>= k).outcomes =
      prepend (.emit bit) '' (k PUnit.unit).outcomes := by
  ext ⟨r, w⟩
  rw [Tagged.mem_bind]
  simp only [model, Tagged.outcomes_ofOutcomes, Set.mem_singleton_iff, Prod.mk.injEq,
    reduceCtorEq, false_and, and_false, exists_false, false_or]
  constructor
  · rintro ⟨a, _, v, ⟨ha, rfl⟩, hv, rfl⟩
    cases ha
    exact ⟨(r, v), hv, rfl⟩
  · rintro ⟨⟨r', v⟩, hv, h⟩
    cases h
    exact ⟨PUnit.unit, FreeMonoid.of (.emit bit), v, ⟨rfl, rfl⟩, hv, rfl⟩

private theorem ask_bind {A : Type} (req : Bool) (k : value Answer → Trace A) :
    (model.eval (.ask req) PUnit.unit >>= k).outcomes =
      prepend (.answer req false) '' (k (.inl PUnit.unit)).outcomes ∪
        prepend (.answer req true) '' (k (.inr PUnit.unit)).outcomes := by
  ext ⟨r, w⟩
  rw [Tagged.mem_bind]
  simp only [model, Tagged.outcomes_ofOutcomes, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq, reduceCtorEq, false_and, or_self, and_false, exists_false, false_or]
  constructor
  · rintro ⟨a, u, v, h, hv, rfl⟩
    rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · cases h
      exact Or.inl ⟨(r, v), hv, rfl⟩
    · cases h
      exact Or.inr ⟨(r, v), hv, rfl⟩
  · rintro (⟨⟨r', v⟩, hv, h⟩ | ⟨⟨r', v⟩, hv, h⟩)
    · cases h
      exact ⟨.inl PUnit.unit, FreeMonoid.of (.answer req false), v, Or.inl ⟨rfl, rfl⟩, hv, rfl⟩
    · cases h
      exact ⟨.inr PUnit.unit, FreeMonoid.of (.answer req true), v, Or.inr ⟨rfl, rfl⟩, hv, rfl⟩

private theorem stop_bind {A : Type} (fault : Bool) (k : value Ty.empty → Trace A) :
    (model.eval (.stop fault) PUnit.unit >>= k).outcomes = {(.error fault, 1)} := by
  ext ⟨r, w⟩
  rw [Tagged.mem_bind]
  constructor
  · rintro (⟨t, rfl, ht⟩ | ⟨a, _, _, _⟩)
    · change (Except.error t, w) = (Except.error fault, 1)
      change (Except.error t, w) = (Except.error fault, 1) at ht
      obtain ⟨h, rfl⟩ := Prod.mk.inj ht
      cases h
      rfl
    · exact a.elim
  · intro h
    change (r, w) = (Except.error fault, 1) at h
    cases h
    exact Or.inl ⟨fault, rfl, rfl⟩

theorem normal_run_with_proof {R A : Type} {B : Sorts} (ret : ReturnOperand R B)
    (finish : value B → Trace A) (success : R → A)
    (onReturn : ∀ {n : Nat} (β : BoundCtx Sorts n) (ρ : BoundEnv value β) (r : R),
      (Kleisli.run model (ret β r).2 ρ >>= finish).outcomes = {(.ok (success r), 1)})
    (p : Normal R) {n : Nat} {β : BoundCtx Sorts n} (ρ : BoundEnv value β) :
    (Kleisli.run model (p.render.operandWith ret β).2 ρ >>= finish).outcomes =
      p.outcomesWith success := by
  induction p generalizing n with
  | ret r => exact onReturn β ρ r
  | emit bit next ih =>
    simp only [Normal.render, Tree.operandWith, Kleisli.run, Derivation.denote, pure_bind, bind_assoc]
    change ((model.eval (.emit bit) PUnit.unit >>= fun u =>
      Kleisli.run model (next.render.operandWith ret (β.snoc U)).2 (ρ.snoc u) >>= finish).outcomes) = _
    rw [model_emit_bind_proof, ih]
    rfl
  | stop bit =>
    simp only [Normal.render, Tree.operandWith, Kleisli.run, Derivation.denote, pure_bind, bind_assoc]
    exact stop_bind bit _
  | ask req l r ihl ihr =>
    let query : Derivation signature.Instr Γ₀ β (.op (.ask req) .unit) Answer := .op .unit
    change (Kleisli.run model
      (.case query (l.render.operandWith ret (β.snoc U)).2 (r.render.operandWith ret (β.snoc U)).2) ρ >>= finish).outcomes = _
    simp only [Kleisli.run, query, Derivation.denote, pure_bind, bind_assoc]
    have unitValue : (Isotope.Semantics.UnitModel.unitEquiv (D := value)).symm PUnit.unit =
        PUnit.unit := rfl
    rw [unitValue, ask_bind]
    exact congrArg₂ (fun left right : Set (Outcome A) =>
      prepend (.answer req false) '' left ∪ prepend (.answer req true) '' right)
      (ihl (ρ.snoc (A := U) PUnit.unit)) (ihr (ρ.snoc (A := U) PUnit.unit))

private theorem packed_normal_run (tail : List Sorts) (p : Normal) :
    p.render.programOutcomes tail = p.outcomes (Sum.inl PUnit.unit : value (packedExitType (U :: tail))) := by
  let ρ := boundEnv value (β := .nil) PUnit.unit
  let entry := (p.render.operand .nil).2
  change (Kleisli.run model (.let₁ entry (.let₁ (.bv (ι := 0)) (.inl (.bv (ι := 0))))) ρ).outcomes = _
  simp only [Kleisli.run, Derivation.denote, pure_bind]
  refine normal_run_with_proof unitReturn (fun u => pure (Sum.inl u)) (fun _ => Sum.inl PUnit.unit) ?_ p ρ
  intro n β ρ r
  simp only [unitReturn, Kleisli.run, Derivation.denote, pure_bind]
  rfl

theorem programOutcomes_proof (tail : List Sorts) (p : Tree) :
    p.programOutcomes tail = p.normal.outcomes (Sum.inl PUnit.unit : value (packedExitType (U :: tail))) := by
  let e := equation tail p p.normal.render
  have normalized : Repaired false e :=
    .let₁ (p.normalize_operand .nil) (.equiv (.refl (.let₁ .bv (.inl .bv))))
  have sat := Kleisli.sat_of_repaired model model_pure_proof e normalized
  have eval := Kleisli.run_eq_of_sat model e sat PUnit.unit
  exact (congrArg Tagged.outcomes eval).trans (packed_normal_run tail p.normal)

theorem programOutcomes_eq_of_sat_proof (tail : List Sorts) (p q : Tree)
    (h : ((LetCase.inst Γ₀).obj signature).Sat (Kleisli.algebra model) (grammarCase (equation tail p q))) :
    p.programOutcomes tail = q.programOutcomes tail :=
  congrArg Tagged.outcomes (Kleisli.run_eq_of_sat model (equation tail p q) h PUnit.unit)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
