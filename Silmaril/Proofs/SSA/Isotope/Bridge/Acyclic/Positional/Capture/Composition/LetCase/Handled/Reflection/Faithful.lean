module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.History
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Collect

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled

open Silmaril.Elgot.ITree
open Silmaril.Semantics.NondeterministicTrace (Finite)
open Region (packedExitType)
open Reverse (operandSetoid)
open Isotope.Semantics (BoundEnv ProductModel InstructionModel)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext equiv_iff_traceArrow_eq_snoc)
open LetCase.Structural.Reply (Γ₀ run traceArrow_eq_iff_run)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.toSmall)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe u v w e s

section Packing

variable {τ : Type u} [TypeFormers τ] {D : τ → Type w} [ProductModel D]

theorem wrapValue_injective_proof : ∀ {n : Nat} (β : BoundCtx τ n) {X : τ} (ρ : BoundEnv D β),
    Function.Injective (wrapValue (X := X) β ρ)
  | _, .nil, _, _ => fun _ _ same => same
  | _, .snoc β A, X, _ => fun _ _ same =>
    (Prod.mk.inj ((ProductModel.productEquiv A X).symm.injective (wrapValue_injective_proof β _ same))).2

end Packing

namespace Free

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat} {β : Context d} {A B : Ty Empty}

local notation "small" => Structured.toSmall Atoms
local notation "⟪" d "⟫" => Derivation.denote Val (model Φ) d (fun x => Empty.elim x)

theorem history_map_proof {X Y : Type 1} (g : X → Y) (log : Log Empty Φ) (x : X) :
    (history log x).map g = history log (g x) := by
  induction log using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul exchange log ih => exact congrArg (Trace.exchange _ _) ih

theorem mem_run_iff_proof {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : Derivation Φ Γ₀ γ t A) (ρ : BoundEnv Val γ) (result : LetCase.Structural.Finite.Value A)
    (log : Log Empty Φ) :
    (result, log) ∈ (run d (lower ρ)).outcomes ↔ HasTrace (⟪d⟫ ρ) (history log ((small A).symm result)) := by
  rw [← collect_denote, mem_collect]

theorem permissive_exposes_proof : Exposes (permissive Φ) := by
  intro X log result
  refine ⟨PUnit.unit, ?_⟩
  induction log using FreeMonoid.inductionOn' with
  | one => trivial
  | of_mul exchange log ih => exact ⟨PUnit.unit, trivial, ih⟩

theorem scripted_replay_proof {X : Type 1} (log : Log Empty Φ) (result : X) :
    Replay (scripted Φ) log (history log result) := by
  induction log using FreeMonoid.inductionOn' with
  | one => trivial
  | of_mul exchange log ih => exact ⟨log, rfl, ih⟩

private theorem snoc_eta (ρ : BoundEnv Val (β.snoc A)) : ∃ (older : BoundEnv Val β) (x : Val A), ρ = older.snoc x :=
  ⟨fun i => ρ i.succ, ρ 0, funext (Fin.cases rfl (fun _ => rfl))⟩

theorem equiv_of_histories_proof (input : StructuralContext β) (a b : Operand Φ (β.snoc A) B)
    (same : ∀ (w : Val (wrap β A)) (log : Log Empty Φ) (y : Val (wrap β B)),
      HasTrace ((pack β a).run (model Φ) w) (history log y) ↔
        HasTrace ((pack β b).run (model Φ) w) (history log y)) :
    Equiv false Γ₀ (β.snoc A) a.1 b.1 B := by
  apply (equiv_iff_traceArrow_eq_snoc input a.2 b.2).mpr
  apply (traceArrow_eq_iff_run a.2 b.2).mpr
  intro σ
  obtain ⟨ρ, x, env⟩ := snoc_eta (raise σ)
  have trees : ∀ (log : Log Empty Φ) (y : Val B),
      HasTrace (⟪a.2⟫ (ρ.snoc x)) (history log y) ↔ HasTrace (⟪b.2⟫ (ρ.snoc x)) (history log y) := by
    intro log y
    have packed := same (wrapValue β ρ x) log (wrapValue β ρ y)
    rw [run_pack, run_pack, ← history_map_proof,
      hasTrace_bind_pure_map_iff (wrapValue_injective_proof β ρ),
      hasTrace_bind_pure_map_iff (wrapValue_injective_proof β ρ)] at packed
    exact packed
  have collected : collect (small B) (⟪a.2⟫ (ρ.snoc x)) = collect (small B) (⟪b.2⟫ (ρ.snoc x)) :=
    Finite.outcomes_injective (Set.ext fun p => (mem_collect _ _ p.1 p.2).trans ((trees p.2 _).trans (mem_collect _ _ p.1 p.2).symm))
  rw [collect_denote, collect_denote, ← env, lower_raise] at collected
  exact collected

theorem run_pack_eq_of_equiv_proof {a b : Operand Φ (β.snoc A) B}
    (h : Equiv false Γ₀ (β.snoc A) a.1 b.1 B) (w : Val (wrap β A)) :
    (pack β a).run (model Φ) w = (pack β b).run (model Φ) w := by
  obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective β w
  rw [run_pack, run_pack]
  exact congrArg (· >>= _) (denote_eq_of_equiv h a.2 b.2 _)

variable {State : Type s} {I J : LCtx (Ty Empty)}

theorem equiv_of_refines_proof (input : StructuralContext β) (policy : Handler State (Events Φ))
    (exposes : Exposes policy) (a b : Operand Φ (β.snoc A) B)
    (forward : HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b))
    (backward : HandledTrace.Program.Refines (model Φ) policy (pack β b) (pack β a)) :
    Equiv false Γ₀ (β.snoc A) a.1 b.1 B := by
  refine equiv_of_histories_proof input a b fun w log y => ⟨fun seen => ?_, fun seen => ?_⟩
  · obtain ⟨state, replay⟩ := exposes log y
    exact (forward w state _ ⟨seen, replay⟩).1
  · obtain ⟨state, replay⟩ := exposes log y
    exact (backward w state _ ⟨seen, replay⟩).1

end Free

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled
