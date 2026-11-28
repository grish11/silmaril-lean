module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Total

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free

open Silmaril.Elgot.ITree
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀ run traceArrow_eq_iff_run traceArrow_of_valid valid_of_equiv)
open LetCase (HandledTrace.Program)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.toSmall)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

universe s

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {State : Type s} {X Y : Type 1}

local notation "small" => Structured.toSmall Atoms

/-! Replay reads only the completed exchanges of an observation. -/

theorem replay_history_iff_proof (policy : Handler State (Events Φ)) (p : Trace (Events Φ) X) (y : Y)
    (state : State) : Replay policy state (history (exchanges p) y) ↔ Replay policy state p := by
  induction p generalizing state with
  | «prefix» => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | request e => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | result value => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | exchange event reply tail ih =>
    cases event with
    | call f argument => exact exists_congr fun next => and_congr_right fun _ => ih next

theorem replay_of_exposes_proof {policy : Handler State (Events Φ)} (exposes : Exposes policy)
    (p : Trace (Events Φ) X) : ∃ state, Replay policy state p := by
  obtain ⟨state, replay⟩ := exposes (exchanges p) (PUnit.unit : PUnit.{2})
  exact ⟨state, (replay_history_iff_proof policy p _ state).mp replay⟩

theorem handled_iff_traceLE_proof {policy : Handler State (Events Φ)} (exposes : Exposes policy)
    (t u : Tree (Events Φ) X) : (∀ state, HandledTraceLE policy state t u) ↔ TraceLE t u :=
  ⟨fun handled p seen => by
    obtain ⟨state, replay⟩ := replay_of_exposes_proof exposes p
    exact (handled state p ⟨seen, replay⟩).1,
    fun below _ p seen => ⟨below p seen.1, seen.2⟩⟩

/-! Total trees with inhabited replies are determined by complete histories. -/

theorem exists_history_proof {t : Tree (Events Φ) X} (total : Total t) :
    ∃ (log : Log Empty Φ) (y : X), HasTrace t (history log y) := by
  induction total with
  | ret x => exact ⟨1, x, (hasTrace_ret_history x x 1).mpr ⟨rfl, rfl⟩⟩
  | vis e k _ ih =>
    cases e with
    | call f argument =>
      obtain ⟨log, y, seen⟩ := ih (LetCase.Structural.Finite.Signature.target f).witness.value
      exact ⟨_, y, (hasTrace_vis_history f argument k _ y).mpr ⟨_, log, rfl, seen⟩⟩

theorem eq_of_total_histories_proof {t u : Tree (Events Φ) X} (total : Total t)
    (below : ∀ (log : Log Empty Φ) (y : X), HasTrace t (history log y) → HasTrace u (history log y)) :
    t = u := by
  induction total generalizing u with
  | ret x =>
    have returned : out u = Part.some (.ret x) := below 1 x ((hasTrace_ret_history x x 1).mpr ⟨rfl, rfl⟩)
    exact (out_injective (returned.trans (out_ret x).symm)).symm
  | vis e k totals ih =>
    cases e with
    | call f argument =>
      obtain ⟨log, y, seen⟩ := exists_history_proof (totals (LetCase.Structural.Finite.Signature.target f).witness.value)
      obtain ⟨l, root, -⟩ := below _ y ((hasTrace_vis_history f argument k _ y).mpr ⟨_, log, rfl, seen⟩)
      have shape : u = vis (.call f argument) l := out_injective (root.trans (out_vis _ _).symm)
      subst shape
      exact congrArg (vis _) (funext fun reply => ih reply fun log y seen => by
        have shown := below _ y ((hasTrace_vis_history f argument k _ y).mpr ⟨reply, log, rfl, seen⟩)
        rwa [history_cons, hasTrace_vis_exchange_iff] at shown)

/-! The relations on captured operands. -/

variable {d : Nat} {β : Context d} {A B : Ty Empty}

private theorem snoc_eta (ρ : BoundEnv Val (β.snoc A)) : ∃ (older : BoundEnv Val β) (x : Val A), ρ = older.snoc x :=
  ⟨fun i => ρ i.succ, ρ 0, funext (Fin.cases rfl (fun _ => rfl))⟩

theorem refines_of_treeRefines_proof (policy : Handler State (Events Φ)) {a b : Operand Φ (β.snoc A) B}
    (tree : TreeRefines a b) : HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b) := by
  intro w state
  obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective β w
  rw [run_pack, run_pack]
  exact fun p seen => ⟨(tree (ρ.snoc x)).bind_pure _ p seen.1, seen.2⟩

theorem treeRefines_of_refines_proof {policy : Handler State (Events Φ)} (exposes : Exposes policy)
    {a b : Operand Φ (β.snoc A) B}
    (refines : HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b)) : TreeRefines a b := by
  intro env
  obtain ⟨ρ, x, rfl⟩ := snoc_eta env
  have packed := (handled_iff_traceLE_proof exposes _ _).mp (refines (wrapValue β ρ x))
  rw [run_pack, run_pack] at packed
  exact (TraceLE.bind_pure_iff (wrapValue_injective β ρ)).mp packed

theorem treeRefines_of_equiv_proof {a b : Operand Φ (β.snoc A) B}
    (h : Equiv false Γ₀ (β.snoc A) a.1 b.1 B) : TreeRefines a b :=
  fun ρ => denote_eq_of_equiv h a.2 b.2 ρ ▸ fun _ seen => seen

theorem treeRefines_congr_proof {a a' b b' : Operand Φ (β.snoc A) B}
    (left : Equiv false Γ₀ (β.snoc A) a.1 a'.1 B) (right : Equiv false Γ₀ (β.snoc A) b.1 b'.1 B) :
    TreeRefines a b ↔ TreeRefines a' b' := by
  constructor <;> intro tree ρ
  · rw [← denote_eq_of_equiv left a.2 a'.2 ρ, ← denote_eq_of_equiv right b.2 b'.2 ρ]
    exact tree ρ
  · rw [denote_eq_of_equiv left a.2 a'.2 ρ, denote_eq_of_equiv right b.2 b'.2 ρ]
    exact tree ρ

theorem equiv_of_treeRefines_proof (input : StructuralContext β) {a b : Operand Φ (β.snoc A) B}
    (tree : TreeRefines a b) : Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  (equiv_iff_run_pack_eq input a b).mpr fun w => by
    obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective β w
    rw [run_pack, run_pack, eq_of_total_traceLE_proof (total_denote_proof a.2 _) (tree (ρ.snoc x))]

theorem outcomeRefines_of_equiv_proof {a b : Operand Φ (β.snoc A) B}
    (h : Equiv false Γ₀ (β.snoc A) a.1 b.1 B) : OutcomeRefines a b :=
  fun ρ => (traceArrow_eq_iff_run a.2 b.2).mp (traceArrow_of_valid (valid_of_equiv a.2 b.2 h)) ρ ▸ subset_rfl

theorem equiv_of_outcomeRefines_proof (input : StructuralContext β) {a b : Operand Φ (β.snoc A) B}
    (outcomes : OutcomeRefines a b) : Equiv false Γ₀ (β.snoc A) a.1 b.1 B :=
  (equiv_iff_run_pack_eq input a b).mpr fun w => by
    obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective β w
    rw [run_pack, run_pack, eq_of_total_histories_proof (total_denote_proof a.2 (ρ.snoc x)) fun log y seen => ?_]
    have source := (mem_run_iff a.2 (ρ.snoc x) (small B y) log).mpr (by rwa [Equiv.symm_apply_apply])
    have target := (mem_run_iff b.2 (ρ.snoc x) (small B y) log).mp (outcomes _ source)
    rwa [Equiv.symm_apply_apply] at target

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free
