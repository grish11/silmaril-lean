module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)
open Silmaril.Logic.ITree.TraceInstitution (Sat)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation compileFiniteExit)
open Silmaril.Isotope.Institution.Acyclic.Captured (grammarCase readGrammar numberGrammar readGrammar_finiteExit)
open Region (packedExitType)
open Reverse (CheckedTable)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetCase (HandledTrace.Program)
open Free
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Trees

universe u v w

variable {E : Type u → Type u} {X Y : Type v} {State : Type w}

theorem replay_map_proof (step : Handler State E) (g : X → Y) (p : Trace E X) (state : State) :
    Replay step state (p.map g) ↔ Replay step state p := by
  induction p generalizing state with
  | «prefix» => exact Iff.rfl
  | request e => exact Iff.rfl
  | result value => exact Iff.rfl
  | exchange event reply tail ih => exact exists_congr fun next => and_congr_right fun _ => ih next

theorem handled_bind_pure_iff_proof (step : Handler State E) {g : X → Y} (injective : Function.Injective g)
    (state : State) (t u : Tree E X) :
    HandledTraceLE step state (t >>= fun x => pure (g x)) (u >>= fun x => pure (g x)) ↔
      HandledTraceLE step state t u := by
  constructor
  · intro packed p seen
    have shown := packed (p.map g)
      ⟨(hasTrace_bind_pure_map_iff injective t p).mpr seen.1, (replay_map_proof step g p state).mpr seen.2⟩
    exact ⟨(hasTrace_bind_pure_map_iff injective u p).mp shown.1, seen.2⟩
  · exact fun below => below.bind_left _

end Trees

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {M : HandledModel Φ}

theorem sat_refinement_iff_proof {n : Nat} {γ : Context n} {B : Ty Empty} (a b : Operand Φ γ B)
    (ρ : BoundEnv Val γ) :
    Sat M (refinement a b ρ) ↔ ∀ x, M.initial x → HandledTraceLE M.step x
      (a.2.denote Val (model Φ) (fun x => x.elim) ρ) (b.2.denote Val (model Φ) (fun x => x.elim) ρ) :=
  ⟨fun holds x start p seen => ⟨holds x start p seen, seen.2⟩,
    fun below x start p seen => (below x start p seen).1⟩

theorem sat_refinement_of_exposing_proof (exposing : Exposing M) {n : Nat} {γ : Context n} {B : Ty Empty}
    (a b : Operand Φ γ B) (ρ : BoundEnv Val γ) :
    Sat M (refinement a b ρ) ↔ TraceLE (a.2.denote Val (model Φ) (fun x => x.elim) ρ)
      (b.2.denote Val (model Φ) (fun x => x.elim) ρ) := by
  constructor
  · intro holds p seen
    obtain ⟨x, start, replay⟩ := exposing (exchanges p) (PUnit.unit : PUnit.{2})
    exact holds x start p ⟨seen, (replay_history_iff M.step p _ x).mp replay⟩
  · exact fun below x _ p seen => below p seen.1

variable {d : Nat} {β : Context d} {A B : Ty Empty} {I J : LCtx (Ty Empty)}

private theorem snoc_eta (ρ : BoundEnv Val (β.snoc A)) : ∃ (older : BoundEnv Val β) (x : Val A), ρ = older.snoc x :=
  ⟨fun i => ρ i.succ, ρ 0, funext (Fin.cases rfl (fun _ => rfl))⟩

theorem satLe_congr_proof {a a' b b' : Operand Φ (β.snoc A) B}
    (left : Equiv false Γ₀ (β.snoc A) a.1 a'.1 B) (right : Equiv false Γ₀ (β.snoc A) b.1 b'.1 B) :
    SatLe M (captured a b) ↔ SatLe M (captured a' b') := by
  have trees : ∀ ρ : BoundEnv Val (β.snoc A), refinement a b ρ = refinement a' b' ρ := fun ρ => by
    unfold refinement
    rw [denote_eq_of_equiv left a.2 a'.2 ρ, denote_eq_of_equiv right b.2 b'.2 ρ]
  exact forall_congr' fun ρ => by rw [show refinement (captured a b).2.1 (captured a b).2.2 ρ =
    refinement (captured a' b').2.1 (captured a' b').2.2 ρ from trees ρ]

theorem satLe_iff_refines_proof {State : Type} (policy : Handler State (Events Φ))
    (a b : Operand Φ (β.snoc A) B) :
    SatLe (⟨State, fun _ => True, policy⟩ : HandledModel Φ) (captured a b) ↔
      HandledTrace.Program.Refines (model Φ) policy (pack β a) (pack β b) := by
  constructor
  · intro holds w state
    obtain ⟨ρ, x, rfl⟩ := wrapValue_surjective β w
    rw [run_pack, run_pack]
    exact (handled_bind_pure_iff_proof policy (wrapValue_injective β ρ) state _ _).mpr
      ((sat_refinement_iff_proof a b (ρ.snoc x)).mp (holds (ρ.snoc x)) state trivial)
  · intro refines env
    obtain ⟨ρ, x, rfl⟩ := snoc_eta env
    refine (sat_refinement_iff_proof a b (ρ.snoc x)).mpr fun state _ => ?_
    have packed := refines (wrapValue β ρ x) state
    rw [run_pack, run_pack] at packed
    exact (handled_bind_pure_iff_proof policy (wrapValue_injective β ρ) state _ _).mp packed

theorem satLe_iff_treeRefines_proof (exposing : Exposing M) (a b : Operand Φ (β.snoc A) B) :
    SatLe M (captured a b) ↔ TreeRefines a b :=
  forall_congr' fun ρ => sat_refinement_of_exposing_proof exposing a b ρ

theorem exposing_of_exposes_proof {State : Type} {policy : Handler State (Events Φ)} (exposes : Exposes policy) :
    Exposing (⟨State, fun _ => True, policy⟩ : HandledModel Φ) :=
  fun log result => (exposes log result).imp fun _ replay => ⟨trivial, replay⟩

theorem ranked_endpoint_proof (p q : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    grammarCase (readGrammar (rankedOf p q)) = captured p.toLetCase q.toLetCase :=
  (congrArg compileFiniteExit (readGrammar_finiteExit (rankedOf p q))).trans rfl

theorem number_endpoint_proof (h : J ≠ []) (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)) :
    numberGrammar (grammarOf h a b) =
      rankedOf (CheckedTable.ofLetCase h a.2) (CheckedTable.ofLetCase h b.2) :=
  rfl

theorem sat_readback_proof (h : J ≠ []) (a b : Operand Φ (β.snoc (packedExitType I)) (packedExitType J)) :
    SatLe M (grammarCase (readGrammar (numberGrammar (grammarOf h a b)))) ↔ SatLe M (captured a b) := by
  rw [number_endpoint_proof, ranked_endpoint_proof]
  exact satLe_congr_proof (CheckedTable.ofLetCase_emit false h a.2) (CheckedTable.ofLetCase_emit false h b.2)

theorem satLe_refl_proof (a : Operand Φ (β.snoc A) B) : SatLe M (captured a a) :=
  fun _ _ _ _ seen => seen.1

theorem allReplies_exposing_proof :
    Exposing (Logic.ITree.TraceInstitution.allRepliesModel (events Φ) : HandledModel Φ) := by
  intro X log result
  refine ⟨(), trivial, ?_⟩
  induction log using FreeMonoid.inductionOn' with
  | one => trivial
  | of_mul exchange log ih => exact ⟨(), trivial, ih⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
