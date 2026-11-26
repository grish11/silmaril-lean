module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

/-! The first invocation can return normally or repeat at a new state. The
repeat reaches a literal overlay UB continuation. A separate initial state
never reaches that continuation and keeps exactly its ordinary return. -/

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)

namespace LambdaSSAUBOverlayIterationRegression

private inductive Phase where
  | start | poison | safe

private abbrev U : Ty Empty := .unit
private abbrev S : Ty Empty := .coprod U U
private abbrev routes : List (Ty Empty) := [S, U]

local instance : HasTy Unit (Ty Empty) := ⟨fun _ => U, fun _ => .coprod S U⟩

private def reply : Phase → Value Unit
  | .start => .inl (.inr .unit)
  | .poison => .inr .unit
  | .safe => .inl (.inl .unit)

private def nextState : Phase → Phase
  | .start => .poison
  | phase => phase

private abbrev raw {n : Nat} (bound : Fin n → Value Unit) : Institution.Observational.Model Unit n where
  α := Unit
  σ := Phase
  instr := fun _ _ s b t => b = reply s ∧ t = nextState s
  faults := fun _ _ _ _ => False
  prim := fun _ _ _ => False
  bound := bound

private abbrev fixture : Shape.Model Unit ([] : List (Ty Empty)) where
  raw := raw Fin.elim0
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    rintro _ _ s _ _ _ ⟨rfl, _⟩
    cases s
    · exact .inl (.inr .unit)
    · exact .inr .unit
    · exact .inl (.inl .unit)

private abbrev input : singlePayload (atomType := fixture.atomType) U := ⟨.unit, .unit⟩

private abbrev selector : LambdaSSA.UB.Typed (Φ := Unit) [U] routes :=
  ⟨.let₁ (.op () (.var 0)) (.case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))),
    .let₁ (.op (f := ()) (.var (i := 0) rfl))
      (.case (A := S) (B := U) (.var (i := 0) rfl)
        (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (.br (ℓ := 1) rfl (.var (i := 0) rfl)))⟩

private abbrev pass : LambdaSSA.UB.Typed (Φ := Unit) [S, U] [S] :=
  ⟨.br 0 (.var 0), .br (ℓ := 0) rfl (.var (i := 0) rfl)⟩

private def route (fallback : Region Unit [U, U] [S]) (i : Fin routes.length) :
    Region Unit (routes.get i :: [U]) [S] :=
  Fin.cases (motive := fun j => Region Unit (routes.get j :: [U]) [S]) (.native pass)
    (fun j => by obtain rfl := Fin.eq_zero j; exact fallback) i

private abbrev step (fallback : Region Unit [U, U] [S]) : Region Unit [U] [S] :=
  .lsubst (.native selector) (route fallback)

private abbrev ordinaryFallback : Region Unit [U, U] [S] :=
  .native ⟨.br 0 (.inl .unit), .br (ℓ := 0) rfl (.inl .unit)⟩

private noncomputable abbrev observed (fallback : Region Unit [U, U] [S]) :=
  interpretSingleton fixture (step fallback)

private noncomputable abbrev loop (fallback : Region Unit [U, U] [S]) :=
  iterateOverlay fixture (step fallback)

private def chosenExit (s : Phase) : Fin 2 := match s with | .poison => 1 | _ => 0

private def chosenPayload (s : Phase) : Value Unit :=
  match s with | .start => .inr .unit | .poison => .unit | .safe => .inl .unit

private theorem native_exact {Γ L : List (Ty Empty)} (r : LambdaSSA.UB.Typed (Φ := Unit) Γ L)
    (bound : Fin Γ.length → Value Unit) (s : Phase) (i : Fin L.length) (b : Value Unit) (t : Phase)
    (run : Region.Eval (raw bound).instr (envOfBound bound) r.val s i b t) :
    nativeOutcomes r (raw bound) s = {Outcome.ret i b t} := by
  have deterministic : InstrDeterministic (raw bound).instr := by
    intro _ _ _ _ _ _ _ first second
    exact ⟨first.1.trans second.1.symm, first.2.trans second.2.symm⟩
  apply Set.ext
  intro o
  rw [mem_nativeOutcomes_iff r (M := raw bound) (envOfBound_agrees bound), Set.mem_singleton_iff]
  cases o with
  | ret j c u =>
    constructor
    · intro seen
      obtain ⟨label, value, final⟩ := seen.deterministic deterministic run
      exact Outcome.ret.injEq .. |>.mpr ⟨Fin.ext label, value, final⟩
    · intro eq
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj eq
      exact run
  | fault =>
    exact ⟨fun h => h.false.elim, fun h => by cases h⟩
  | diverge =>
    exact ⟨fun h => (run.not_diverges deterministic (External.Diverges.false_iff.mp h)).elim,
      fun h => by cases h⟩

private abbrev captured := (fixture.extend (A := U) .unit).raw

private theorem chosen (s : Phase) :
    Region.Eval captured.instr (envOfBound captured.bound) selector.val s
      (chosenExit s).val (chosenPayload s) (nextState s) := by
  cases s
  · exact .let₁ (.op .var ⟨rfl, rfl⟩) (.case_inl .var (.br .var))
  · exact .let₁ (.op .var ⟨rfl, rfl⟩) (.case_inr .var (.br .var))
  · exact .let₁ (.op .var ⟨rfl, rfl⟩) (.case_inl .var (.br .var))

private theorem at_step (fallback : Region Unit [U, U] [S]) (s : Phase) :
    (observed fallback).run 0 input s =
      denote (route fallback (chosenExit s)) (extendModel captured (chosenPayload s)) (nextState s) := by
  change Behaviour.bind (WithTop.some (nativeOutcomes selector captured s))
    (fun i b t => denote (route fallback i) (extendModel captured b) t) = _
  rw [native_exact selector captured.bound s (chosenExit s) (chosenPayload s) (nextState s) (chosen s)]
  exact return_bind (chosenExit s) (chosenPayload s) (nextState s) _

private theorem pass_outcomes (b : Value Unit) (s : Phase) :
    denote (.native pass) (extendModel captured b) s =
      WithTop.some {Outcome.ret (0 : Fin 1) b s} :=
  congrArg WithTop.some (native_exact pass (extendModel captured b).bound s 0 b s (.br .var))

private theorem at_start (fallback : Region Unit [U, U] [S]) :
    (observed fallback).run 0 input .start =
      WithTop.some {Outcome.ret (0 : Fin 1) (.inr .unit) .poison} :=
  (at_step fallback .start).trans (pass_outcomes (.inr .unit) .poison)

private theorem at_safe (fallback : Region Unit [U, U] [S]) :
    (observed fallback).run 0 input .safe =
      WithTop.some {Outcome.ret (0 : Fin 1) (.inl .unit) .safe} :=
  (at_step fallback .safe).trans (pass_outcomes (.inl .unit) .safe)

private theorem at_poison : (observed .ub).run 0 input .poison = ⊤ :=
  at_step .ub .poison

private theorem reached_ub_after_repeat : (loop .ub).run 0 input .start = ⊤ := by
  apply (iterateOverlay_eq_top_iff fixture (step .ub) input .start).mpr
  refine ⟨(input, .poison), .single ?_, at_poison⟩
  change ((observed .ub).run 0 input .start).Ordinary (.ret 0 (.inr .unit) .poison)
  rw [at_start]
  exact ⟨WithTop.coe_ne_top, rfl⟩

private theorem safe_start_exact (fallback : Region Unit [U, U] [S]) :
    (loop fallback).run 0 input .safe = WithTop.some {Outcome.ret (0 : Fin 1) .unit .safe} := by
  have noRepeat (p) : ¬ Repeat (observed fallback) (input, .safe) p := by
    intro h
    change ((observed fallback).run 0 input .safe).Ordinary (.ret 0 (.inr p.1.val) p.2) at h
    rw [at_safe] at h
    have eq := (Outcome.ret.inj (Set.mem_singleton_iff.mp h.2)).2.1
    cases eq
  refine (iterateSum_no_repeat (observed fallback) input .safe noRepeat (at_safe fallback)).trans ?_
  apply congrArg WithTop.some
  ext o
  cases o with
  | ret i b s =>
    have hi := Fin.eq_zero i
    subst i
    simp [tagIterationOutcome, Feedback.external]
  | fault | diverge => simp [tagIterationOutcome, Feedback.external]

private theorem overlay_iteration_widens :
    (loop ordinaryFallback).run 0 input .start ≤ (loop .ub).run 0 input .start := by
  apply iterateOverlay_mono fixture ?_ input .start
  refine lsubst_mono (fun _ _ => le_rfl) ?_
  intro i
  by_cases first : i.val = 0
  · have hi : i = 0 := Fin.ext first
    subst i
    exact fun _ _ => le_rfl
  · have bound : i.val < 2 := i.isLt
    have hi : i = 1 := Fin.ext (show i.val = 1 by omega)
    subst i
    exact refines_ub ordinaryFallback

#print axioms iterateOverlay_eq_top_iff
#print axioms iterateOverlay_mono
#print axioms reached_ub_after_repeat
#print axioms safe_start_exact
#print axioms overlay_iteration_widens

end LambdaSSAUBOverlayIterationRegression
