module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Capture.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

/-! The same seed and machine state repeat with a new payload and state.
Only the original capture determines whether that repeat reaches UB. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)

namespace LambdaSSAUBCapturedIterationRegression

private abbrev U : Ty Empty := .unit
private abbrev Flag : Ty Empty := .coprod U U
private abbrev S : Ty Empty := .coprod U Flag
private abbrev routes : List (Ty Empty) := [S, U]

local instance : HasTy Unit (Ty Empty) := ⟨fun _ => U, fun _ => U⟩

private abbrev raw {n : Nat} (bound : Fin n → Value Unit) : Institution.Observational.Model Unit n where
  α := Unit
  σ := Nat
  instr := fun _ _ s b t => b = .unit ∧ t = s + 1
  faults := fun _ _ _ _ => False
  prim := fun _ _ _ => False
  bound := bound

private abbrev fixture : Shape.Model Unit ([] : List (Ty Empty)) where
  raw := raw Fin.elim0
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by rintro _ _ _ _ _ _ ⟨rfl, _⟩; exact .unit

private abbrev left : singlePayload (atomType := fixture.atomType) Flag := ⟨.inl .unit, .inl .unit⟩
private abbrev right : singlePayload (atomType := fixture.atomType) Flag := ⟨.inr .unit, .inr .unit⟩
private abbrev flagModel (c : singlePayload (atomType := fixture.atomType) Flag) :=
  fixture.extend c.property

private abbrev selector : LambdaSSA.UB.Typed (Φ := Unit) [Flag, Flag] routes :=
  ⟨.let₁ (.op () .unit)
      (.case (.var 1) (.br 0 (.inr (.inr .unit)))
        (.case (.var 3) (.br 1 .unit) (.br 0 (.inl .unit)))),
    .let₁ (.op (f := ()) .unit)
      (.case (A := U) (B := U) (.var (i := 1) rfl)
        (.br (ℓ := 0) rfl (.inr (.inr .unit)))
        (.case (A := U) (B := U) (.var (i := 3) rfl)
          (.br (ℓ := 1) rfl .unit) (.br (ℓ := 0) rfl (.inl .unit))))⟩

private abbrev pass : LambdaSSA.UB.Typed (Φ := Unit) [S, Flag, Flag] [S] :=
  ⟨.br 0 (.var 0), .br (ℓ := 0) rfl (.var (i := 0) rfl)⟩

private def route (i : Fin routes.length) : Region Unit (routes.get i :: [Flag, Flag]) [S] :=
  Fin.cases (motive := fun j => Region Unit (routes.get j :: [Flag, Flag]) [S])
    (.native pass) (fun _ => .ub) i

private abbrev step : Region Unit [Flag, Flag] [S] := .lsubst (.native selector) route

private noncomputable abbrev observed (c : singlePayload (atomType := fixture.atomType) Flag) :=
  interpretSingleton (flagModel c) step

private noncomputable abbrev loop := iterateCaptured fixture step

private theorem native_exact {Γ L : List (Ty Empty)} (r : LambdaSSA.UB.Typed (Φ := Unit) Γ L)
    (bound : Fin Γ.length → Value Unit) (s : Nat) (i : Fin L.length) (b : Value Unit) (t : Nat)
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

private abbrev captured (c a : singlePayload (atomType := fixture.atomType) Flag) :=
  ((flagModel c).extend a.property).raw

private theorem observation_of_selection (c a : singlePayload (atomType := fixture.atomType) Flag)
    (s : Nat) (i : Fin routes.length) (b : Value Unit)
    (run : Region.Eval (captured c a).instr (envOfBound (captured c a).bound) selector.val s i b (s + 1)) :
    (observed c).run 0 a s = denote (route i) (extendModel (captured c a) b) (s + 1) := by
  change Behaviour.bind (WithTop.some (nativeOutcomes selector (captured c a) s))
    (fun j b t => denote (route j) (extendModel (captured c a) b) t) = _
  rw [native_exact selector (captured c a).bound s i b (s + 1) run]
  exact return_bind i b (s + 1) _

private theorem pass_outcomes (c a : singlePayload (atomType := fixture.atomType) Flag)
    (b : Value Unit) (s : Nat) :
    denote (.native pass) (extendModel (captured c a) b) s = returnPayload b s :=
  congrArg WithTop.some (native_exact pass (extendModel (captured c a) b).bound s 0 b s (.br .var))

private theorem first_view (c : singlePayload (atomType := fixture.atomType) Flag) (s : Nat) :
    (observed c).run 0 left s = returnPayload (.inr right.val) (s + 1) :=
  (observation_of_selection c left s 0 _ (.let₁ (.op .unit ⟨rfl, rfl⟩) (.case_inl .var (.br (.inr (.inr .unit)))))).trans
    (pass_outcomes c left _ _)

private theorem poisoned_view (s : Nat) : (observed left).run 0 right s = ⊤ :=
  observation_of_selection left right s 1 _ (.let₁ (.op .unit ⟨rfl, rfl⟩) (.case_inr .var (.case_inl .var (.br .unit))))

private theorem safe_view (s : Nat) : (observed right).run 0 right s = returnPayload (.inl .unit) (s + 1) :=
  (observation_of_selection right right s 0 _
    (.let₁ (.op .unit ⟨rfl, rfl⟩) (.case_inr .var (.case_inr .var (.br (.inl .unit)))))).trans
      (pass_outcomes right right _ _)

private theorem first_repeat (c : singlePayload (atomType := fixture.atomType) Flag) :
    Repeat (observed c) (left, 0) (right, 1) := by
  change ((observed c).run 0 left 0).Ordinary (.ret 0 (.inr right.val) 1)
  rw [first_view]
  exact ⟨WithTop.coe_ne_top, rfl⟩

private theorem ub_with_left_capture : loop.run 0 (pairPayload left left) 0 = ⊤ :=
  (iterateCaptured_eq_top_iff fixture step left left 0).mpr
    ⟨(right, 1), .single (first_repeat left), poisoned_view 1⟩

private theorem safe_with_right_capture : loop.run 0 (pairPayload right left) 0 ≠ ⊤ := by
  intro top
  obtain ⟨p, path, reached⟩ := (iterateCaptured_eq_top_iff fixture step right left 0).mp top
  change (observed right).run 0 p.1 p.2 = ⊤ at reached
  rcases path.cases_head with rfl | ⟨q, first, rest⟩
  · exact WithTop.coe_ne_top ((first_view _ _).symm.trans reached)
  · change ((observed right).run 0 left 0).Ordinary (.ret 0 (.inr q.1.val) q.2) at first
    rw [first_view] at first
    obtain ⟨_, value, state⟩ := Outcome.ret.inj (Set.mem_singleton_iff.mp first.2)
    have same : q = (right, 1) := Prod.ext (Subtype.ext (Value.inr.inj value)) state
    subst q
    have noRepeat (q) : ¬ Repeat (observed right) (right, 1) q := by
      intro h
      change ((observed right).run 0 right 1).Ordinary (.ret 0 (.inr q.1.val) q.2) at h
      rw [safe_view] at h
      cases (Outcome.ret.inj (Set.mem_singleton_iff.mp h.2)).2.1
    obtain rfl := (Relation.reflTransGen_iff_eq noRepeat).mp rest
    exact WithTop.coe_ne_top ((safe_view 1).symm.trans reached)

private theorem return_with_right_capture : (loop.run 0 (pairPayload right left) 0).Ordinary (.ret 0 .unit 2) := by
  let graph := iterationGraph (observed right) left
  have safe : ¬ Feedback.ReachesUB graph (.entry 0) :=
    fun ub => safe_with_right_capture (Feedback.close_eq_top_iff.mpr ub)
  have first : Feedback.Step graph (.entry 0) (.block 0 left.val 0) :=
    .branch ⟨WithTop.coe_ne_top, rfl⟩
  have back : Feedback.Step graph (.block 0 left.val 0) (.block 0 right.val 1) :=
    .branch ((iterationGraph_block_ordinary (observed right) left left 0 _).mpr (first_repeat right))
  have finish : (graph (.block 0 right.val 1)).Ordinary (.ret (1 : Fin 2) .unit 2) := by
    apply (iterationGraph_block_ordinary (observed right) left right 1 _).mpr
    rw [safe_view]
    exact ⟨WithTop.coe_ne_top, rfl⟩
  exact Feedback.ordinary_close_iff.mpr
    ⟨safe, .inl ⟨.block 0 right.val 1, (Relation.ReflTransGen.single first).tail back, finish⟩⟩

#print axioms iterateCaptured_eq_top_iff
#print axioms iterateCaptured_mono
#print axioms interpretCfgEta_iterateSum
#print axioms interpret_guarded_feedback
#print axioms singleton_map_unpacked_iterateRegion
#print axioms ub_with_left_capture
#print axioms return_with_right_capture

end LambdaSSAUBCapturedIterationRegression
