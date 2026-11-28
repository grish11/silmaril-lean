module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour
import Mathlib.Tactic.FinCases

/-! Both executable tables are certified against actual overlay regions.
One changing repeat reaches the replaced continuation. Another enters
a two-state cycle. Finite fault, finite return and in-step divergence
also occur at separate supported starts. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)

namespace LambdaSSAUBFiniteIterationRegression

private abbrev U : Ty Empty := .unit
private abbrev S : Ty Empty := .coprod U U
private abbrev routes : List (Ty Empty) := [S, U]
private abbrev State := Fin 7

local instance : HasTy Unit (Ty Empty) := ⟨fun _ => U, fun _ => .coprod S U⟩

private def reply (s : State) : Value Unit :=
  if s = 1 then .inr .unit else if s = 6 then .inl (.inl .unit) else .inl (.inr .unit)

private def nextState (s : State) : State :=
  match s.val with
  | 0 => 1
  | 2 => 3
  | 3 => 2
  | _ => s

private abbrev raw {n : Nat} (bound : Fin n → Value Unit) : Institution.Observational.Model Unit n where
  α := Unit
  σ := State
  instr := fun _ _ s b t => s ≠ 4 ∧ s ≠ 5 ∧ b = reply s ∧ t = nextState s
  faults := fun _ _ s t => s = 4 ∧ t = 4
  prim := fun _ _ s => s = 5
  bound := bound

private abbrev fixture : Shape.Model Unit ([] : List (Ty Empty)) where
  raw := raw Fin.elim0
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    rintro _ _ s _ _ _ ⟨_, _, rfl, _⟩
    unfold reply
    split
    · exact .inr .unit
    · split
      · exact .inl (.inl .unit)
      · exact .inl (.inr .unit)

private abbrev unitPayload : singlePayload (atomType := fixture.atomType) U := ⟨.unit, .unit⟩

private abbrev carrier : Carrier fixture U U U 1 7 1 7 where
  capture _ := unitPayload
  invocation s := (unitPayload, s)
  result := ⟨fun _ => unitPayload, fun _ _ _ => Subsingleton.elim _ _⟩
  final := Function.Embedding.refl State

private abbrev selector : LambdaSSA.UB.Typed (Φ := Unit) [U, U] routes :=
  ⟨.let₁ (.op () (.var 0)) (.case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))),
    .let₁ (.op (f := ()) (.var (i := 0) rfl))
      (.case (A := S) (B := U) (.var (i := 0) rfl)
        (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (.br (ℓ := 1) rfl (.var (i := 0) rfl)))⟩

private abbrev pass : LambdaSSA.UB.Typed (Φ := Unit) [S, U, U] [S] :=
  ⟨.br 0 (.var 0), .br (ℓ := 0) rfl (.var (i := 0) rfl)⟩

private abbrev fallback : LambdaSSA.UB.Typed (Φ := Unit) [U, U, U] [S] :=
  ⟨.br 0 (.inl .unit), .br (ℓ := 0) rfl (.inl .unit)⟩

private def route (allowUB : Bool) (i : Fin routes.length) : Region Unit (routes.get i :: [U, U]) [S] :=
  Fin.cases (motive := fun j => Region Unit (routes.get j :: [U, U]) [S]) (.native pass)
    (fun j => by
      obtain rfl := Fin.eq_zero j
      exact if allowUB then .ub else .native fallback) i

private abbrev region (allowUB : Bool) : Region Unit [U, U] [S] :=
  .lsubst (.native selector) (route allowUB)

private def table (allowUB : Bool) : Table 1 7 1 7 := fun _ s =>
  match s.val with
  | 0 => .repeat 1
  | 1 => .stop (if allowUB then .ub else .ret 0 1)
  | 2 => .repeat 3
  | 3 => .repeat 2
  | 4 => .stop (.fault 4)
  | 5 => .stop .diverge
  | _ => .stop (.ret 0 6)

private abbrev captured := ((fixture.extend (A := U) .unit).extend (A := U) .unit).raw

private theorem selector_no_run_of (s : State) (blocked : s = 4 ∨ s = 5)
    {i : Nat} {b : Value Unit} {t : State} :
    ¬ Region.Eval captured.instr (envOfBound captured.bound) selector.val s i b t := by
  intro run
  cases run with
  | let₁ head _ =>
    cases head with
    | op arg primitive =>
      cases arg
      exact blocked.elim primitive.1 primitive.2.1

private theorem selector_fault (s t : State) :
    Region.Fault captured.instr captured.faults (envOfBound captured.bound) selector.val s t ↔
      s = 4 ∧ t = 4 := by
  constructor
  · intro run
    cases run with
    | let₁_arg arg =>
      cases arg with
      | op_fault arg fault => cases arg; exact fault
      | op_arg arg => cases arg
    | let₁_body _ rest =>
      cases rest with
      | case_arg arg => cases arg
      | case_inl _ br | case_inr _ br =>
        cases br with | br arg => cases arg
  · intro fault
    exact .let₁_arg (.op_fault .var fault)

private theorem br_var_no_div {env : Env Unit} {s : State} {i : Nat} :
    ¬ External.Diverges captured.instr captured.prim (.region env (.br i (.var 0)) s) := by
  intro h
  cases h.unfold with
  | br arg => cases arg
  | core step => cases step

private theorem selector_diverges (s : State) :
    External.Diverges captured.instr captured.prim (.region (envOfBound captured.bound) selector.val s) ↔ s = 5 := by
  constructor
  · intro h
    cases h.unfold with
    | let₁_arg arg =>
      cases arg with
      | op_arg arg => cases arg
      | primitive arg active => cases arg; exact active
    | core step =>
      cases step with
      | let₁ _ h =>
        cases h.unfold with
        | case_arg arg => cases arg
        | core step =>
          cases step with
          | case_inl _ tail | case_inr _ tail => exact (br_var_no_div tail).elim
  · intro active
    exact .fold (.let₁_arg (.primitive .var active))

private theorem exact_return {Γ L : List (Ty Empty)} (r : LambdaSSA.UB.Typed (Φ := Unit) Γ L)
    (bound : Fin Γ.length → Value Unit) (s : State) (i : Fin L.length) (b : Value Unit) (t : State)
    (run : Region.Eval (raw bound).instr (envOfBound bound) r.val s i b t)
    (safe : ∀ t, ¬ Region.Fault (raw bound).instr (raw bound).faults (envOfBound bound) r.val s t)
    (ends : ¬ External.Diverges (raw bound).instr (raw bound).prim (.region (envOfBound bound) r.val s)) :
    nativeOutcomes r (raw bound) s = {Outcome.ret i b t} := by
  have deterministic : InstrDeterministic (raw bound).instr := by
    intro _ _ _ _ _ _ _ first second
    exact ⟨first.2.2.1.trans second.2.2.1.symm, first.2.2.2.trans second.2.2.2.symm⟩
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
  | fault t => exact ⟨fun h => (safe t h).elim, fun h => by cases h⟩
  | diverge => exact ⟨fun h => (ends h).elim, fun h => by cases h⟩

private theorem selector_exact (s t : State) (i : Fin routes.length) (b : Value Unit)
    (run : Region.Eval captured.instr (envOfBound captured.bound) selector.val s i b t)
    (hf : s ≠ 4) (hd : s ≠ 5) :
    nativeOutcomes selector captured s = {Outcome.ret i b t} :=
  exact_return selector captured.bound s i b t run
    (fun t fault => hf ((selector_fault s t).mp fault).1)
    (fun div => hd ((selector_diverges s).mp div))

private theorem selector_at_fault : nativeOutcomes selector captured 4 = {Outcome.fault 4} := by
  ext o
  rw [mem_nativeOutcomes_iff _ (envOfBound_agrees captured.bound), Set.mem_singleton_iff]
  cases o with
  | ret => exact ⟨fun h => (selector_no_run_of 4 (.inl rfl) h).elim, fun h => by cases h⟩
  | fault t => simpa using selector_fault 4 t
  | diverge => simpa using selector_diverges 4

private theorem selector_at_diverge : nativeOutcomes selector captured 5 = {Outcome.diverge} := by
  ext o
  rw [mem_nativeOutcomes_iff _ (envOfBound_agrees captured.bound), Set.mem_singleton_iff]
  cases o with
  | ret => exact ⟨fun h => (selector_no_run_of 5 (.inr rfl) h).elim, fun h => by cases h⟩
  | fault t => simpa using selector_fault 5 t
  | diverge => simpa using selector_diverges 5

private theorem pass_exact (b : Value Unit) (s : State) :
    denote (.native pass) (extendModel captured b) s = returnPayload b s :=
  congrArg WithTop.some (exact_return pass (extendModel captured b).bound s 0 b s (.br .var)
    (by intro _ fault; cases fault with | br arg => cases arg) br_var_no_div)

private theorem fallback_exact (s : State) :
    denote (.native fallback) (extendModel captured .unit) s = returnPayload (.inl .unit) s := by
  apply congrArg WithTop.some
  apply exact_return fallback (extendModel captured .unit).bound s 0 (.inl .unit) s (.br (.inl .unit))
  · intro _ fault
    cases fault with
    | br arg => cases arg with | inl arg => cases arg
  · intro h
    cases h.unfold with
    | br arg => cases arg with | inl arg => cases arg
    | core step => cases step

private theorem binds_selected (allowUB : Bool) (s t : State) (i : Fin routes.length) (b : Value Unit)
    (run : Region.Eval captured.instr (envOfBound captured.bound) selector.val s i b t)
    (hf : s ≠ 4) (hd : s ≠ 5) :
    denote (region allowUB) captured s = denote (route allowUB i) (extendModel captured b) t := by
  change Behaviour.bind (WithTop.some (nativeOutcomes selector captured s))
    (fun j b t => denote (route allowUB j) (extendModel captured b) t) = _
  rw [selector_exact s t i b run hf hd]
  exact return_bind i b t _

private theorem binds_fault (allowUB : Bool) :
    denote (region allowUB) captured 4 = WithTop.some {Outcome.fault (4 : State)} := by
  change Behaviour.bind (WithTop.some (nativeOutcomes selector captured 4))
    (fun j b t => denote (route allowUB j) (extendModel captured b) t) = _
  rw [selector_at_fault]
  simp [Behaviour.bind, Behaviour.possible, WithTop.untopD_coe]
  ext o
  cases o <;> simp [Outcome.bind]

private theorem binds_diverge (allowUB : Bool) :
    denote (region allowUB) captured 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) := by
  change Behaviour.bind (WithTop.some (nativeOutcomes selector captured 5))
    (fun j b t => denote (route allowUB j) (extendModel captured b) t) = _
  rw [selector_at_diverge]
  simp [Behaviour.bind, Behaviour.possible, WithTop.untopD_coe]
  ext o
  cases o <;> simp [Outcome.bind]

private theorem certificate (allowUB : Bool) : Certified carrier (region allowUB) (table allowUB) := by
  intro c p
  change denote (region allowUB) captured p = _
  fin_cases p
  · exact (binds_selected allowUB 0 1 0 _ (.let₁ (.op .var ⟨by decide, by decide, rfl, rfl⟩)
      (.case_inl .var (.br .var))) (by decide) (by decide)).trans (pass_exact _ _)
  · have chosen := binds_selected allowUB 1 1 1 .unit (.let₁ (.op .var ⟨by decide, by decide, rfl, rfl⟩)
      (.case_inr .var (.br .var))) (by decide) (by decide)
    cases allowUB
    · exact chosen.trans (fallback_exact 1)
    · exact chosen
  · exact (binds_selected allowUB 2 3 0 _ (.let₁ (.op .var ⟨by decide, by decide, rfl, rfl⟩)
      (.case_inl .var (.br .var))) (by decide) (by decide)).trans (pass_exact _ _)
  · exact (binds_selected allowUB 3 2 0 _ (.let₁ (.op .var ⟨by decide, by decide, rfl, rfl⟩)
      (.case_inl .var (.br .var))) (by decide) (by decide)).trans (pass_exact _ _)
  · exact binds_fault allowUB
  · exact binds_diverge allowUB
  · exact (binds_selected allowUB 6 6 0 _ (.let₁ (.op .var ⟨by decide, by decide, rfl, rfl⟩)
      (.case_inl .var (.br .var))) (by decide) (by decide)).trans (pass_exact _ _)

private noncomputable abbrev observed (allowUB : Bool) (s : State) :=
  (iterateCaptured fixture (region allowUB)).run 0 (pairPayload unitPayload unitPayload) s

private theorem repeat_reaches_ub : observed true 0 = ⊤ :=
  (classify carrier _ _ (certificate true) 0 0).trans rfl

private theorem cycle_is_ordinary_divergence :
    observed true 2 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) :=
  (classify carrier _ _ (certificate true) 0 2).trans rfl

private theorem fault_at_four : observed true 4 = WithTop.some {Outcome.fault (4 : State)} :=
  (classify carrier _ _ (certificate true) 0 4).trans rfl

private theorem divergence_at_five :
    observed true 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) :=
  (classify carrier _ _ (certificate true) 0 5).trans rfl

private theorem return_after_repeat : observed false 0 = returnPayload .unit (1 : State) :=
  (classify carrier _ _ (certificate false) 0 0).trans rfl

private theorem checked_refinement : ∀ s, observed false s ≤ observed true s :=
  fun s => (check_iff carrier _ _ (certificate false) (certificate true)).mp (by decide) 0 s

private theorem checked_reverse_failure : ¬ ∀ s, observed true s ≤ observed false s := by
  intro le
  have checked := (check_iff carrier _ _ (certificate true) (certificate false)).mpr (fun _ s => le s)
  have failed : check (table true) (table false) = false := by decide
  rw [failed] at checked
  cases checked

#print axioms classify
#print axioms check_iff
#print axioms repeat_reaches_ub
#print axioms cycle_is_ordinary_divergence
#print axioms fault_at_four
#print axioms divergence_at_five
#print axioms return_after_repeat
#print axioms checked_refinement
#print axioms checked_reverse_failure

end LambdaSSAUBFiniteIterationRegression
