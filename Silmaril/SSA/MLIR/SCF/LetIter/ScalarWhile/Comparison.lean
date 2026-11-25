module

public import Silmaril.SSA.MLIR.SCF.LetIter.ScalarWhile.Defs
public import Silmaril.SSA.MLIR.SCF.LetIter.Operational

/-! The typed scalar evaluator and the region controller have matching exits and backedges. -/

public section

namespace Silmaril.MLIR.SCF.LetIter.ScalarWhile

open Arith (Width Env)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Institution.Observational (Observation iterBeh noFree)
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.Semantics (BoundEnv Eval Fault InstrDeterministic extend extend_zero)
open Silmaril.Isotope.LetIter.Semantics.External (Diverges)

variable {Op : OpSignature} {Input Result : List Width}
variable (loop : While Op Input Result) (evalOp : Pure.Eval Op) (input : Env Input)

private abbrev beforeAt (state : Env loop.State) :=
  loop.before.eval evalOp Condition.eval (state.append input)

private abbrev yieldAt (payload : Env loop.Payload) :=
  loop.after.eval evalOp Yield.eval (payload.append input)

private abbrev parentAt (payload : Env loop.Payload) :=
  loop.cont.eval evalOp Return.eval (payload.append input)

local notation "M" => model (State := loop.State) (Payload := loop.Payload) (Result := Result) evalOp input
local notation "p" => toRegionLoop loop

private theorem eval_call_iff {n : Nat} {bound : BoundEnv (M).α n} {t : Tm Empty
    (Call Op Input Result loop.State loop.Payload) n} {f : Call Op Input Result loop.State loop.Payload}
    {arg out : Value (M).α} (harg : Eval (M).instr noFree bound t () arg ()) :
    Eval (M).instr noFree bound (.op f t) () out () ↔ f.run evalOp input arg = some out := by
  refine ⟨fun run => ?_, fun h => .op harg h⟩
  cases run with
  | op argEval call =>
      have det : InstrDeterministic (M).instr := fun _ _ _ _ s₁ _ s₂ a b =>
        ⟨Option.some.inj (a.symm.trans b), Subsingleton.elim (α := Unit) s₁ s₂⟩
      obtain ⟨rfl, rfl⟩ := harg.deterministic det argEval
      exact call

private theorem eval_condition_iff {state : Env loop.State}
    {out : Value (Atom loop.State loop.Payload Result)} :
    Eval (M).instr noFree (extend (M).bound (.atom (.state state))) (p).condition () out () ↔
      (let (test, payload) := beforeAt loop evalOp input state
       if test then Value.inr (.atom (.payload payload)) else .inl (.atom (.payload payload))) = out := by
  change Eval (M).instr noFree _ (.op (.before loop.before) (.bv 0)) () out () ↔ _
  rw [eval_call_iff loop evalOp input .bv]
  cases h : beforeAt loop evalOp input state with
  | mk test payload =>
      change loop.before.eval evalOp Condition.eval (state.append input) = (test, payload) at h
      simp only [extend_zero, Call.run, h, Option.some.injEq]

private theorem exit_iff {state : Env loop.State} {out : Value (Atom loop.State loop.Payload Result)} :
    (p).Exit M (.atom (.state state), ()) out () ↔
      ∃ payload, beforeAt loop evalOp input state = (false, payload) ∧ out = .atom (.payload payload) := by
  change Eval (M).instr noFree (extend (M).bound (.atom (.state state))) (p).condition () (.inl out) () ↔ _
  rw [eval_condition_iff loop evalOp input]
  cases h : beforeAt loop evalOp input state with
  | mk test payload => cases test <;> simp [eq_comm]

private theorem backedge_iff {state : Env loop.State} {c : RegionLoop.Entry M} :
    (p).Backedge M (.atom (.state state), ()) c ↔
      ∃ payload, beforeAt loop evalOp input state = (true, payload) ∧
        c = (.atom (.state (yieldAt loop evalOp input payload)), ()) := by
  constructor
  · rintro ⟨v, ⟨⟩, test, afterRegion⟩
    have htest := (eval_condition_iff loop evalOp input).mp test
    cases hbefore : beforeAt loop evalOp input state with
    | mk test payload => cases test with
      | false =>
          rw [hbefore] at htest
          cases htest
      | true =>
          rw [hbefore] at htest
          obtain rfl := Value.inr.inj htest
          have hafter := Option.some.inj ((eval_call_iff loop evalOp input .bv).mp afterRegion)
          exact ⟨payload, rfl, Prod.ext hafter.symm (Subsingleton.elim (α := Unit) _ _)⟩
  · rintro ⟨payload, test, rfl⟩
    refine ⟨.atom (.payload payload), (), (eval_condition_iff loop evalOp input).mpr ?_, .op .bv rfl⟩
    rw [test]
    rfl

private theorem runFrom_succ (state : Env loop.State) (fuel : Nat) :
    loop.runFrom evalOp input (fuel + 1) state =
      let (test, payload) := beforeAt loop evalOp input state
      if test then loop.runFrom evalOp input fuel (yieldAt loop evalOp input payload)
      else some (parentAt loop evalOp input payload) := rfl

/-- An exit followed by the parent is witnessed by a sufficient scalar loop budget. -/
private theorem path_returns {d : RegionLoop.Entry M} {out : Value (M).α}
    (exit : (p).Exit M d out ()) {c : RegionLoop.Entry M} (path : Relation.ReflTransGen ((p).Backedge M) c d)
    {state : Env loop.State} (hc : c = (.atom (.state state), ())) :
    ∃ fuel payload, loop.runFrom evalOp input fuel state = some (parentAt loop evalOp input payload) ∧
      out = .atom (.payload payload) := by
  revert state
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro state rfl
      obtain ⟨payload, hbefore, hout⟩ := (exit_iff loop evalOp input).mp exit
      exact ⟨1, payload, by rw [runFrom_succ loop evalOp input, hbefore]; rfl, hout⟩
  | head edge _ ih =>
      intro state rfl
      obtain ⟨payload, hbefore, hc⟩ := (backedge_iff loop evalOp input).mp edge
      obtain ⟨fuel, final, hrun, hout⟩ := ih hc
      exact ⟨fuel + 1, final, by rw [runFrom_succ loop evalOp input, hbefore]; exact hrun, hout⟩

private theorem fuel_returns {result : Env Result} (fuel : Nat) {state : Env loop.State}
    (run : loop.runFrom evalOp input fuel state = some result) :
    ∃ payload, (p).LoopReturns M (.atom (.state state), ()) (.atom (.payload payload)) () ∧
      parentAt loop evalOp input payload = result := by
  induction fuel generalizing state with
  | zero => simp [While.runFrom] at run
  | succ fuel ih =>
      rw [runFrom_succ loop evalOp input] at run
      cases h : beforeAt loop evalOp input state with
      | mk test payload => cases test with
        | false =>
            rw [h] at run
            exact ⟨payload, ⟨_, .refl, (exit_iff loop evalOp input).mpr ⟨payload, h, rfl⟩⟩,
              Option.some.inj run⟩
        | true =>
            rw [h] at run
            obtain ⟨out, ⟨d, path, exit⟩, parent⟩ := ih run
            exact ⟨out, ⟨d, path.head ((backedge_iff loop evalOp input).mpr ⟨payload, h, rfl⟩), exit⟩, parent⟩

/-- The independent scalar and LetIter semantics return the same result vector. -/
theorem returns_iff_proof (out : Value (Atom loop.State loop.Payload Result)) :
    Observation.ret () out () ∈ observe loop evalOp input ↔
      ∃ result, out = .atom (.result result) ∧ ∃ fuel, loop.run evalOp fuel input = some result := by
  rw [observe, ← RegionLoop.observe_eq_iterBeh]
  constructor
  · rintro ⟨v, ⟨⟩, payload, ⟨⟩, init, ⟨d, path, exit⟩, parent⟩
    have hinit := Option.some.inj ((eval_call_iff loop evalOp input .unit).mp init)
    change Value.atom (Atom.state (loop.init.eval input)) = v at hinit
    subst v
    obtain ⟨fuel, payload, run, rfl⟩ := path_returns loop evalOp input exit path rfl
    have hr := Option.some.inj ((eval_call_iff loop evalOp input .bv).mp parent)
    exact ⟨parentAt loop evalOp input payload, hr.symm, fuel, run⟩
  · rintro ⟨result, rfl, fuel, run⟩
    obtain ⟨payload, returns, hparent⟩ := fuel_returns loop evalOp input fuel run
    refine ⟨.atom (.state (loop.init.eval input)), (), .atom (.payload payload), (), .op .unit rfl, returns, ?_⟩
    exact .op .bv (congrArg (fun v => some (Value.atom (Atom.result v))) hparent)

private theorem no_call_div {n : Nat} {bound : BoundEnv (M).α n}
    {f : Call Op Input Result loop.State loop.Payload} {arg : Tm Empty _ n}
    (finiteArg : ¬ Diverges (M).instr noFree (M).prim (.term bound arg ())) :
    ¬ Diverges (M).instr noFree (M).prim (.term bound (.op f arg) ()) := by
  intro div
  cases div.unfold with
  | primitive _ impossible => exact impossible
  | core step => cases step with | op argDiv => exact finiteArg argDiv

private theorem no_iteration_div {c : RegionLoop.Entry M} : ¬ (p).IterationDiverges M c := by
  obtain ⟨state, ⟨⟩⟩ := c
  rintro (before | ⟨payload, ⟨⟩, _, afterRegion⟩)
  · exact no_call_div loop evalOp input (fun h => by cases h.unfold with | core h => cases h) before
  · exact no_call_div loop evalOp input (fun h => by cases h.unfold with | core h => cases h) afterRegion

private theorem runFrom_none_of_closed {R : RegionLoop.Entry M → Prop}
    (closed : ∀ c, R c → (p).IterationDiverges M c ∨ ∃ d, (p).Backedge M c d ∧ R d)
    (fuel : Nat) (state : Env loop.State) (here : R (.atom (.state state), ())) :
    loop.runFrom evalOp input fuel state = none := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rcases closed _ here with div | ⟨d, backedge, tail⟩
      · exact (no_iteration_div loop evalOp input div).elim
      · obtain ⟨payload, hbefore, rfl⟩ := (backedge_iff loop evalOp input).mp backedge
        rw [runFrom_succ loop evalOp input, hbefore]
        exact ih _ tail

private theorem loop_diverges_iff (state : Env loop.State) :
    (p).LoopDiverges M (.atom (.state state), ()) ↔ ∀ fuel, loop.runFrom evalOp input fuel state = none := by
  constructor
  · rintro ⟨R, here, closed⟩ fuel
    exact runFrom_none_of_closed loop evalOp input closed fuel state here
  · intro h
    refine ⟨fun c => ∃ s : Env loop.State, c = (.atom (.state s), ()) ∧
      ∀ fuel, loop.runFrom evalOp input fuel s = none, ⟨state, rfl, h⟩, ?_⟩
    rintro c ⟨s, rfl, allNone⟩
    cases hbefore : beforeAt loop evalOp input s with
    | mk test payload => cases test with
      | false =>
          have noReturn := allNone 1
          rw [runFrom_succ loop evalOp input, hbefore] at noReturn
          cases noReturn
      | true =>
          refine Or.inr ⟨_, (backedge_iff loop evalOp input).mpr ⟨payload, hbefore, rfl⟩, _, rfl, ?_⟩
          intro fuel
          have noReturn := allNone (fuel + 1)
          rw [runFrom_succ loop evalOp input, hbefore] at noReturn
          exact noReturn

/-- Internal LetIter divergence agrees with absence of a return at every
scalar budget. The block calls themselves are total at the admitted interfaces. -/
theorem diverges_iff_proof :
    Observation.diverge () ∈ observe loop evalOp input ↔ loop.Diverges evalOp input := by
  rw [observe, ← RegionLoop.observe_eq_iterBeh]
  constructor
  · rintro (init | ⟨v, ⟨⟩, init, div | ⟨out, ⟨⟩, _, parent⟩⟩)
    · exact (no_call_div loop evalOp input (fun h => by cases h.unfold with | core h => cases h) init).elim
    · have hinit := Option.some.inj ((eval_call_iff loop evalOp input .unit).mp init)
      change Value.atom (Atom.state (loop.init.eval input)) = v at hinit
      subst v
      exact (loop_diverges_iff loop evalOp input _).mp div
    · exact (no_call_div loop evalOp input (fun h => by cases h.unfold with | core h => cases h) parent).elim
  · intro h
    exact Or.inr ⟨_, (), .op .unit rfl, Or.inl ((loop_diverges_iff loop evalOp input _).mpr h)⟩

end Silmaril.MLIR.SCF.LetIter.ScalarWhile
