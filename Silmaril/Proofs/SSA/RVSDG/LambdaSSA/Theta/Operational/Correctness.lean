module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Proofs

open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics (Env InstrDeterministic)
open Isotope.LambdaSSA.Semantics.Region (Eval Follow)

universe u v w x y

variable {V S : Type u} {Op : Dialect.{u,v} V S} {σ : Type x}
variable {carried : List (PortType V S)} {sigs : List (List (PortType V S))}
variable (m : Model.{u,v,w} Op) (g : RVSDG.Theta.Graph Op carried sigs)

theorem pack_injective {ports : List (PortType V S)} :
    Function.Injective (pack m (ports := ports)) := by
  intro xs ys same
  induction xs with
  | nil => cases ys; rfl
  | cons a rest ih =>
    cases ys with
    | cons b tail =>
      obtain ⟨head, finish⟩ := Value.pair.inj same
      have slot := Value.atom.inj head
      have ab := (Sigma.mk.inj_iff.mp slot).2
      cases eq_of_heq ab
      rw [ih finish]

private theorem instruction_deterministic :
    InstrDeterministic (instruction m (carried := carried) (σ := σ)) := by
  intro op arg initial a sa b sb ra rb
  obtain ⟨xs, rfl, rfl, rfl⟩ := ra
  obtain ⟨ys, packet, rfl, rfl⟩ := rb
  have same := pack_injective m packet
  cases same
  exact ⟨rfl, rfl⟩

theorem split_bodyResult (again : Bool) (output : Tuple m.Val carried) :
    split m (RVSDG.Theta.bodyResult m again output) = (again, output) := by
  cases again <;> rfl

private theorem bodyResult_split (output : Tuple m.Val (RVSDG.Theta.BodyResults carried)) :
    RVSDG.Theta.bodyResult m (split m output).1 (split m output).2 = output := by
  cases output with
  | cons tag rest =>
    obtain ⟨i⟩ := tag
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [Fin.eq_zero j]
      rfl

private theorem body_iff (input output : Tuple m.Val carried) (again : Bool) :
    g.body.run m input = RVSDG.Theta.bodyResult m again output ↔
      split m (g.body.run m input) = (again, output) := by
  constructor
  · intro ran
    rw [ran, split_bodyResult]
  · intro ran
    have h := bodyResult_split m (g.body.run m input)
    rw [ran] at h
    exact h.symm

/-- Each real CFG block either exits at label one or latches the next
packet at its local label zero. -/
theorem block_eval (env : Env (Atom m)) (input output : Tuple m.Val carried)
    (again : Bool) (body : g.body.run m input = RVSDG.Theta.bodyResult m again output) (start : σ) :
    Eval (instruction m) (Isotope.LambdaSSA.Semantics.extend env (pack m input)) (LambdaSSA.Theta.block (step g).op)
      start (if again then 0 else 1) (pack m output) start := by
  have ran : instruction m (step g).op (pack m input) start (choice m (again, output)) start := by
    refine ⟨input, rfl, ?_, rfl⟩
    change choice m (again, output) = choice m (split m (g.body.run m input))
    rw [(body_iff m g input output again).mp body]
  cases again
  · exact .case_inl (.op .var ran) (.br .var)
  · exact .case_inr (.op .var ran) (.br .var)

section Header

variable {Φ : Type y} {header : Region Φ}
variable {instr : Φ → Value (Atom m) → σ → Value (Atom m) → σ → Prop}
variable (headerEval : ∀ (env : Env (Atom m)) (input output : Tuple m.Val carried) (again : Bool),
  g.body.run m input = RVSDG.Theta.bodyResult m again output → ∀ state : σ,
  Eval instr (Isotope.LambdaSSA.Semantics.extend env (pack m input)) header
    state (if again then 0 else 1) (pack m output) state)
include headerEval

private theorem follow_of_returns (env : Env (Atom m)) {input output : Tuple m.Val carried}
    (returned : g.Returns m input output) (start : σ) :
    Follow instr env (fun _ : Fin 1 => header)
      0 (pack m input) start 0 (pack m output) start := by
  change RVSDG.Theta.Iterate _ input output at returned
  induction returned with
  | stop body =>
    exact .step (by decide) (headerEval env _ _ false body start) (.exit (Nat.le_refl 1))
  | again body _ rest =>
    exact .step (by decide) (headerEval env _ _ true body start) rest

variable (deterministic : InstrDeterministic instr)
include deterministic

private theorem returns_of_follow {env : Env (Atom m)} {n : Nat}
    {blocks : Fin n → Region Φ}
    {first label : Nat} {current payload : Value (Atom m)} {start finish : σ}
    (h : Follow instr env blocks first current start label payload finish)
    (sizeEq : n = 1) (bodyEq : ∀ i, blocks i = header)
    (atHeader : first = 0) (old : Tuple m.Val carried) (currentEq : current = pack m old) :
    ∃ out, g.Returns m old out ∧ label = 0 ∧ payload = pack m out ∧ finish = start := by
  refine Follow.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ {n} code first current start label payload finish _ =>
      n = 1 → (∀ i, code i = header) → first = 0 →
        ∀ old, current = pack m old →
          ∃ out, g.Returns m old out ∧ label = 0 ∧ payload = pack m out ∧ finish = start)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?_ ?_ h sizeEq bodyEq atHeader old currentEq
  · intro _ _ _ _ _ _ outside sizeEq _ atHeader _ _
    omega
  · intro env _ _ _ _ _ _ _ _ start _ _ _ round rest _ ih sizeEq bodyEq _ old currentEq
    rw [currentEq, bodyEq] at round
    -- The selector and packet are recovered from the same numbered activation.
    cases resultEq : split m (g.body.run m old) with
    | mk again out =>
      have stepRan := (body_iff m g old out again).mpr resultEq
      have observed :=
        round.deterministic deterministic (headerEval env old out again stepRan start)
      cases again
      · obtain ⟨rfl, rfl, rfl⟩ := observed
        subst_vars
        cases rest with
        | exit _ => exact ⟨out, .stop stepRan, rfl, rfl, rfl⟩
        | step impossible _ _ => exact (Nat.lt_irrefl 1 impossible).elim
      · obtain ⟨rfl, rfl, rfl⟩ := observed
        obtain ⟨value, returned, exit, packed, state⟩ := ih sizeEq bodyEq rfl out rfl
        exact ⟨value, .again stepRan returned, exit, packed, state⟩

theorem loop_eval_iff (input : Tuple m.Val carried) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Eval instr (inputEnv m input) (loop header) start label payload finish ↔
      ∃ output, g.Returns m input output ∧ label = 0 ∧ payload = pack m output ∧ finish = start := by
  constructor
  · intro ran
    cases ran with
    | cfg entry follow =>
      have initial :
          Eval instr (inputEnv m input) (.br 0 (.var 0)) start 0 (pack m input) start :=
        .br .var
      obtain ⟨rfl, rfl, rfl⟩ := entry.deterministic deterministic initial
      exact returns_of_follow m g headerEval deterministic follow rfl (fun _ => rfl) rfl input rfl
  · rintro ⟨output, returned, rfl, rfl, rfl⟩
    exact .cfg (.br .var) (follow_of_returns m g headerEval (inputEnv m input) returned _)

end Header

theorem lower_eval_iff (input : Tuple m.Val carried) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) (lower g) start label payload finish ↔
      ∃ output, g.Returns m input output ∧ label = 0 ∧ payload = pack m output ∧ finish = start :=
  loop_eval_iff m g (block_eval m g) (instruction_deterministic m) input start finish label payload

theorem returns_iff_runFuel (input output : Tuple m.Val carried) :
    g.Returns m input output ↔ ∃ fuel, runFuel m g fuel input = some output := by
  constructor
  · intro ran
    change RVSDG.Theta.Iterate _ input output at ran
    induction ran with
    | stop completed =>
      exact ⟨1, by rw [runFuel, (body_iff m g _ _ false).mp completed]; rfl⟩
    | again completed _ ih =>
      obtain ⟨fuel, rest⟩ := ih
      exact ⟨fuel + 1, by rw [runFuel, (body_iff m g _ _ true).mp completed]; exact rest⟩
  · rintro ⟨fuel, ran⟩
    induction fuel generalizing input with
    | zero => cases ran
    | succ fuel ih =>
      rw [runFuel] at ran
      cases observed : split m (g.body.run m input) with
      | mk again next =>
        have stepRan := (body_iff m g input next again).mpr observed
        rw [observed] at ran
        cases again
        · have same : next = output := Option.some.inj ran
          subst next
          exact .stop stepRan
        · exact .again stepRan (ih next ran)

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Proofs
