module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Recursive.Statement

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Token.Proofs
open Simple.Proofs (get_map ports_get)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars before inside all : List (Ty Data)}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
variable {read : Reads (model m) all} {active : List (Fin all.length)} {i : Index all.length}

/-- Sampling completion at any finite pass requires a defined initial
marker. This also holds when the loop takes zero steps. -/
theorem loopMarkerBottom
    {ctx : Tuple (Port before) (.bool :: vars)}
    {code : Code (Opcode P) params ((.bool :: vars) ++ before) inside}
    {guard : Port inside .bool} {feedback : Tuple (Port inside) (.bool :: vars)}
    {neg : Opcode P [.bool] .bool}
    (v : View (model m) env read active (.loop ctx code guard feedback neg))
    (missing : BottomOn read active i
      (v.embed ((Code.loop ctx code guard feedback neg).lift (ctx.get .head)))) :
    BottomOn read active i (v.embed (portLeft .head)) := by
  intro j agree
  have seed : samples v j .head 0 = none :=
    (samples_zero v j .head).trans (missing _ (agrees_set v agree 0))
  change read (v.embed (portLeft .head)) j = none
  rw [evalEquation v j .head]
  cases read (v.embed (passRef (.bool :: vars))) j with
  | none => rfl
  | some count =>
    change monotonize (samples v j .head) count.down = none
    cases sample : monotonize (samples v j .head) count.down with
    | none => rfl
    | some marker =>
      obtain ⟨last, prior⟩ := (monotonize_eq_some_iff _ _ _).mp sample
      by_cases zero : count.down = 0
      · rw [zero, seed] at last
        cases last
      · have first := prior 0 (Nat.pos_of_ne_zero zero)
        rw [seed] at first
        cases first

theorem whileFacts (guard : Expr P vars .bool) (body : Stmt P true vars vars)
    (neg : P [.bool] .bool) (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (ctx : Tuple (Port before) (.bool :: vars))
    (step : Build (Opcode P) params (loopTest guard params before).nodes (.bool :: vars))
    (v : View (model m) env read active (closeLoop neg ctx (loopTest guard params before) step).code)
    (bodyFacts : StatementFacts body
      ((loopTest guard params before).code.liftRefs (loopSlots vars before)) step v.inner.right) :
    StatementFacts (.while rfl guard body) ctx (closeLoop neg ctx (loopTest guard params before) step) v := by
  let test := loopTest guard params before
  change View (model m) env read active (.loop ctx (.seq (.straight test.code) step.code)
    (step.code.lift (test.refs.get .head)) step.refs (.source neg)) at v
  have localFacts : LoopFacts v guard body (fun _ => True) :=
    ⟨fun aligned j agree => guardAligned guard step.code v aligned j agree,
      fun aligned ran => bodyFacts.ofReturns (loopScopeAligned guard step.code v aligned) ran,
      fun aligned done => by
        obtain ⟨next, ran, data⟩ := bodyFacts.ofToken (loopScopeAligned guard step.code v aligned) done
        exact ⟨next, ran, data, trivial⟩⟩
  constructor
  · intro i missing
    have output := loopMarkerBottom v missing
    intro j agree
    change read (v.embed (((ports (.bool :: vars)).map fun _ p => portLeft p).get .head)) j = _
    rw [get_map, ports_get]
    exact output j agree
  · intro i store final entry ran
    obtain ⟨_, trace⟩ := ran.while_trace
    exact (LoopFacts.ofTrace v localFacts negSem entry trace).1
  · intro i store entry complete
    change (read (v.embed (portLeft .head)) i).isSome at complete
    obtain ⟨_, final, trace, _⟩ := LoopFacts.ofCompletion v localFacts negSem entry complete
    exact ⟨final, trace.exec, (LoopFacts.ofTrace v localFacts negSem entry trace).1⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs
