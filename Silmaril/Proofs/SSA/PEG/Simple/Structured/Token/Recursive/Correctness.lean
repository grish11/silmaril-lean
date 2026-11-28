module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Recursive.Branch
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Recursive.Loop

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Token.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars outs before all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
variable {read : Reads (model m) all} {active : List (Fin all.length)}

theorem compileFacts (neg : P [.bool] .bool)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (s : Stmt P true vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (v : View (model m) env read active (compile neg s ctx).code) :
    StatementFacts s ctx (compile neg s ctx) v := by
  induction s generalizing before active with
  | assign rhs => exact straightFacts (.assign rhs) ctx v
  | project slots => exact straightFacts (.project slots) ctx v
  | seq first second one two =>
    let a := compile (params := params) neg first ctx
    let b := compile (params := params) neg second a.refs
    change View (model m) env read active (.seq a.code b.code) at v
    exact sequenceFacts first second ctx a b v (one ctx v.left) (two a.refs v.right)
  | branch guard yes no first second =>
    let test := (expr guard).lower (params := params) (tail ctx)
    let shared := test.code.liftRefs ctx
    let y := compile (params := params) neg yes shared
    let n := compile (params := params) neg no (y.code.liftRefs shared)
    change View (model m) env read active (joinBranch test y n).code at v
    exact branchFacts guard yes no ctx y n v
      (first shared v.right.left) (second (y.code.liftRefs shared) v.right.right.left)
  | @«while» carried _ guard body ih =>
    let test := loopTest guard params before
    let scope := test.code.liftRefs (loopSlots carried before)
    let step := compile (params := params) neg body scope
    change View (model m) env read active (closeLoop neg ctx test step).code at v
    exact whileFacts guard body neg negSem ctx step v (ih scope v.inner.right)

theorem correspondence (p : Program P true params t) (neg : P [.bool] .bool)
    (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {values : (translate p neg).Valuation (model m)}
    (solves : (translate p neg).Solves (model m) env values)
    (i : Index (program p neg).nodes.length) :
    let observed := (translate p neg).observe (model m) values i
    (∀ {value}, p.Returns m env value → observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) ∧
    ((observed.get (.tail .head)).isSome → ∃ value, p.Returns m env value ∧
      observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) := by
  let compiled := program p neg
  let initial := entry P params
  let body := compile (params := params) neg p.body initial.refs
  let read : Reads (model m) compiled.nodes := graphRead (model m) compiled.code compiled.refs values
  let v : View (model m) env read [] (.seq (.straight initial.code) body.code) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations (model m) env compiled.code compiled.refs solves⟩
  have entered := entryAligned (fixed := i) v
  have facts := compileFacts neg negSem p.body initial.refs v.right
  have forward {value : m.Value t} (ran : p.Returns m env value) :
      (translate p neg).observe (model m) values i = .cons (some value) (.cons (some ⟨true⟩) .nil) := by
    obtain ⟨final, ran, returned⟩ := ran
    have data := facts.ofReturns entered ran
    have result := data i (agrees_self [] i) _ (.tail p.retvar)
    have marker := data i (agrees_self [] i) _ .head
    change read (body.refs.get (.tail p.retvar)) i = some (final.get p.retvar) at result
    change read (body.refs.get .head) i = some ⟨true⟩ at marker
    change Tuple.cons (F := fun t => Option ((model m).Value t))
      (read (body.refs.get (.tail p.retvar)) i) (.cons (read (body.refs.get .head) i) .nil) = _
    rw [result, marker, returned]
  refine ⟨@forward, ?_⟩
  intro complete
  change (read (v.right.embed (body.refs.get .head)) i).isSome at complete
  obtain ⟨final, ran, _⟩ := facts.ofToken entered complete
  have returned : p.Returns m env (final.get p.retvar) := ⟨final, ran, rfl⟩
  exact ⟨_, returned, forward returned⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs
