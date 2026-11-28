module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Region

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {vars : List (Ty Data)} {t : Ty Data}

theorem correspondence (guard : Expr P vars .bool) (body : Body P vars vars) (ret : Port vars t)
    (neg : P [.bool] .bool) (m : Interpretation.{u,v,w} P) (env : Tuple m.Value vars)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {val : (translate guard body ret neg).Valuation (model m)}
    (solves : (translate guard body ret neg).Solves (model m) env val)
    (i : Index (program guard body ret neg).nodes.length) :
    let observed := (translate guard body ret neg).observe (model m) val i
    (∀ {value}, (source guard body ret).Returns m env value →
      observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) ∧
    ((observed.get (.tail .head)).isSome → ∃ value, (source guard body ret).Returns m env value ∧
      observed = .cons (some value) (.cons (some ⟨true⟩) .nil)) := by
  let compiled := program guard body ret neg
  let initial := entry P vars
  let lowered := loop guard body neg initial.refs (params := vars)
  let read : Reads (model m) compiled.nodes := graphRead (model m) compiled.code compiled.refs val
  let v : View (model m) env read [] (.seq (.straight initial.code) lowered.code) :=
    ⟨(fun r => nomatch r), (fun r => r), 0, (fun _ _ => (Nat.zero_add _).symm),
      (fun _ bad => by cases bad), graphEquations (model m) env compiled.code compiled.refs solves⟩
  let facts := loopFreeFacts guard body neg v.right
  have start := entryAligned (fixed := i) v
  have forward {value : m.Value t} (run : (source guard body ret).Returns m env value) :
      (translate guard body ret neg).observe (model m) val i =
        .cons (some value) (.cons (some ⟨true⟩) .nil) := by
    obtain ⟨final, ran, returned⟩ := run
    obtain ⟨_, trace⟩ := ran.while_trace
    have aligned := (LoopFacts.ofTrace v.right facts negSem start trace).1
    have data := aligned i (agrees_self [] i) _ (.tail ret)
    have done := aligned i (agrees_self [] i) _ .head
    change Tuple.cons (F := fun t => Option ((model m).Value t)) (read (lowered.refs.get (.tail ret)) i)
      (.cons (read (lowered.refs.get .head) i) .nil) = _
    change read (lowered.refs.get (.tail ret)) i = some (final.get ret) at data
    change read (lowered.refs.get .head) i = some ⟨true⟩ at done
    change final.get ret = value at returned
    rw [data, done, returned]
  refine ⟨@forward, ?_⟩
  intro done
  change (read (v.right.embed (portLeft .head)) i).isSome at done
  obtain ⟨_, final, trace, _⟩ := LoopFacts.ofCompletion v.right facts negSem start done
  have returns : (source guard body ret).Returns m env (final.get ret) := ⟨final, trace.exec, rfl⟩
  exact ⟨_, returns, forward returns⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Proofs
