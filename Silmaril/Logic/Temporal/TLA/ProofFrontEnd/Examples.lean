module

import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Thms
meta import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Defs

/-! Parsed regressions for obligation scope and exact premise reuse. -/

namespace Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples

meta section

private def source (body : String) : String :=
  "---- MODULE ProofScope ----\n" ++ body ++ "\n====\n"

private def accepted := source r#"
CONSTANT C
Equal(n) == C = n
ASSUME Zero == Equal(0)
THEOREM Exact == C = 0 BY ONLY Zero
THEOREM Alias == Zero BY Zero
THEOREM Different == C = 1 BY Zero
THEOREM Skipped == FALSE OMITTED
THEOREM CitesSkipped == FALSE BY Skipped
THEOREM LocalRule == ASSUME C = 0, TRUE PROVE C = 0 OBVIOUS
ASSUME Later == FALSE
THEOREM Missing == TRUE
THEOREM CitesRule == TRUE BY LocalRule
THEOREM After == FALSE BY Later
"#

#guard match prepare accepted with
  | .ok context =>
    decide (context.assumptions.map (·.unit) = [2, 9]) &&
    decide (context.theorems.map (·.sourceProof) =
      [.byFacts true [.assumption 2], .byFacts false [.assumption 2],
       .byFacts false [.assumption 2], .omitted, .byFacts false [.theoremDecl 6],
       .obvious, .missing, .byFacts false [.theoremDecl 8], .byFacts false [.assumption 9]]) &&
    decide (context.theorems.map (fun o => o.assumptions.map (·.unit)) =
      [[2], [2], [2], [2], [2], [2], [2, 9], [2, 9], [2, 9]]) &&
    decide (context.theorems.map (fun o => o.hypotheses.length) = [0, 0, 0, 0, 0, 2, 0, 0, 0]) &&
    decide (context.theorems.map (fun o => o.checkExact.isSome) =
      [true, true, false, false, false, false, false, false, true])
  | .error _ => false

#guard match prepare (source r#"
ASSUME A == IF TRUE THEN TRUE ELSE FALSE
ASSUME B == TRUE
THEOREM OutsideMatcher == A BY A
THEOREM Multiple == TRUE BY A, B
"#) with
  | .ok context =>
    decide (context.theorems.map (·.sourceProof) =
      [.byFacts false [.assumption 0], .byFacts false [.assumption 0, .assumption 1]]) &&
    context.theorems.all (fun obligation => obligation.checkExact.isNone)
  | .error _ => false

private def rejected (body : String) (test : Diagnostic → Bool) : Bool :=
  match prepare (source body) with
  | .error diagnostic => test diagnostic
  | .ok _ => false

private def outOfScope (body : String) (unit : Nat) (name : String) : Bool :=
  rejected body fun
    | .factNotInScope index cited => index == unit && cited == name
    | _ => false

#guard outOfScope "THEOREM T == TRUE BY T" 0 "T"
#guard outOfScope "THEOREM T == TRUE BY A\nASSUME A == TRUE" 0 "A"
#guard outOfScope "THEOREM T == TRUE BY U\nTHEOREM U == TRUE" 0 "U"
#guard outOfScope "P == TRUE\nTHEOREM T == TRUE BY P" 1 "P"
#guard outOfScope "THEOREM T == TRUE BY SMT" 0 "SMT"

#guard rejected "EXTENDS TLAPS\nTHEOREM T == TRUE BY SMT" fun
  | .imports => true
  | _ => false

#guard rejected "P == TRUE\nTHEOREM T == TRUE BY DEF P" fun
  | .unsupportedCitation 1 => true
  | _ => false

#guard rejected "ASSUME A == TRUE\nTHEOREM T == TRUE BY A!:" fun
  | .unsupportedCitation 1 => true
  | _ => false

#guard rejected "THEOREM T == TRUE\n<1> QED OBVIOUS" fun
  | .unsupportedProof 0 => true
  | _ => false

#guard rejected "THEOREM T == ASSUME NEW x PROVE x = x" fun
  | .unsupportedStatement 0 => true
  | _ => false

#guard rejected "CONSTANT R\nTHEOREM R == ASSUME TRUE PROVE TRUE" fun
  | .nameConflict 1 "R" => true
  | _ => false

#guard rejected "ASSUME A == TRUE\nTHEOREM A == FALSE" fun
  | .nameConflict 1 "A" => true
  | _ => false

#guard rejected "VARIABLE x\nASSUME A == x = x" fun
  | .expectedConstant _ .state => true
  | _ => false

#guard rejected "THEOREM T == <<TRUE>> OBVIOUS" fun
  | .lowering ⟨_, .unsupported .tuple⟩ => true
  | _ => false

end

universe u

-- A caller can prove a denoted goal separately from the source proof status.
example {V : Type u} (obligation : Obligation) (model : Interpretation V)
    (goal : obligation.goal.term = .boolean true) : SuppliedEvidence obligation model := by
  constructor
  intro valuation _ _
  unfold Proposition.holds DataElab.CheckedExpr.eval
  rw [goal]
  rfl

end Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Examples
