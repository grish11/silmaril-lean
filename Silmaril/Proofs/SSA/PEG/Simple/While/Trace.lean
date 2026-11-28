module

public import Silmaril.SSA.PEG.Simple.While.Trace

public section

namespace Silmaril.SSA.PEG.Simple.WhileProofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {m : Interpretation.{u,v,w} P} {vars outs : List (Ty Data)}
variable {guard : Expr P vars .bool} {body : Stmt P true vars vars}

theorem runEnabled (s : Stmt P false vars outs) (store : Tuple m.Value vars) :
    Exec m s.enableWhile store (s.runLoopFree m store) := by
  induction s with
  | assign rhs =>
    simp only [Stmt.enableWhile, Stmt.runLoopFree]
    cases h : rhs.eval m store with
    | none => exact .assignFailed h
    | some v => exact .assign h
  | project slots => exact .project
  | seq a b ihA ihB =>
    simp only [Stmt.enableWhile, Stmt.runLoopFree]
    cases h : a.runLoopFree m store with
    | none => exact .firstFailed (h ▸ ihA store)
    | some next => exact .seq (h ▸ ihA store) (ihB next)
  | branch guard yes no ihYes ihNo =>
    simp only [Stmt.enableWhile, Stmt.runLoopFree]
    cases h : guard.eval m store with
    | none => exact .branchFailed h
    | some b =>
      cases b with
      | up flag =>
        cases flag
        · exact .branchFalse h (ihNo store)
        · exact .branchTrue h (ihYes store)
  | «while» impossible _ _ _ => nomatch impossible

theorem forgetEnabled (s : Stmt P false vars outs) {store : Tuple m.Value vars}
    {outcome : Option (Tuple m.Value outs)} (h : Exec m s.enableWhile store outcome) :
    Exec m s store outcome := by
  induction s with
  | assign rhs =>
    cases h with
    | assign e => exact .assign e
    | assignFailed e => exact .assignFailed e
  | project slots =>
    cases h
    exact .project
  | seq a b ihA ihB =>
    cases h with
    | firstFailed first => exact .firstFailed (ihA first)
    | seq first second => exact .seq (ihA first) (ihB second)
  | branch guard yes no ihYes ihNo =>
    cases h with
    | branchFailed test => exact .branchFailed test
    | branchTrue test run => exact .branchTrue test (ihYes run)
    | branchFalse test run => exact .branchFalse test (ihNo run)
  | «while» impossible _ _ _ => nomatch impossible

private def Extract {enabled : Bool} (s : Stmt P enabled vars outs)
    (start : Tuple m.Value vars) (outcome : Option (Tuple m.Value outs)) : Prop :=
  match s with
  | .while _ guard body =>
    ∀ final, outcome = some final → ∃ k, WhileTrace m guard (by
      cases ‹enabled = true›
      exact body) k start final
  | _ => True

private theorem extract {enabled : Bool} {s : Stmt P enabled vars outs}
    {start : Tuple m.Value vars} {outcome : Option (Tuple m.Value outs)}
    (h : Exec m s start outcome) : Extract s start outcome := by
  induction h with
  | whileStop test =>
    intro final eq
    cases eq
    exact ⟨0, .stop test⟩
  | whileStep test run rest ihRun ihRest =>
    intro final eq
    obtain ⟨k, trace⟩ := ihRest final eq
    exact ⟨k + 1, .step test run trace⟩
  | whileGuardFailed test => intro final eq; cases eq
  | whileBodyFailed test run ih => intro final eq; cases eq
  | _ => trivial

theorem whileTrace {start final : Tuple m.Value vars}
    (h : Exec m (.while rfl guard body) start (some final)) :
    ∃ k, WhileTrace m guard body k start final :=
  extract h final rfl

theorem traceExec {k : Nat} {start final : Tuple m.Value vars}
    (trace : WhileTrace m guard body k start final) :
    Exec m (.while rfl guard body) start (some final) := by
  induction trace with
  | stop test => exact .whileStop test
  | step test run _ ih => exact .whileStep test run ih

end Silmaril.SSA.PEG.Simple.WhileProofs
