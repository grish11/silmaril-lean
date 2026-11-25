module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.Contexts

/-! # Compositional inversion of finite L1 runs

The evaluation derivations below describe the finite value endpoints of the
existing small-step relation. Both directions are proved without typing or
store coverage assumptions. Chapter 8's equivalence compares these endpoints
pointwise on typed, covered inputs.
-/

public section

namespace Silmaril.Courses.Cambridge.L1

inductive Evaluates : Expr → Store → Config → Prop where
  | int (n : Int) (s : Store) : Evaluates (.int n) s ⟨.int n, s⟩
  | bool (b : Bool) (s : Store) : Evaluates (.bool b) s ⟨.bool b, s⟩
  | skip (s : Store) : Evaluates .skip s ⟨.skip, s⟩
  | add {left right : Expr} {s middle finish : Store} {a b : Int} :
      Evaluates left s ⟨.int a, middle⟩ → Evaluates right middle ⟨.int b, finish⟩ →
      Evaluates (.binary left .add right) s ⟨.int (a + b), finish⟩
  | ge {left right : Expr} {s middle finish : Store} {a b : Int} :
      Evaluates left s ⟨.int a, middle⟩ → Evaluates right middle ⟨.int b, finish⟩ →
      Evaluates (.binary left .ge right) s ⟨.bool (a ≥ b), finish⟩
  | deref {loc : Loc} {s : Store} {n : Int} :
      Store.lookup s loc = some n → Evaluates (.deref loc) s ⟨.int n, s⟩
  | assign {loc : Loc} {rhs : Expr} {s finish : Store} {n : Int} :
      Evaluates rhs s ⟨.int n, finish⟩ → loc ∈ finish →
      Evaluates (.assign loc rhs) s ⟨.skip, finish.insert loc n⟩
  | seq {left right : Expr} {s middle : Store} {finish : Config} :
      Evaluates left s ⟨.skip, middle⟩ → Evaluates right middle finish →
      Evaluates (.seq left right) s finish
  | ifTrue {test yes no : Expr} {s middle : Store} {finish : Config} :
      Evaluates test s ⟨.bool true, middle⟩ → Evaluates yes middle finish →
      Evaluates (.cond test yes no) s finish
  | ifFalse {test yes no : Expr} {s middle : Store} {finish : Config} :
      Evaluates test s ⟨.bool false, middle⟩ → Evaluates no middle finish →
      Evaluates (.cond test yes no) s finish
  | whileFalse {test body : Expr} {s finish : Store} :
      Evaluates test s ⟨.bool false, finish⟩ → Evaluates (.loop test body) s ⟨.skip, finish⟩
  | whileTrue {test body : Expr} {s afterTest afterBody finish : Store} :
      Evaluates test s ⟨.bool true, afterTest⟩ → Evaluates body afterTest ⟨.skip, afterBody⟩ →
      Evaluates (.loop test body) afterBody ⟨.skip, finish⟩ →
      Evaluates (.loop test body) s ⟨.skip, finish⟩

private theorem steps_under (plug : Expr → Expr)
    (lift : ∀ {e e' : Expr} {s s' : Store}, Step ⟨e, s⟩ ⟨e', s'⟩ →
      Step ⟨plug e, s⟩ ⟨plug e', s'⟩)
    {e e' : Expr} {s s' : Store} (path : Steps ⟨e, s⟩ ⟨e', s'⟩) :
    Steps ⟨plug e, s⟩ ⟨plug e', s'⟩ := by
  let wrap : Config → Config := fun c => ⟨plug c.expr, c.store⟩
  apply Relation.ReflTransGen.lift wrap ?_ _ _ path
  rintro ⟨_, _⟩ ⟨_, _⟩ step
  exact lift step

theorem Evaluates.returns {e : Expr} {s : Store} {result : Config}
    (run : Evaluates e s result) : Returns ⟨e, s⟩ result := by
  induction run with
  | int => exact ⟨.refl, .int _⟩
  | bool => exact ⟨.refl, .bool _⟩
  | skip => exact ⟨.refl, .skip⟩
  | deref lookup => exact ⟨.single (.deref lookup), .int _⟩
  | @add _ rhs _ _ _ a _ _ _ left right =>
    have first := steps_under (fun e => .binary e .add rhs) (fun step => .binaryLeft step) left.1
    have second := steps_under (fun e => .binary (.int a) .add e) (fun step => .binaryRight (.int a) step) right.1
    exact ⟨(first.trans second).tail (.add _ _ _), .int _⟩
  | @ge _ rhs _ _ _ a _ _ _ left right =>
    have first := steps_under (fun e => .binary e .ge rhs) (fun step => .binaryLeft step) left.1
    have second := steps_under (fun e => .binary (.int a) .ge e) (fun step => .binaryRight (.int a) step) right.1
    exact ⟨(first.trans second).tail (.ge _ _ _), .bool _⟩
  | @assign loc _ _ _ _ _ present rhs =>
    have path := steps_under (Expr.assign loc) (fun step => .assignStep step) rhs.1
    exact ⟨path.tail (.assignValue present), .skip⟩
  | @seq _ rhs _ _ _ _ _ left right =>
    have path := steps_under (fun e => .seq e rhs) (fun step => .seqStep step) left.1
    exact ⟨(path.tail .seqSkip).trans right.1, right.2⟩
  | @ifTrue _ yesExpr noExpr _ _ _ _ _ test yes =>
    have path := steps_under (fun e => .cond e yesExpr noExpr) (fun step => .ifStep step) test.1
    exact ⟨(path.tail .ifTrue).trans yes.1, yes.2⟩
  | @ifFalse _ yesExpr noExpr _ _ _ _ _ test no =>
    have path := steps_under (fun e => .cond e yesExpr noExpr) (fun step => .ifStep step) test.1
    exact ⟨(path.tail .ifFalse).trans no.1, no.2⟩
  | @whileFalse testExpr bodyExpr _ _ _ test =>
    have path := steps_under (fun e => .cond e (.seq bodyExpr (.loop testExpr bodyExpr)) .skip)
      (fun step => .ifStep step) test.1
    exact ⟨.head .while (path.tail .ifFalse), .skip⟩
  | @whileTrue testExpr bodyExpr _ _ _ _ _ _ _ test body rest =>
    let loop := Expr.loop testExpr bodyExpr
    have guardPath := steps_under (fun e => .cond e (.seq bodyExpr loop) .skip)
      (fun step => .ifStep step) test.1
    have bodyPath := steps_under (fun e => .seq e loop) (fun step => .seqStep step) body.1
    have iteration := ((guardPath.tail .ifTrue).trans bodyPath).tail .seqSkip
    exact ⟨.head .while (iteration.trans rest.1), .skip⟩

private theorem Step.evaluates_before {before after result : Config} (step : Step before after)
    (run : Evaluates after.expr after.store result) : Evaluates before.expr before.store result := by
  induction step generalizing result with
  | add => cases run; exact .add (.int _ _) (.int _ _)
  | ge => cases run; exact .ge (.int _ _) (.int _ _)
  | binaryLeft _ ih =>
    cases run with
    | add hl hr => exact .add (ih hl) hr
    | ge hl hr => exact .ge (ih hl) hr
  | binaryRight value _ ih =>
    cases run with
    | add hl hr =>
      cases value <;> cases hl
      exact .add (.int _ _) (ih hr)
    | ge hl hr =>
      cases value <;> cases hl
      exact .ge (.int _ _) (ih hr)
  | deref lookup => cases run; exact .deref lookup
  | assignValue present => cases run; exact .assign (.int _ _) present
  | assignStep _ ih => cases run with | assign rhs present => exact .assign (ih rhs) present
  | seqSkip => exact .seq (.skip _) run
  | seqStep _ ih => cases run with | seq hl hr => exact .seq (ih hl) hr
  | ifTrue => exact .ifTrue (.bool true _) run
  | ifFalse => exact .ifFalse (.bool false _) run
  | ifStep _ ih =>
    cases run with
    | ifTrue test yes => exact .ifTrue (ih test) yes
    | ifFalse test no => exact .ifFalse (ih test) no
  | «while» =>
    cases run with
    | ifTrue test yes =>
      cases yes with
      | seq body rest =>
        cases rest with
        | whileFalse guard => exact .whileTrue test body (.whileFalse guard)
        | whileTrue guard next remaining => exact .whileTrue test body (.whileTrue guard next remaining)
    | ifFalse test no => cases no; exact .whileFalse test

theorem Returns.evaluates {start result : Config} (run : Returns start result) :
    Evaluates start.expr start.store result := by
  rcases run with ⟨path, value⟩
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨e, s⟩ := result
    cases value
    · exact .int _ _
    · exact .bool _ _
    · exact .skip _
  | head step _ ih => exact step.evaluates_before ih

theorem Evaluates.coverage {Γ : TypeEnv} {e : Expr} {s : Store} {result : Config}
    (run : Evaluates e s result) (covers : StoreCovers Γ s) : StoreCovers Γ result.store := by
  have along {first last : Config} (path : Steps first last) :
      StoreCovers Γ first.store → StoreCovers Γ last.store := by
    intro initial
    induction path with
    | refl => exact initial
    | tail _ step ih => exact step.preserves_coverage ih
  exact along run.returns.1 covers

theorem semanticEquiv_iff_evaluates {Γ : TypeEnv} {T : Ty} {left right : Expr} :
    SemanticEquiv Γ T left right ↔ HasType Γ left T ∧ HasType Γ right T ∧
      ∀ s, StoreCovers Γ s → ∀ result, Evaluates left s result ↔ Evaluates right s result := by
  rw [semanticEquiv_iff_returns]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor <;> intro same s covers result
  · exact ⟨fun run => ((same s covers result).mp run.returns).evaluates,
      fun run => ((same s covers result).mpr run.returns).evaluates⟩
  · exact ⟨fun run => ((same s covers result).mp run.evaluates).returns,
      fun run => ((same s covers result).mpr run.evaluates).returns⟩

end Silmaril.Courses.Cambridge.L1
