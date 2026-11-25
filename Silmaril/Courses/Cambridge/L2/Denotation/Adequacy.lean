module

public import Silmaril.Courses.Cambridge.L2.Denotation.Pure
import Silmaril.Courses.Cambridge.L2.Denotation.Substitution
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-! # Adequacy for pure CBV L2

The logical relation at function type compares applications to related
syntactic values. The environment relation pairs each semantic value with
the expression substituted for its bound occurrence.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.PureDenotation

private def Related : (T : Ty) → Expr → Value T → Prop
  | .int, e, n => e = .int n
  | .bool, e, b => e = .bool b
  | .unit, e, _ => e = .skip
  | .arr A B, e, f => ∃ body, e = .lam A body ∧
      ∀ (arg : Expr) (a : Value A), Related A arg a → ∀ s : Store,
        ∃ result, Steps ⟨body.beta arg, s⟩ ⟨result, s⟩ ∧ Related B result (f a)

private theorem Related.isValue {T : Ty} {e : Expr} {v : Value T}
    (related : Related T e v) : IsValue e := by
  cases T with
  | int => cases related; exact .int _
  | bool => cases related; exact .bool _
  | unit => cases related; exact .skip
  | arr => obtain ⟨_, rfl, _⟩ := related; exact .lam _ _

private def EnvRelated {Γ : List Ty} (ρ : Env Γ) (σ : Nat → Expr) : Prop :=
  ∀ {i : Nat} {T : Ty} (lookup : Γ[i]? = some T), Related T (σ i) (ρ.lookup lookup)

private theorem EnvRelated.push {Γ : List Ty} {T : Ty} {ρ : Env Γ} {σ : Nat → Expr}
    {v : Value T} {e : Expr} (env : EnvRelated ρ σ) (value : Related T e v) :
    EnvRelated (ρ.push v) (extendSubst e σ) := by
  intro index A lookup
  cases index with
  | zero =>
    cases Option.some.inj lookup
    exact value
  | succ index =>
    exact env (i := index) lookup

private theorem steps_under (plug : Expr → Expr)
    (lift : ∀ {e f : Expr} {s t : Store}, Step ⟨e, s⟩ ⟨f, t⟩ → Step ⟨plug e, s⟩ ⟨plug f, t⟩)
    {e f : Expr} {s : Store} (run : Steps ⟨e, s⟩ ⟨f, s⟩) :
    Steps ⟨plug e, s⟩ ⟨plug f, s⟩ := by
  let wrap : Config → Config := fun c => ⟨plug c.expr, c.store⟩
  apply Relation.ReflTransGen.lift wrap ?_ _ _ run
  rintro ⟨_, _⟩ ⟨_, _⟩ step
  exact lift step

private theorem reduces {Γ : List Ty} {e : Expr} {T : Ty} (term : Term Γ e T) :
    ∀ (ρ : Env Γ) (σ : Nat → Expr), EnvRelated ρ σ → ∀ s : Store,
      ∃ v, Steps ⟨e.subst σ, s⟩ ⟨v, s⟩ ∧ Related T v (term.denote ρ) := by
  induction term with
  | int n => intro ρ σ related s; exact ⟨.int n, .refl, rfl⟩
  | bool b => intro ρ σ related s; exact ⟨.bool b, .refl, rfl⟩
  | skip => intro ρ σ related s; exact ⟨.skip, .refl, rfl⟩
  | bvar lookup =>
    intro ρ σ related s
    exact ⟨_, .refl, related lookup⟩
  | @add _ left right ld rd ihLeft ihRight =>
    intro ρ σ related s
    obtain ⟨lv, hl, rl⟩ := ihLeft ρ σ related s
    obtain ⟨rv, hr, rr⟩ := ihRight ρ σ related s
    change lv = .int (ld.denote ρ) at rl
    change rv = .int (rd.denote ρ) at rr
    subst lv rv
    have first := steps_under (fun e => .binary e .add (right.subst σ)) (fun h => .binaryLeft h) hl
    have second := steps_under (fun e => .binary (.int (ld.denote ρ)) .add e)
      (fun h => .binaryRight (.int _) h) hr
    exact ⟨_, (first.trans second).tail (.add _ _ _), rfl⟩
  | @ge _ left right ld rd ihLeft ihRight =>
    intro ρ σ related s
    obtain ⟨lv, hl, rl⟩ := ihLeft ρ σ related s
    obtain ⟨rv, hr, rr⟩ := ihRight ρ σ related s
    change lv = .int (ld.denote ρ) at rl
    change rv = .int (rd.denote ρ) at rr
    subst lv rv
    have first := steps_under (fun e => .binary e .ge (right.subst σ)) (fun h => .binaryLeft h) hl
    have second := steps_under (fun e => .binary (.int (ld.denote ρ)) .ge e)
      (fun h => .binaryRight (.int _) h) hr
    exact ⟨_, (first.trans second).tail (.ge _ _ _), rfl⟩
  | @cond _ guard yes no T gd yd nd ihGuard ihYes ihNo =>
    intro ρ σ related s
    obtain ⟨test, path, eq⟩ := ihGuard ρ σ related s
    change test = .bool (gd.denote ρ) at eq
    subst test
    have first := steps_under (fun e => .cond e (yes.subst σ) (no.subst σ)) (fun h => .ifStep h) path
    cases answer : gd.denote ρ
    · obtain ⟨v, tail, result⟩ := ihNo ρ σ related s
      rw [answer] at first
      exact ⟨v, (first.tail .ifFalse).trans tail, by simpa [Term.denote, answer] using result⟩
    · obtain ⟨v, tail, result⟩ := ihYes ρ σ related s
      rw [answer] at first
      exact ⟨v, (first.tail .ifTrue).trans tail, by simpa [Term.denote, answer] using result⟩
  | @seq _ left right T ld rd ihLeft ihRight =>
    intro ρ σ related s
    obtain ⟨v, hl, eq⟩ := ihLeft ρ σ related s
    change v = .skip at eq
    subst v
    obtain ⟨v, hr, result⟩ := ihRight ρ σ related s
    have first := steps_under (fun e => .seq e (right.subst σ)) (fun h => .seqStep h) hl
    refine ⟨v, (first.tail .seqSkip).trans hr, ?_⟩
    change Related T v (match ld.denote ρ with | () => rd.denote ρ)
    cases ld.denote ρ
    exact result
  | lam body ih =>
    intro ρ σ related s
    refine ⟨_, .refl, ⟨_, rfl, ?_⟩⟩
    intro arg a argument store
    rw [beta_after_subst]
    exact ih (ρ.push a) (extendSubst arg σ) (related.push argument) store
  | @app _ fn arg A B fd ad ihFn ihArg =>
    intro ρ σ related s
    obtain ⟨closure, fnPath, fnResult⟩ := ihFn ρ σ related s
    obtain ⟨argument, argPath, argResult⟩ := ihArg ρ σ related s
    obtain ⟨body, rfl, applyClosure⟩ := fnResult
    obtain ⟨v, bodyPath, result⟩ := applyClosure argument (ad.denote ρ) argResult s
    have first := steps_under (fun e => .app e (arg.subst σ)) (fun h => .appLeft h) fnPath
    have second := steps_under (Expr.app (.lam A body)) (fun h => .appRight (.lam A body) h) argPath
    exact ⟨v, ((first.trans second).tail (.appFun argResult.isValue)).trans bodyPath, result⟩
  | @letE _ value body A B vd bd ihValue ihBody =>
    intro ρ σ related s
    obtain ⟨argument, valuePath, valueResult⟩ := ihValue ρ σ related s
    obtain ⟨v, bodyPath, result⟩ :=
      ihBody (ρ.push (vd.denote ρ)) (extendSubst argument σ) (related.push valueResult) s
    rw [← beta_after_subst] at bodyPath
    have first := steps_under (fun e => .letE A e (body.subst (Expr.liftSubst σ)))
      (fun h => .letStep h) valuePath
    exact ⟨v, (first.tail (.letValue valueResult.isValue)).trans bodyPath, result⟩

private theorem reduces_closed {e : Expr} {T : Ty} (term : Term [] e T) (s : Store) :
    ∃ v, Steps ⟨e, s⟩ ⟨v, s⟩ ∧ Related T v (term.denote .empty) := by
  have empty : EnvRelated Env.empty Expr.bvar := by
    intro index T lookup
    simp at lookup
  simpa only [Expr.subst_id] using reduces term Env.empty Expr.bvar empty s

theorem Term.terminates {e : Expr} {T : Ty} (term : Term [] e T) (s : Store) :
    ∃ v, Steps ⟨e, s⟩ ⟨v, s⟩ ∧ IsValue v := by
  obtain ⟨v, path, value⟩ := reduces_closed term s
  exact ⟨v, path, value.isValue⟩

private theorem step_deterministic {before firstResult secondResult : Config}
    (first : Step before firstResult) (second : Step before secondResult) :
    firstResult = secondResult := by
  induction first generalizing secondResult with
  | add =>
      cases second with
      | add => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  | ge =>
      cases second with
      | ge => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  | binaryLeft inner ih =>
      cases second with
      | add => cases inner
      | ge => cases inner
      | binaryLeft other =>
          have equal := ih other
          cases equal
          rfl
      | binaryRight value _ => exact False.elim (value_terminal value _ inner)
  | binaryRight value inner ih =>
      cases second with
      | add => cases inner
      | ge => cases inner
      | binaryLeft other => exact False.elim (value_terminal value _ other)
      | binaryRight _ other =>
          have equal := ih other
          cases equal
          rfl
  | deref firstPresent =>
      cases second with
      | deref secondPresent =>
          have equal : _ := firstPresent.symm.trans secondPresent
          cases Option.some.inj equal
          rfl
  | assignValue =>
      cases second with
      | assignValue => rfl
      | assignStep inner => cases inner
  | assignStep inner ih =>
      cases second with
      | assignValue => cases inner
      | assignStep other =>
          have equal := ih other
          cases equal
          rfl
  | seqSkip =>
      cases second with
      | seqSkip => rfl
      | seqStep inner => cases inner
  | seqStep inner ih =>
      cases second with
      | seqSkip => cases inner
      | seqStep other =>
          have equal := ih other
          cases equal
          rfl
  | ifTrue =>
      cases second with
      | ifTrue => rfl
      | ifStep inner => cases inner
  | ifFalse =>
      cases second with
      | ifFalse => rfl
      | ifStep inner => cases inner
  | ifStep inner ih =>
      cases second with
      | ifTrue => cases inner
      | ifFalse => cases inner
      | ifStep other =>
          have equal := ih other
          cases equal
          rfl
  | «while» =>
      cases second
      rfl

  | appLeft inner ih =>
      cases second with
      | appLeft other => cases ih other; rfl
      | appRight value _ => exact False.elim (value_terminal value _ inner)
      | appFun _ => cases inner
  | appRight value inner ih =>
      cases second with
      | appLeft other => exact False.elim (value_terminal value _ other)
      | appRight _ other => cases ih other; rfl
      | appFun ready => exact False.elim (value_terminal ready _ inner)
  | appFun ready =>
      cases second with
      | appLeft inner => cases inner
      | appRight _ inner => exact False.elim (value_terminal ready _ inner)
      | appFun _ => rfl
  | letStep inner ih =>
      cases second with
      | letStep other => cases ih other; rfl
      | letValue ready => exact False.elim (value_terminal ready _ inner)
  | letValue ready =>
      cases second with
      | letStep inner => exact False.elim (value_terminal ready _ inner)
      | letValue _ => rfl
  | letRecFun =>
      cases second
      rfl

private theorem stepRightUnique : Relator.RightUnique Step :=
  fun ⦃_ _ _⦄ first other => step_deterministic first other

/-- No infinite CBV trace starts from a closed term of the fragment. -/
theorem Term.not_diverges {e : Expr} {T : Ty} (term : Term [] e T) (s : Store) :
    ¬ InfiniteTrace Step ⟨e, s⟩ := by
  obtain ⟨_, path, value⟩ := term.terminates s
  exact RightUnique.not_infinite_of_final stepRightUnique path (value_terminal value)

/-- The denotation determines the full returned configuration at a ground
type, for every initial store and against the original L2 reduction relation. -/
theorem Term.adequate {e : Expr} {T : Ty} (term : Term [] e T) (ground : Ground T)
    (s : Store) (result : Config) :
    Steps ⟨e, s⟩ result ∧ IsValue result.expr ↔
      result = ⟨ground.quote (term.denote .empty), s⟩ := by
  obtain ⟨value, path, related⟩ := reduces_closed term s
  have exactValue : value = ground.quote (term.denote .empty) := by
    cases ground <;> exact related
  subst value
  constructor
  · rintro ⟨run, value⟩
    cases result
    exact RightUnique.reach_final_eq stepRightUnique run path (value_terminal value)
      (value_terminal related.isValue)
  · rintro rfl
    exact ⟨path, related.isValue⟩

end Silmaril.Courses.Cambridge.L2.PureDenotation
