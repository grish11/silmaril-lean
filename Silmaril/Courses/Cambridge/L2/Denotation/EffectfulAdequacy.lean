module

public import Silmaril.Courses.Cambridge.L2.Denotation.Effectful
import Silmaril.Courses.Cambridge.L2.Denotation.Operational
import Silmaril.Courses.Cambridge.L2.Denotation.Substitution

/-! # Finite adequacy of effectful CBV L2

A related closure takes each related argument and each store covering the
location assumptions to a matched semantic result and substitution run.
The proof uses the existing L2 store-domain preservation lemma.
-/

public section

namespace Silmaril.Courses.Cambridge.L2.EffectfulDenotation

open Denotation (LexicalEnv stepRightUnique steps_under)
open PureDenotation (Ground beta_after_subst extendSubst)

private theorem pure_run {A : Type} (a : A) (s : Store) : (a, s) ∈ (pure a : Computation A).run s :=
  Part.mem_some _

private theorem bind_run {A B : Type} {first : Computation A} {next : A → Computation B}
    {a : A} {b : B} {start middle finish : Store}
    (head : (a, middle) ∈ first.run start) (tail : (b, finish) ∈ (next a).run middle) :
    (b, finish) ∈ (first >>= next).run start := by
  change (b, finish) ∈ (first.run start).bind (fun p => (next p.1).run p.2)
  exact Part.mem_bind head tail

private theorem read_run {loc : Loc} {n : Int} {s : Store}
    (found : L1.Store.lookup s loc = some n) : (n, s) ∈ (read loc).run s := by
  change (n, s) ∈ Part.ofOption _
  simp [found]

private theorem write_run {loc : Loc} {n : Int} {s : Store} (present : loc ∈ s) :
    ((), s.insert loc n) ∈ (write loc n).run s := by
  change ((), s.insert loc n) ∈ Part.ofOption _
  simp [L1.Store.update_eq_some s loc n present]

private theorem steps_cover {locations : L1.TypeEnv} {before after : Config}
    (run : Steps before after) (covers : Covers locations before.store) : Covers locations after.store := by
  induction run with
  | refl => exact covers
  | tail _ step ih => exact step.preserves_coverage ih

private def Related (locations : L1.TypeEnv) : (T : Ty) → Expr → Value T → Prop
  | .int, e, n => e = .int n
  | .bool, e, b => e = .bool b
  | .unit, e, _ => e = .skip
  | .arr A B, e, f => ∃ body, e = .lam A body ∧
      ∀ (arg : Expr) (a : Value A), Related locations A arg a →
        ∀ (s : Store), Covers locations s →
          ∃ result value finalStore, (value, finalStore) ∈ (f a).run s ∧
            Steps ⟨body.beta arg, s⟩ ⟨result, finalStore⟩ ∧ Related locations B result value

private theorem Related.isValue {locations : L1.TypeEnv} {T : Ty} {e : Expr} {v : Value T}
    (related : Related locations T e v) : IsValue e := by
  cases T with
  | int => cases related; exact .int _
  | bool => cases related; exact .bool _
  | unit => cases related; exact .skip
  | arr => obtain ⟨_, rfl, _⟩ := related; exact .lam _ _

private def EnvRelated (locations : L1.TypeEnv) {Γ : List Ty} (ρ : Env Γ) (σ : Nat → Expr) : Prop :=
  ∀ {i : Nat} {T : Ty} (lookup : Γ[i]? = some T), Related locations T (σ i) (ρ.lookup lookup)

private theorem EnvRelated.push {locations : L1.TypeEnv}
    {Γ : List Ty} {T : Ty} {ρ : Env Γ} {σ : Nat → Expr} {v : Value T} {e : Expr}
    (env : EnvRelated locations ρ σ) (value : Related locations T e v) :
    EnvRelated locations (ρ.push v) (extendSubst e σ) := by
  intro i A lookup
  cases i with
  | zero =>
    cases Option.some.inj lookup
    exact value
  | succ i =>
    exact env (i := i) lookup

private theorem realizes {locations : L1.TypeEnv} {Γ : List Ty} {e : Expr} {T : Ty}
    (term : Term locations Γ e T) :
    ∀ (ρ : Env Γ) (σ : Nat → Expr), EnvRelated locations ρ σ → ∀ s : Store, Covers locations s →
      ∃ result value finalStore, (value, finalStore) ∈ (term.denote ρ).run s ∧
        Steps ⟨e.subst σ, s⟩ ⟨result, finalStore⟩ ∧ Related locations T result value := by
  induction term with
  | int n =>
    intro ρ σ env s covers
    exact ⟨.int n, n, s, pure_run n s, .refl, rfl⟩
  | bool b =>
    intro ρ σ env s covers
    exact ⟨.bool b, b, s, pure_run b s, .refl, rfl⟩
  | skip =>
    intro ρ σ env s covers
    exact ⟨.skip, (), s, pure_run () s, .refl, rfl⟩
  | bvar lookup =>
    intro ρ σ env s covers
    exact ⟨_, _, s, pure_run _ s, .refl, env lookup⟩
  | @add _ left right ld rd ihLeft ihRight =>
    intro ρ σ env s covers
    obtain ⟨lv, a, middle, ml, hl, rl⟩ := ihLeft ρ σ env s covers
    obtain ⟨rv, b, finish, mr, hr, rr⟩ := ihRight ρ σ env middle (steps_cover hl covers)
    change lv = .int a at rl
    change rv = .int b at rr
    subst lv rv
    have first := steps_under (fun e => .binary e .add (right.subst σ)) (fun h => .binaryLeft h) hl
    have second := steps_under (fun e => .binary (.int a) .add e) (fun h => .binaryRight (.int a) h) hr
    exact ⟨_, a + b, finish, bind_run ml (bind_run mr (pure_run _ _)),
      (first.trans second).tail (.add a b finish), rfl⟩
  | @ge _ left right ld rd ihLeft ihRight =>
    intro ρ σ env s covers
    obtain ⟨lv, a, middle, ml, hl, rl⟩ := ihLeft ρ σ env s covers
    obtain ⟨rv, b, finish, mr, hr, rr⟩ := ihRight ρ σ env middle (steps_cover hl covers)
    change lv = .int a at rl
    change rv = .int b at rr
    subst lv rv
    have first := steps_under (fun e => .binary e .ge (right.subst σ)) (fun h => .binaryLeft h) hl
    have second := steps_under (fun e => .binary (.int a) .ge e) (fun h => .binaryRight (.int a) h) hr
    exact ⟨_, decide (a ≥ b), finish, bind_run ml (bind_run mr (pure_run _ _)),
      (first.trans second).tail (.ge a b finish), rfl⟩
  | @cond _ guard yes no T gd yd nd ihGuard ihYes ihNo =>
    intro ρ σ env s covers
    obtain ⟨test, b, middle, mt, ht, rt⟩ := ihGuard ρ σ env s covers
    change test = .bool b at rt
    subst test
    have first := steps_under (fun e => .cond e (yes.subst σ) (no.subst σ)) (fun h => .ifStep h) ht
    cases b
    · obtain ⟨v, value, finish, mr, hr, rr⟩ := ihNo ρ σ env middle (steps_cover ht covers)
      exact ⟨v, value, finish, bind_run mt mr, (first.tail .ifFalse).trans hr, rr⟩
    · obtain ⟨v, value, finish, mr, hr, rr⟩ := ihYes ρ σ env middle (steps_cover ht covers)
      exact ⟨v, value, finish, bind_run mt mr, (first.tail .ifTrue).trans hr, rr⟩
  | @seq _ left right T ld rd ihLeft ihRight =>
    intro ρ σ env s covers
    obtain ⟨lv, a, middle, ml, hl, rl⟩ := ihLeft ρ σ env s covers
    change lv = .skip at rl
    subst lv
    obtain ⟨v, value, finish, mr, hr, rr⟩ := ihRight ρ σ env middle (steps_cover hl covers)
    have first := steps_under (fun e => .seq e (right.subst σ)) (fun h => .seqStep h) hl
    exact ⟨v, value, finish, bind_run ml mr, (first.tail .seqSkip).trans hr, rr⟩
  | lam body ih =>
    intro ρ σ env s covers
    refine ⟨_, _, s, pure_run _ s, .refl, ⟨_, rfl, ?_⟩⟩
    intro arg a argument store covered
    rw [beta_after_subst]
    exact ih (ρ.push a) (extendSubst arg σ) (env.push argument) store covered
  | @app _ fn arg A B fd ad ihFn ihArg =>
    intro ρ σ env s covers
    obtain ⟨closure, f, afterFn, mf, hf, rf⟩ := ihFn ρ σ env s covers
    have coversFn : Covers locations afterFn := steps_cover hf covers
    obtain ⟨argument, a, afterArg, ma, ha, ra⟩ := ihArg ρ σ env afterFn coversFn
    obtain ⟨body, rfl, applyClosure⟩ := rf
    obtain ⟨v, value, finish, mr, hr, rr⟩ :=
      applyClosure argument a ra afterArg (steps_cover ha coversFn)
    have first := steps_under (fun e => .app e (arg.subst σ)) (fun h => .appLeft h) hf
    have second := steps_under (Expr.app (.lam A body)) (fun h => .appRight (.lam A body) h) ha
    exact ⟨v, value, finish, bind_run mf (bind_run ma mr),
      ((first.trans second).tail (.appFun ra.isValue)).trans hr, rr⟩
  | @letE _ value body A B vd bd ihValue ihBody =>
    intro ρ σ env s covers
    obtain ⟨argument, a, afterValue, mv, hv, rv⟩ := ihValue ρ σ env s covers
    obtain ⟨v, result, finish, mr, hr, rr⟩ :=
      ihBody (ρ.push a) (extendSubst argument σ) (env.push rv) afterValue (steps_cover hv covers)
    rw [← beta_after_subst] at hr
    have first := steps_under (fun e => .letE A e (body.subst (Expr.liftSubst σ)))
      (fun h => .letStep h) hv
    exact ⟨v, result, finish, bind_run mv mr, (first.tail (.letValue rv.isValue)).trans hr, rr⟩
  | @deref _ loc present =>
    intro ρ σ env s covers
    obtain ⟨n, found⟩ := Finmap.mem_iff.mp (covers loc present)
    exact ⟨.int n, n, s, read_run found, .single (.deref found), rfl⟩
  | @assign _ loc _ present _ ih =>
    intro ρ σ env s covers
    obtain ⟨v, n, afterRhs, mr, hr, rr⟩ := ih ρ σ env s covers
    change v = .int n at rr
    subst v
    have allocated := (steps_cover hr covers) loc present
    have rhs := steps_under (Expr.assign loc) (fun h => .assignStep h) hr
    exact ⟨.skip, (), afterRhs.insert loc n, bind_run mr (write_run allocated),
      rhs.tail (.assignValue allocated), rfl⟩

private theorem realizes_closed {locations : L1.TypeEnv} {e : Expr} {T : Ty}
    (term : Term locations [] e T) {s : Store} (covers : Covers locations s) :
    ∃ result value finalStore, (value, finalStore) ∈ (term.denote LexicalEnv.empty).run s ∧
      Steps ⟨e, s⟩ ⟨result, finalStore⟩ ∧ Related locations T result value := by
  have empty : EnvRelated locations LexicalEnv.empty Expr.bvar := by
    intro index T lookup
    simp at lookup
  simpa only [Expr.subst_id] using realizes term LexicalEnv.empty Expr.bvar empty s covers

/-- Every closed, covered term in this fragment reaches a value. -/
theorem Term.terminates {locations : L1.TypeEnv} {e : Expr} {T : Ty}
    (term : Term locations [] e T) {s : Store} (covers : Covers locations s) :
    ∃ result, Steps ⟨e, s⟩ result ∧ IsValue result.expr := by
  obtain ⟨_, _, _, _, run, related⟩ := realizes_closed term covers
  exact ⟨_, run, related.isValue⟩

/-- Membership in the denotational ground observation agrees exactly with
finite CBV return, including the final store. -/
theorem Term.adequate {locations : L1.TypeEnv} {e : Expr} {T : Ty} (term : Term locations [] e T)
    (ground : Ground T) {s : Store} (covers : Covers locations s) (result : Config) :
    result ∈ term.observe ground s ↔ Steps ⟨e, s⟩ result ∧ IsValue result.expr := by
  obtain ⟨v, value, finish, mem, path, related⟩ := realizes_closed term covers
  have quoted : v = quoteGround ground value := by cases ground <;> exact related
  subst v
  let target : Config := ⟨quoteGround ground value, finish⟩
  have observed : target ∈ term.observe ground s := Part.mem_map _ mem
  have valueForm : IsValue target.expr := related.isValue
  constructor
  · intro seen
    have same := Part.mem_unique seen observed
    rw [same]
    exact ⟨path, valueForm⟩
  · rintro ⟨run, isValue⟩
    cases result
    have same := RightUnique.reach_final_eq stepRightUnique run path
      (value_terminal isValue) (value_terminal valueForm)
    rw [same]
    exact observed

end Silmaril.Courses.Cambridge.L2.EffectfulDenotation
