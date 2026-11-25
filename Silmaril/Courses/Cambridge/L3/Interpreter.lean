module

public import Silmaril.Courses.Cambridge.L3.Reduction

/-! # Executable L3 reduction (§5.5)

The interpreter follows the direct rules, including their location premise for
right-hand assignment steps. It chooses a fresh address above the current store
domain. Every selected step is permitted, and a step is selected whenever the
relation has a successor.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

private theorem IsValue.no_step {e : Expr} (value : IsValue e) {s : Store}
    {next : Config} : ¬ Step ⟨e, s⟩ next := by
  induction value generalizing s next with
  | int | bool | skip | loc | lam =>
      intro step
      cases step
  | pair left right ihLeft ihRight =>
      intro step
      cases step with
      | pairLeft inner => exact ihLeft inner
      | pairRight _ inner => exact ihRight inner
  | inl value ih =>
      intro step
      cases step with
      | inl inner => exact ih inner
  | inr value ih =>
      intro step
      cases step with
      | inr inner => exact ih inner
  | record ready ih =>
      intro step
      cases step with
      | recordStep i _ inner => exact ih i inner

private inductive Reduction (e : Expr) (s : Store) : Type where
  | value (ready : IsValue e)
  | step (next : Config) (valid : Step ⟨e, s⟩ next)
  | stuck (blocked : Stuck ⟨e, s⟩)

/-- After consuming a prefix of values, inspect the next field only. -/
private def reduceRecord (labels : RecordLabels) (fields : labels.Index → Expr) (s : Store)
    (inspect : ∀ i, Reduction (fields i) s) : (remaining : Nat) →
    (bound : remaining ≤ labels.names.length) →
    (prior : ∀ j : labels.Index, j.val < labels.names.length - remaining →
      IsValue (fields j)) → Reduction (.record labels fields) s
  | 0, _, prior => .value (.record (fun j => prior j (by simpa only [Nat.sub_zero] using j.isLt)))
  | remaining + 1, bound, prior =>
      let i : labels.Index := ⟨labels.names.length - (remaining + 1), by omega⟩
      match inspect i with
      | .value ready =>
          reduceRecord labels fields s inspect remaining (by omega) (by
            intro j earlier
            by_cases same : j = i
            · exact same ▸ ready
            · apply prior
              have different : j.val ≠ i.val := fun eq => same (Fin.ext eq)
              dsimp [i] at different
              omega)
      | .step ⟨e', s'⟩ valid =>
          .step ⟨.record labels (Function.update fields i e'), s'⟩
            (.recordStep i (fun j earlier => prior j earlier) valid)
      | .stuck blocked =>
          .stuck ⟨(by intro ready; cases ready with | record all => exact blocked.1 (all i)),
            fun next step => by
              cases step with
              | recordStep j earlier inner =>
                  rcases Nat.lt_trichotomy j.val i.val with before | equal | after
                  · exact (prior j before).no_step inner
                  · obtain rfl := Fin.ext equal
                    exact blocked.2 _ inner
                  · exact blocked.1 (earlier i after)⟩

private def reduceBinaryValues (s : Store) (left : Expr) (op : Op) (right : Expr)
    (vl : IsValue left) (vr : IsValue right) :
    Reduction (.binary left op right) s := by
  have invalid {e₁ e₂ : Expr} (h₁ : IsValue e₁) (h₂ : IsValue e₂)
      (notInts : ∀ a b, e₁ = .int a → e₂ = .int b → False) :
      Stuck ⟨.binary e₁ op e₂, s⟩ := by
    refine ⟨(by intro value; cases value), ?_⟩
    intro _ step
    cases step with
    | add a b | ge a b => exact notInts a b rfl rfl
    | binaryLeft inner => exact h₁.no_step inner
    | binaryRight _ inner => exact h₂.no_step inner
  cases left
  case int a =>
    cases right
    case int b =>
      cases op
      · exact .step ⟨.int (a + b), s⟩ (.add a b s)
      · exact .step ⟨.bool (a ≥ b), s⟩ (.ge a b s)
    all_goals exact .stuck (invalid vl vr (by intros; contradiction))
  all_goals exact .stuck (invalid vl vr (by intros; contradiction))

private def reduceCondValue (s : Store) (test yes no : Expr) (ready : IsValue test) :
    Reduction (.cond test yes no) s := by
  cases test
  case bool b =>
    cases b
    · exact .step ⟨no, s⟩ .ifFalse
    · exact .step ⟨yes, s⟩ .ifTrue
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | ifStep inner => exact ready.no_step inner⟩

private def reduceSeqValue (s : Store) (left right : Expr) (ready : IsValue left) :
    Reduction (.seq left right) s := by
  cases left
  case skip => exact .step ⟨right, s⟩ .seqSkip
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | seqStep inner => exact ready.no_step inner⟩

private def reduceAppValues (s : Store) (fn arg : Expr) (vf : IsValue fn)
    (va : IsValue arg) : Reduction (.app fn arg) s := by
  cases fn
  case lam domain body => exact .step ⟨body.beta arg, s⟩ (.appFun va)
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | appLeft inner => exact vf.no_step inner
      | appRight _ inner => exact va.no_step inner⟩

private def reduceFstValue (s : Store) (e : Expr) (ready : IsValue e) :
    Reduction (.fst e) s := by
  cases e
  case pair left right =>
    exact .step ⟨left, s⟩ (by cases ready with | pair vl vr => exact .fstValue vl vr)
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | fstStep inner => exact ready.no_step inner⟩

private def reduceSndValue (s : Store) (e : Expr) (ready : IsValue e) :
    Reduction (.snd e) s := by
  cases e
  case pair left right =>
    exact .step ⟨right, s⟩ (by cases ready with | pair vl vr => exact .sndValue vl vr)
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | sndStep inner => exact ready.no_step inner⟩

private def reduceMatchValue (s : Store) (e : Expr) (A : Ty) (left : Expr)
    (B : Ty) (right : Expr) (ready : IsValue e) :
    Reduction (.matchSum e A left B right) s := by
  cases e
  case inl payload T =>
    exact .step ⟨left.beta payload, s⟩ (by cases ready with | inl vp => exact .matchLeft vp)
  case inr payload T =>
    exact .step ⟨right.beta payload, s⟩ (by cases ready with | inr vp => exact .matchRight vp)
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | matchStep inner => exact ready.no_step inner⟩

private def reduceProjectValue (s : Store) (e : Expr) (label : Label) (ready : IsValue e) :
    Reduction (.project e label) s := by
  cases e
  case record labels fields =>
    match found : labels.names.findFinIdx? (· == label) with
    | some i =>
        have eq : labels.label i = label :=
          beq_iff_eq.mp (List.findFinIdx?_eq_some_iff.mp found).1
        exact .step ⟨fields i, s⟩ (by
          rw [← eq]
          cases ready with
          | record all => exact .projectValue i all)
    | none =>
        exact .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | projectStep inner => exact ready.no_step inner
          | projectValue i all =>
              exact List.findFinIdx?_eq_none_iff.mp found (labels.label i)
                (List.get_mem labels.names i) (beq_self_eq_true _)⟩
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | projectStep inner => exact ready.no_step inner⟩

private def reduceDerefValue (s : Store) (e : Expr) (ready : IsValue e) :
    Reduction (.deref e) s := by
  cases e
  case loc loc =>
    match found : s.lookup loc with
    | some value => exact .step ⟨value.val, s⟩ (.derefValue found)
    | none =>
        exact .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | derefValue present => rw [present] at found; contradiction
          | derefStep inner => exact ready.no_step inner⟩
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | derefStep inner => exact ready.no_step inner⟩

private def reduceAssignValue (s : Store) (lhs rhs : Expr) (ready : IsValue lhs)
    (inspect : Unit → Reduction rhs s) : Reduction (.assign lhs rhs) s := by
  cases lhs
  case loc loc =>
    match inspect () with
    | .step next valid => exact .step ⟨.assign (.loc loc) next.expr, next.store⟩ (.assignRight valid)
    | .value value =>
        if present : loc ∈ s then
          exact .step ⟨.skip, s.insert loc ⟨rhs, value⟩⟩ (.assignValue ⟨rhs, value⟩ present)
        else
          exact .stuck ⟨(by intro value; cases value), fun _ step => by
            cases step with
            | assignValue _ allocated => exact present allocated
            | assignLeft inner => exact ready.no_step inner
            | assignRight inner => exact value.no_step inner⟩
    | .stuck blocked =>
        exact .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | assignValue value _ => exact blocked.1 value.property
          | assignLeft inner => exact ready.no_step inner
          | assignRight inner => exact blocked.2 _ inner⟩
  all_goals
    exact .stuck ⟨(by intro value; cases value), fun _ step => by
      cases step with
      | assignLeft inner => exact ready.no_step inner⟩

private def classify (s : Store) : (e : Expr) → Reduction e s
  | .int n => .value (.int n)
  | .bool b => .value (.bool b)
  | .skip => .value .skip
  | .loc loc => .value (.loc loc)
  | .lam domain body => .value (.lam domain body)
  | .bvar _ | .fvar _ => .stuck ⟨(by intro value; cases value), fun _ step => by cases step⟩
  | .binary left op right =>
      match classify s left with
      | .step next valid => .step ⟨.binary next.expr op right, next.store⟩ (.binaryLeft valid)
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | add a _ | ge a _ => exact blocked.1 (.int a)
          | binaryLeft inner => exact blocked.2 _ inner
          | binaryRight value _ => exact blocked.1 value⟩
      | .value leftValue =>
          match classify s right with
          | .step next valid =>
              .step ⟨.binary left op next.expr, next.store⟩ (.binaryRight leftValue valid)
          | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
              cases step with
              | add _ b | ge _ b => exact blocked.1 (.int b)
              | binaryLeft inner => exact leftValue.no_step inner
              | binaryRight _ inner => exact blocked.2 _ inner⟩
          | .value rightValue => reduceBinaryValues s left op right leftValue rightValue
  | .cond test yes no =>
      match classify s test with
      | .step next valid => .step ⟨.cond next.expr yes no, next.store⟩ (.ifStep valid)
      | .value ready => reduceCondValue s test yes no ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | ifTrue => exact blocked.1 (.bool true)
          | ifFalse => exact blocked.1 (.bool false)
          | ifStep inner => exact blocked.2 _ inner⟩
  | .seq left right =>
      match classify s left with
      | .step next valid => .step ⟨.seq next.expr right, next.store⟩ (.seqStep valid)
      | .value ready => reduceSeqValue s left right ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | seqSkip => exact blocked.1 .skip
          | seqStep inner => exact blocked.2 _ inner⟩
  | .loop test body => .step ⟨.cond test (.seq body (.loop test body)) .skip, s⟩ .while
  | .app fn arg =>
      match classify s fn with
      | .step next valid => .step ⟨.app next.expr arg, next.store⟩ (.appLeft valid)
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | appFun _ => exact blocked.1 (.lam _ _)
          | appLeft inner => exact blocked.2 _ inner
          | appRight value _ => exact blocked.1 value⟩
      | .value fnValue =>
          match classify s arg with
          | .step next valid => .step ⟨.app fn next.expr, next.store⟩ (.appRight fnValue valid)
          | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
              cases step with
              | appFun value => exact blocked.1 value
              | appLeft inner => exact fnValue.no_step inner
              | appRight _ inner => exact blocked.2 _ inner⟩
          | .value argValue => reduceAppValues s fn arg fnValue argValue
  | .letE T e body =>
      match classify s e with
      | .step next valid => .step ⟨.letE T next.expr body, next.store⟩ (.letStep valid)
      | .value ready => .step ⟨body.beta e, s⟩ (.letValue ready)
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | letValue value => exact blocked.1 value
          | letStep inner => exact blocked.2 _ inner⟩
  | .letRecFun domain codomain fn body =>
      .step ⟨body.beta (Expr.recClosure domain codomain fn), s⟩ .letRecFun
  | .pair left right =>
      match classify s left with
      | .step next valid => .step ⟨.pair next.expr right, next.store⟩ (.pairLeft valid)
      | .stuck blocked => .stuck ⟨(by
          intro value
          cases value with
          | pair vl _ => exact blocked.1 vl), fun _ step => by
          cases step with
          | pairLeft inner => exact blocked.2 _ inner
          | pairRight value _ => exact blocked.1 value⟩
      | .value leftValue =>
          match classify s right with
          | .step next valid => .step ⟨.pair left next.expr, next.store⟩ (.pairRight leftValue valid)
          | .value rightValue => .value (.pair leftValue rightValue)
          | .stuck blocked => .stuck ⟨(by
              intro value
              cases value with
              | pair _ vr => exact blocked.1 vr), fun _ step => by
              cases step with
              | pairLeft inner => exact leftValue.no_step inner
              | pairRight _ inner => exact blocked.2 _ inner⟩
  | .fst e =>
      match classify s e with
      | .step next valid => .step ⟨.fst next.expr, next.store⟩ (.fstStep valid)
      | .value ready => reduceFstValue s e ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | fstValue vl vr => exact blocked.1 (.pair vl vr)
          | fstStep inner => exact blocked.2 _ inner⟩
  | .snd e =>
      match classify s e with
      | .step next valid => .step ⟨.snd next.expr, next.store⟩ (.sndStep valid)
      | .value ready => reduceSndValue s e ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | sndValue vl vr => exact blocked.1 (.pair vl vr)
          | sndStep inner => exact blocked.2 _ inner⟩
  | .inl e T =>
      match classify s e with
      | .step next valid => .step ⟨.inl next.expr T, next.store⟩ (.inl valid)
      | .value ready => .value (.inl ready)
      | .stuck blocked => .stuck ⟨(by
          intro value
          cases value with
          | inl inner => exact blocked.1 inner), fun _ step => by
          cases step with
          | inl inner => exact blocked.2 _ inner⟩
  | .inr e T =>
      match classify s e with
      | .step next valid => .step ⟨.inr next.expr T, next.store⟩ (.inr valid)
      | .value ready => .value (.inr ready)
      | .stuck blocked => .stuck ⟨(by
          intro value
          cases value with
          | inr inner => exact blocked.1 inner), fun _ step => by
          cases step with
          | inr inner => exact blocked.2 _ inner⟩
  | .matchSum e A left B right =>
      match classify s e with
      | .step next valid => .step ⟨.matchSum next.expr A left B right, next.store⟩ (.matchStep valid)
      | .value ready => reduceMatchValue s e A left B right ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | matchLeft value => exact blocked.1 (.inl value)
          | matchRight value => exact blocked.1 (.inr value)
          | matchStep inner => exact blocked.2 _ inner⟩
  | .record labels fields =>
      reduceRecord labels fields s (fun i => classify s (fields i)) labels.names.length
        (Nat.le_refl _) (by simp)
  | .project e label =>
      match classify s e with
      | .step next valid => .step ⟨.project next.expr label, next.store⟩ (.projectStep valid)
      | .value ready => reduceProjectValue s e label ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | projectValue _ ready => exact blocked.1 (.record ready)
          | projectStep inner => exact blocked.2 _ inner⟩
  | .ref e =>
      match classify s e with
      | .step next valid => .step ⟨.ref next.expr, next.store⟩ (.refStep valid)
      | .value ready =>
          .step ⟨.loc s.freshAddress, s.insert s.freshAddress ⟨e, ready⟩⟩
            (.refValue ⟨e, ready⟩ s.freshAddress_not_mem)
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | refValue value _ => exact blocked.1 value.property
          | refStep inner => exact blocked.2 _ inner⟩
  | .deref e =>
      match classify s e with
      | .step next valid => .step ⟨.deref next.expr, next.store⟩ (.derefStep valid)
      | .value ready => reduceDerefValue s e ready
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | derefValue _ => exact blocked.1 (.loc _)
          | derefStep inner => exact blocked.2 _ inner⟩
  | .assign lhs rhs =>
      match classify s lhs with
      | .step next valid => .step ⟨.assign next.expr rhs, next.store⟩ (.assignLeft valid)
      | .value ready => reduceAssignValue s lhs rhs ready (fun _ => classify s rhs)
      | .stuck blocked => .stuck ⟨(by intro value; cases value), fun _ step => by
          cases step with
          | assignValue _ _ | assignRight _ => exact blocked.1 (.loc _)
          | assignLeft inner => exact blocked.2 _ inner⟩
termination_by structural e => e

/-- Select a permitted successor of a configuration, if one exists. -/
@[no_expose] def Config.reduce (before : Config) : Option Config :=
  match classify before.store before.expr with
  | .step next _ => some next
  | .value _ | .stuck _ => none

theorem Config.reduce_sound {before after : Config} (result : before.reduce = some after) :
    Step before after := by
  unfold Config.reduce at result
  split at result
  · cases result
    exact ‹Step _ _›
  · contradiction
  · contradiction

/-- Failure to select a step is equivalent to absence of any permitted step. -/
theorem Config.reduce_eq_none_iff_terminal {before : Config} :
    before.reduce = none ↔ ∀ after, ¬ Step before after := by
  unfold Config.reduce
  split
  · rename_i next valid _
    constructor
    · intro impossible
      contradiction
    · intro terminal
      exact (terminal next valid).elim
  · exact ⟨fun _ _ step => (show IsValue before.expr from by assumption).no_step step,
      fun _ => rfl⟩
  · exact ⟨fun _ => (show Stuck before from by assumption).2, fun _ => rfl⟩

theorem Config.reduce_exists_iff_step_exists {before : Config} :
    (∃ after, before.reduce = some after) ↔ ∃ after, Step before after := by
  constructor
  · rintro ⟨after, reduced⟩
    exact ⟨after, before.reduce_sound reduced⟩
  · rintro ⟨after, step⟩
    cases result : before.reduce with
    | none => exact (reduce_eq_none_iff_terminal.mp result after step).elim
    | some next => exact ⟨next, rfl⟩

-- Both addresses are legal in the direct rules. Executable allocation chooses 1.
example : Config.reduce ⟨.ref (.int 0), ∅⟩ =
    some ⟨.loc 1, (∅ : Store).insert 1 ⟨.int 0, .int 0⟩⟩ := rfl

example : Step ⟨.ref (.int 0), ∅⟩ ⟨.loc 0, (∅ : Store).insert 0 ⟨.int 0, .int 0⟩⟩ :=
  .refValue ⟨.int 0, .int 0⟩ Finmap.notMem_empty

example : Config.reduce ⟨.assign (.int 0) (.ref (.int 1)), ∅⟩ = none := rfl

end Silmaril.Courses.Cambridge.L3
