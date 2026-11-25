module

public import Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Defs
import Silmaril.Courses.Cambridge.L1.Metatheory.Determinacy

/-! Finite denotational outcomes construct small-step paths. In the loop
case, one iteration either reaches a terminal configuration or reaches the
loop again at the new store. Conversely, reduction preserves the denotation
and every terminal configuration has a defined outcome. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.EffectfulDenotational

open Silmaril.Elgot

private def ValueAt (value : Expr) (c : Config) : Prop :=
  c.expr = value ∧ IsValue value

private def Sound {α : Type} (m : Computation α) (e : Expr) (returns : α → Config → Prop) : Prop :=
  ∀ ⦃s t : Store⦄ ⦃result : Except Unit α⦄, (result, t) ∈ run m s →
    ∃ out : Expr, Steps ⟨e, s⟩ ⟨out, t⟩ ∧
      match result with
      | .ok a => returns a ⟨out, t⟩
      | .error () => Stuck ⟨out, t⟩

private theorem pure_sound {α : Type} {e : Expr} {a : α} {returns : α → Config → Prop}
    (h : ∀ s, returns a ⟨e, s⟩) : Sound (pure a) e returns := by
  intro s t result member
  rw [run_pure, Part.mem_some_iff] at member
  cases member
  exact ⟨e, .refl, h s⟩

private theorem throw_sound {α : Type} {e : Expr} {returns : α → Config → Prop}
    (h : ∀ s, Stuck ⟨e, s⟩) : Sound (throw ()) e returns := by
  intro s t result member
  rw [run_throw, Part.mem_some_iff] at member
  cases member
  exact ⟨e, .refl, h s⟩

private theorem Sound.prepend {α : Type} {m : Computation α} {e e' : Expr}
    {returns : α → Config → Prop} (sound : Sound m e' returns)
    (step : ∀ s, Step ⟨e, s⟩ ⟨e', s⟩) : Sound m e returns := by
  intro s t result member
  obtain ⟨out, path, h⟩ := sound member
  exact ⟨out, path.head (step s), h⟩

/-- A continuation runs after its operand has produced a value. If the
operand is stuck, the surrounding frame must be stuck too. -/
private theorem bind_sound {α : Type} {m : Computation Expr} {k : Expr → Computation α}
    {e : Expr} {returns : α → Config → Prop} (frame : Expr → Expr) (head : Sound m e ValueAt)
    (lifts : ∀ {a b : Expr} {s t : Store}, Step ⟨a, s⟩ ⟨b, t⟩ →
      Step ⟨frame a, s⟩ ⟨frame b, t⟩)
    (stuck_frame : ∀ {a : Expr} {s : Store}, Stuck ⟨a, s⟩ → Stuck ⟨frame a, s⟩)
    (cont : ∀ v, IsValue v → Sound (k v) (frame v) returns) :
    Sound (m >>= k) (frame e) returns := by
  intro s t result member
  rw [run_bind, Part.mem_bind_iff] at member
  obtain ⟨⟨first, middle⟩, firstMem, restMem⟩ := member
  obtain ⟨v, firstPath, finished⟩ := head firstMem
  have framedPath := Relation.ReflTransGen.lift
    (fun c : Config => (⟨frame c.expr, c.store⟩ : Config))
    (fun ⟨_, _⟩ ⟨_, _⟩ step => lifts step) _ _ firstPath
  cases first with
  | error error =>
      cases error
      change (result, t) ∈ Part.some (.error (), middle) at restMem
      cases Part.mem_some_iff.mp restMem
      exact ⟨frame v, framedPath, stuck_frame finished⟩
  | ok value =>
      obtain ⟨equal, isValue⟩ := finished
      change v = value at equal
      subst v
      obtain ⟨out, path, h⟩ := cont value isValue restMem
      exact ⟨out, framedPath.trans path, h⟩

private theorem stuck_binaryLeft {l r : Expr} {op : Op} {s : Store}
    (stuck : Stuck ⟨l, s⟩) : Stuck ⟨.binary l op r, s⟩ := by
  refine ⟨(fun v => by cases v), ?_⟩
  intro next step
  cases step with
  | add | ge => exact stuck.1 (.int _)
  | binaryLeft inner => exact stuck.2 _ inner
  | binaryRight value _ => exact stuck.1 value

private theorem stuck_binaryRight {l r : Expr} {op : Op} {s : Store}
    (value : IsValue l) (stuck : Stuck ⟨r, s⟩) : Stuck ⟨.binary l op r, s⟩ := by
  refine ⟨(fun v => by cases v), ?_⟩
  intro next step
  cases step with
  | add | ge => exact stuck.1 (.int _)
  | binaryLeft inner => exact value_terminal value _ inner
  | binaryRight _ inner => exact stuck.2 _ inner

private theorem stuck_assign {loc : Loc} {e : Expr} {s : Store}
    (stuck : Stuck ⟨e, s⟩) : Stuck ⟨.assign loc e, s⟩ := by
  refine ⟨(fun v => by cases v), ?_⟩
  intro next step
  cases step with
  | assignValue => exact stuck.1 (.int _)
  | assignStep inner => exact stuck.2 _ inner

private theorem stuck_cond {test yes no : Expr} {s : Store}
    (stuck : Stuck ⟨test, s⟩) : Stuck ⟨.cond test yes no, s⟩ := by
  refine ⟨(fun v => by cases v), ?_⟩
  intro next step
  cases step with
  | ifTrue | ifFalse => exact stuck.1 (.bool _)
  | ifStep inner => exact stuck.2 _ inner

private theorem stuck_seq {first second : Expr} {s : Store}
    (stuck : Stuck ⟨first, s⟩) : Stuck ⟨.seq first second, s⟩ := by
  refine ⟨(fun v => by cases v), ?_⟩
  intro next step
  cases step with
  | seqSkip => exact stuck.1 .skip
  | seqStep inner => exact stuck.2 _ inner

private theorem read_sound (loc : Loc) : Sound (read loc) (.deref loc) ValueAt := by
  intro s t result member
  cases lookup : s.lookup loc with
  | some n =>
      simp only [run_read, lookup, Part.mem_some_iff] at member
      cases member
      exact ⟨.int n, .single (.deref lookup), rfl, .int n⟩
  | none =>
      simp only [run_read, lookup, Part.mem_some_iff] at member
      cases member
      refine ⟨.deref loc, .refl, (fun v => by cases v), ?_⟩
      intro next step
      cases step with
      | deref present => rw [lookup] at present; cases present

private theorem assign_sound (loc : Loc) {v : Expr} (value : IsValue v) :
    Sound (assign loc v) (.assign loc v) ValueAt := by
  cases value with
  | int n =>
      intro s t result member
      by_cases allocated : loc ∈ s
      · simp only [assign, run_write, Store.update_eq_some _ _ _ allocated, Part.mem_some_iff]
          at member
        cases member
        exact ⟨.skip, .single (.assignValue allocated), rfl, .skip⟩
      · simp only [assign, run_write, Store.update_eq_none _ _ _ allocated, Part.mem_some_iff]
          at member
        cases member
        refine ⟨.assign loc (.int n), .refl, (fun v => by cases v), ?_⟩
        intro next step
        cases step with
        | assignValue present => exact allocated present
        | assignStep inner => cases inner
  | bool | skip =>
      apply throw_sound
      intro s
      refine ⟨(fun v => by cases v), ?_⟩
      intro next step
      cases step with
      | assignStep inner => cases inner

private theorem binary_sound (op : Op) {l r : Expr} (left : IsValue l) (right : IsValue r) :
    Sound (binary op l r) (.binary l op r) ValueAt := by
  cases left <;> cases right
  case int.int a b =>
    cases op with
    | add => exact (pure_sound fun _ => ⟨rfl, IsValue.int _⟩).prepend fun s => .add a b s
    | ge => exact (pure_sound fun _ => ⟨rfl, IsValue.bool _⟩).prepend fun s => .ge a b s
  all_goals
    apply throw_sound
    intro s
    refine ⟨(fun v => by cases v), ?_⟩
    intro next step
    cases step with
    | binaryLeft inner => cases inner
    | binaryRight _ inner => cases inner

private theorem branch_sound {α : Type} {yes no : Expr} {m n : Computation α}
    {returns : α → Config → Prop} {v : Expr} (value : IsValue v)
    (left : Sound m yes returns) (right : Sound n no returns) :
    Sound (branch m n v) (.cond v yes no) returns := by
  cases value with
  | bool b =>
      cases b with
      | false => exact right.prepend fun _ => .ifFalse
      | true => exact left.prepend fun _ => .ifTrue
  | int | skip =>
      apply throw_sound
      intro s
      refine ⟨(fun v => by cases v), ?_⟩
      intro next step
      cases step with
      | ifStep inner => cases inner

private theorem afterSkip_sound {α : Type} {second : Expr} {m : Computation α}
    {returns : α → Config → Prop} {v : Expr} (value : IsValue v)
    (sound : Sound m second returns) : Sound (afterSkip m v) (.seq v second) returns := by
  cases value with
  | skip => exact sound.prepend fun _ => .seqSkip
  | int | bool =>
      apply throw_sound
      intro s
      refine ⟨(fun v => by cases v), ?_⟩
      intro next step
      cases step with
      | seqStep inner => cases inner

private def LoopReturn (test body : Expr) (a : Expr ⊕ Unit) (c : Config) : Prop :=
  match a with
  | .inl v => ValueAt v c
  | .inr () => c.expr = .loop test body

private theorem whileBody_sound {test body : Expr} (guard : Sound (denote test) test ValueAt)
    (command : Sound (denote body) body ValueAt) :
    Sound (whileBody (denote test) (denote body) ()) (.loop test body) (LoopReturn test body) := by
  apply Sound.prepend _ (fun _ => Step.while)
  apply bind_sound (fun e => .cond e (.seq body (.loop test body)) .skip) guard
    (fun step => .ifStep step) (fun h => stuck_cond h)
  intro v value
  apply branch_sound value _ (pure_sound fun _ => ⟨rfl, .skip⟩)
  apply bind_sound (fun e => .seq e (.loop test body)) command
    (fun step => .seqStep step) (fun h => stuck_seq h)
  intro v value
  exact afterSkip_sound value (pure_sound fun _ => rfl)

private noncomputable def loopStep (test body : Expr) : Unit × Store →
    Part ((Except Unit Expr × Store) ⊕ (Unit × Store)) :=
  Elgot.StateT.body (Elgot.ExceptT.body (whileBody (denote test) (denote body)))

private theorem loopStep_mem {test body : Expr} {s : Store}
    {out : (Except Unit Expr × Store) ⊕ (Unit × Store)} (h : out ∈ loopStep test body ((), s)) :
    ∃ (result : Except Unit (Expr ⊕ Unit)) (t : Store),
      (result, t) ∈ run (whileBody (denote test) (denote body) ()) s ∧
        out = Elgot.StateT.distribute (Elgot.ExceptT.distribute result, t) := by
  change out ∈ ((((whileBody (denote test) (denote body) ()).run >>=
    pure ∘ Elgot.ExceptT.distribute).run s).bind fun r => Part.some (Elgot.StateT.distribute r)) at h
  rw [_root_.StateT.run_bind, Part.mem_bind_iff] at h
  obtain ⟨mid, middle, final⟩ := h
  change mid ∈ (run (whileBody (denote test) (denote body) ()) s).bind
    (fun (result, t) => Part.some (Elgot.ExceptT.distribute result, t)) at middle
  obtain ⟨⟨result, t⟩, member, midEq⟩ := Part.mem_bind_iff.mp middle
  have equal := Part.mem_some_iff.mp midEq
  subst mid
  exact ⟨result, t, member, Part.mem_some_iff.mp final⟩

private theorem loop_runs_sound {test body : Expr}
    (sound : Sound (whileBody (denote test) (denote body) ()) (.loop test body)
      (LoopReturn test body))
    {start : Unit × Store} {finish : Except Unit Expr × Store}
    (runs : Elgot.Part.Runs (loopStep test body) start finish) :
    ∃ out : Expr, Steps ⟨.loop test body, start.2⟩ ⟨out, finish.2⟩ ∧
      match finish.1 with
      | .ok v => ValueAt v ⟨out, finish.2⟩
      | .error () => Stuck ⟨out, finish.2⟩ := by
  induction runs with
  | @done start finish step =>
      rcases start with ⟨⟨⟩, s⟩
      obtain ⟨result, t, member, equal⟩ := loopStep_mem step
      obtain ⟨out, path, returned⟩ := sound member
      cases result with
      | error error =>
          cases error
          cases equal
          exact ⟨out, path, returned⟩
      | ok result =>
          cases result with
          | inl v => cases equal; exact ⟨out, path, returned⟩
          | inr u => cases u; cases equal
  | @more start middle finish step _ ih =>
      rcases start with ⟨⟨⟩, s⟩
      obtain ⟨result, t, member, equal⟩ := loopStep_mem step
      obtain ⟨out, path, returned⟩ := sound member
      cases result with
      | error error => cases error; cases equal
      | ok result =>
          cases result with
          | inl v => cases equal
          | inr u =>
              cases u
              cases equal
              change out = .loop test body at returned
              subst out
              obtain ⟨lastExpr, tail, lastResult⟩ := ih
              exact ⟨lastExpr, path.trans tail, lastResult⟩

private theorem loop_sound {test body : Expr} (guard : Sound (denote test) test ValueAt)
    (command : Sound (denote body) body ValueAt) :
    Sound (denote (.loop test body)) (.loop test body) ValueAt := by
  intro s t result member
  change (result, t) ∈ iter (loopStep test body) ((), s) at member
  cases result <;> exact
    loop_runs_sound (whileBody_sound guard command) ((Elgot.Part.mem_iter_iff _ _ _).mp member)

private theorem denote_sound (e : Expr) : Sound (denote e) e ValueAt := by
  induction e with
  | int n => exact pure_sound fun _ => ⟨rfl, .int n⟩
  | bool b => exact pure_sound fun _ => ⟨rfl, .bool b⟩
  | skip => exact pure_sound fun _ => ⟨rfl, .skip⟩
  | deref loc => exact read_sound loc
  | assign loc e ih =>
      exact bind_sound (.assign loc) ih (fun step => .assignStep step)
        (fun h => stuck_assign h) (fun _ value => assign_sound loc value)
  | binary l op r ihLeft ihRight =>
      apply bind_sound (fun e => .binary e op r) ihLeft (fun step => .binaryLeft step)
        (fun h => stuck_binaryLeft h)
      intro lv left
      exact bind_sound (.binary lv op) ihRight (fun step => .binaryRight left step)
        (fun h => stuck_binaryRight left h) (fun _ right => binary_sound op left right)
  | cond test yes no ihTest ihYes ihNo =>
      exact bind_sound (fun e => .cond e yes no) ihTest (fun step => .ifStep step)
        (fun h => stuck_cond h) (fun _ value => branch_sound value ihYes ihNo)
  | seq first second ihFirst ihSecond =>
      exact bind_sound (fun e => .seq e second) ihFirst (fun step => .seqStep step)
        (fun h => stuck_seq h) (fun _ value => afterSkip_sound value ihSecond)
  | loop test body ihTest ihBody => exact loop_sound ihTest ihBody

theorem steps_preserves {source target : Config} (path : Steps source target) :
    run (denote source.expr) source.store = run (denote target.expr) target.store := by
  induction path with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step_preserves step)

/-- Finite denotational returns agree with the existing L1 reductions, for
the whole expression grammar and the full final store. -/
theorem return_iff {source target : Config} :
    (.ok target.expr, target.store) ∈ run (denote source.expr) source.store ↔
      Steps source target ∧ IsValue target.expr := by
  constructor
  · intro member
    obtain ⟨out, path, equal, value⟩ := denote_sound source.expr member
    change out = target.expr at equal
    subst out
    exact ⟨path, value⟩
  · rintro ⟨path, value⟩
    rw [steps_preserves path, denote_value value, run_pure]
    exact Part.mem_some _

private theorem run_terminal (e : Expr) (s : Store) (terminal : Terminal ⟨e, s⟩) :
    run (denote e) s = Part.some ((if e.isValue then .ok e else .error ()), s) := by
  induction e with
  | int | bool | skip => rfl
  | deref loc =>
      cases lookup : s.lookup loc with
      | none => simp [denote, lookup, Expr.isValue]
      | some n => exact (terminal _ (.deref lookup)).elim
  | binary l op r ihLeft ihRight =>
      have leftTerminal : Terminal ⟨l, s⟩ := fun _ step => terminal _ (.binaryLeft step)
      rw [denote, run_bind, ihLeft leftTerminal]
      cases left : l.isValue with
      | false => simp [Part.bind_some, Expr.isValue]
      | true =>
          have lv := Expr.isValue_iff.1 left
          have rightTerminal : Terminal ⟨r, s⟩ := fun _ step => terminal _ (.binaryRight lv step)
          simp only [↓reduceIte, Part.bind_some, run_bind, ihRight rightTerminal]
          cases right : r.isValue with
          | false => simp [Expr.isValue]
          | true =>
              have rv := Expr.isValue_iff.1 right
              cases lv <;> cases rv
              case int.int a b =>
                cases op with
                | add => exact (terminal _ (.add a b s)).elim
                | ge => exact (terminal _ (.ge a b s)).elim
              all_goals simp [Expr.isValue, binary]
  | assign loc e ih =>
      have inner : Terminal ⟨e, s⟩ := fun _ step => terminal _ (.assignStep step)
      rw [denote, run_bind, ih inner]
      cases value : e.isValue with
      | false => simp [Expr.isValue, Part.bind_some]
      | true =>
          cases (Expr.isValue_iff.1 value) with
          | int n =>
              have missing : loc ∉ s := fun present => terminal _ (.assignValue present)
              simp [Expr.isValue, Part.bind_some, assign, Store.update_eq_none _ _ _ missing]
          | bool | skip => simp [Expr.isValue, Part.bind_some, assign]
  | cond test yes no ihTest _ _ =>
      have inner : Terminal ⟨test, s⟩ := fun _ step => terminal _ (.ifStep step)
      rw [denote, run_bind, ihTest inner]
      cases value : test.isValue with
      | false => simp [Expr.isValue, Part.bind_some]
      | true =>
          cases (Expr.isValue_iff.1 value) with
          | bool b => cases b <;> exact (terminal _ (by first | exact .ifFalse | exact .ifTrue)).elim
          | int | skip => simp [Expr.isValue, Part.bind_some, branch]
  | seq first second ihFirst _ =>
      have inner : Terminal ⟨first, s⟩ := fun _ step => terminal _ (.seqStep step)
      rw [denote, run_bind, ihFirst inner]
      cases value : first.isValue with
      | false => simp [Expr.isValue, Part.bind_some]
      | true =>
          cases (Expr.isValue_iff.1 value) with
          | skip => exact (terminal _ .seqSkip).elim
          | int | bool => simp [Expr.isValue, Part.bind_some, afterSkip]
  | loop => exact (terminal _ .while).elim

/-- Explicit denotational failure agrees exactly with finite reachability of
a stuck configuration, including the store at that configuration. -/
theorem error_iff {source : Config} {t : Store} :
    (.error (), t) ∈ run (denote source.expr) source.store ↔
      ∃ out, Steps source ⟨out, t⟩ ∧ Stuck ⟨out, t⟩ := by
  constructor
  · intro member
    exact denote_sound source.expr member
  · rintro ⟨out, path, stuck⟩
    have nonvalue : out.isValue ≠ true := fun h => stuck.1 (Expr.isValue_iff.1 h)
    rw [steps_preserves path, run_terminal _ _ stuck.2]
    simp [nonvalue, Part.mem_some_iff]

private theorem infinite_after_steps {source target : Config} (path : Steps source target)
    (infinite : InfiniteTrace Step source) : InfiniteTrace Step target := by
  induction path with
  | refl => exact infinite
  | tail _ step ih =>
      obtain ⟨next, move, tail⟩ := ih.unfold
      rw [move.deterministic step] at tail
      exact tail

/-- Undefined partial computations are exactly the sources with an infinite
L1 reduction. A finite stuck computation is defined and carries an error. -/
theorem diverges_iff {source : Config} :
    InfiniteTrace Step source ↔ ¬ (run (denote source.expr) source.store).Dom := by
  constructor
  · intro infinite defined
    obtain ⟨⟨result, t⟩, member⟩ := Part.dom_iff_mem.1 defined
    obtain ⟨out, path, finished⟩ := denote_sound source.expr member
    have terminal : Terminal ⟨out, t⟩ := by
      cases result with
      | error error => cases error; exact finished.2
      | ok v =>
          obtain ⟨equal, value⟩ := finished
          change out = v at equal
          subst out
          exact value_terminal value
    obtain ⟨next, step, _⟩ := (infinite_after_steps path infinite).unfold
    exact terminal next step
  · intro undefined
    apply InfiniteTrace.iff_not_sn.2
    intro normalizing
    obtain ⟨target, path, terminal⟩ := normalizing.normalizable
    apply undefined
    rw [steps_preserves path, run_terminal _ _ ((Relation.normal_iff _ _).1 terminal)]
    trivial

end Silmaril.Courses.Cambridge.L1.EffectfulDenotational
