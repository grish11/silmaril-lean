module

public import Silmaril.Courses.Cambridge.L3.Denotation.Defs
public import Silmaril.Courses.Cambridge.L3.Metatheory.Preservation
import Silmaril.Semantics.ElgotMonads.Thms

/-! # Exact may adequacy of the Cambridge L3 data and reference denotation -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation

open scoped Silmaril.Elgot.Nondet

@[simp] theorem returns_pure {A : Type} (a b : A) (s t : Store) :
    Returns (pure a) s b t ↔ b = a ∧ t = s := by
  change (b, t) ∈ₘ (pure (a, s) : SetM (A × Store)) ↔ _
  rw [Silmaril.Elgot.Nondet.mem_pure_iff, Prod.mk.injEq]

@[simp] theorem returns_bind {A B : Type} (m : Computation A) (k : A → Computation B)
    (s : Store) (b : B) (t : Store) :
    Returns (m >>= k) s b t ↔ ∃ a middle, Returns m s a middle ∧ Returns (k a) middle b t := by
  change (b, t) ∈ₘ (m.run s >>= fun (a, middle) => (k a).run middle) ↔ _
  rw [Silmaril.Elgot.Nondet.mem_bind_iff]
  constructor
  · rintro ⟨⟨a, middle⟩, hm, hk⟩
    exact ⟨a, middle, hm, hk⟩
  · rintro ⟨a, middle, hm, hk⟩
    exact ⟨(a, middle), hm, hk⟩

@[simp] theorem not_returns_fail {A : Type} (s t : Store) (a : A) :
    ¬ Returns fail s a t := fun h => h

private theorem returns_fields {n : Nat} {denotations : Fin n → Computation Value}
    {s t : Store} {vs : Fin n → Value} :
    Returns (fields denotations) s vs t ↔
      ∃ stores : Fin (n + 1) → Store, stores 0 = s ∧ stores (Fin.last n) = t ∧
        ∀ i, Returns (denotations i) (stores i.castSucc) (vs i) (stores i.succ) := Iff.rfl

private theorem computation_ext {A : Type} {p q : Computation A}
    (h : ∀ s a t, Returns p s a t ↔ Returns q s a t) : p = q := by
  funext s
  apply Silmaril.Elgot.Nondet.ext
  rintro ⟨a, t⟩
  exact h s a t

private theorem fields_pure {n : Nat} (vs : Fin n → Value) :
    fields (fun i => pure (vs i)) = pure vs := by
  apply computation_ext
  intro s ws t
  rw [returns_fields, returns_pure]
  constructor
  · rintro ⟨stores, start, finish, each⟩
    simp only [returns_pure] at each
    have all : ∀ k (bound : k < n + 1), stores ⟨k, bound⟩ = s := by
      intro k
      induction k with
      | zero => exact fun _ => start
      | succ k ih =>
          intro bound
          exact (each ⟨k, by omega⟩).2.trans (ih (by omega))
    exact ⟨funext (fun i => (each i).1), finish.symm.trans (all n (by omega))⟩
  · rintro ⟨rfl, eq⟩
    subst t
    exact ⟨fun _ => s, rfl, rfl, fun i => (returns_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

private theorem empty_substitution : Environment.empty.substitution = Expr.bvar := rfl

private theorem closeValue_empty (v : Value) : Environment.empty.closeValue v = v :=
  Subtype.ext (Expr.subst_id v.val)

private theorem lift_substitution (env : Environment) :
    env.lift.substitution = Expr.liftSubst env.substitution := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      change ((env i).shift).expr = ((env i).expr).rename Nat.succ
      cases env i <;> rfl

private theorem compose_substitution (inner outer : Environment) :
    (inner.compose outer).substitution =
      fun i => (inner.substitution i).subst outer.substitution := by
  funext i
  simp only [Environment.substitution, Environment.compose]
  cases inner i <;> rfl

private theorem closeValue_compose (inner outer : Environment) (v : Value) :
    outer.closeValue (inner.closeValue v) = (inner.compose outer).closeValue v := by
  apply Subtype.ext
  exact (Expr.subst_comp _ _ _).trans (congrArg (fun σ => v.val.subst σ)
    (compose_substitution inner outer).symm)

private theorem compose_empty (env : Environment) : env.compose Environment.empty = env := by
  funext i
  simp only [Environment.compose]
  cases env i with
  | index i => rfl
  | value v => exact congrArg Binding.value (closeValue_empty v)

private theorem compose_lift_extend (inner outer : Environment) (v : Value) :
    inner.lift.compose (outer.extend v) = (inner.compose outer).extend v := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [Environment.compose, Environment.lift, Environment.extend]
      cases inner i with
      | index j => rfl
      | value old =>
          apply congrArg Binding.value
          apply Subtype.ext
          change (old.val.rename Nat.succ).subst (outer.extend v).substitution =
            old.val.subst outer.substitution
          rw [Expr.subst_rename]
          rfl

private theorem beta_after_subst (body : Expr) (v : Value) (env : Environment) :
    (body.subst (Expr.liftSubst env.substitution)).beta v.val =
      body.subst (env.extend v).substitution := by
  rw [Expr.beta, Expr.subst_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => rw [Expr.liftSubst, Expr.subst_rename]; exact Expr.subst_id _

theorem denoteWith_value (env : Environment) (v : Value) :
    denoteWith env v.val = pure (env.closeValue v) := by
  obtain ⟨e, ready⟩ := v
  induction ready with
  | int | bool | skip | loc | lam => rfl
  | pair vl vr ihl ihr => simp only [denoteWith, ihl, ihr, pure_bind]; rfl
  | inl ready ih | inr ready ih => simp only [denoteWith, ih, pure_bind]; rfl
  | record ready ih =>
      simp only [denoteWith, ih, fields_pure, pure_bind]
      rfl

theorem denote_value (v : Value) : denote v.val = pure v := by
  rw [denote, denoteWith_value, closeValue_empty]

/-- Interpreting a syntactic substitution of value or variable entries agrees
with composing the corresponding lexical environments. -/
theorem denoteWith_subst (e : Expr) (inner outer : Environment) :
    denoteWith outer (e.subst inner.substitution) = denoteWith (inner.compose outer) e := by
  induction e generalizing inner outer <;>
    simp_all only [Expr.subst, denoteWith, ← lift_substitution, compose_lift_extend]
  case bvar i =>
    simp only [Environment.substitution, Environment.compose]
    cases inner i with
    | index j => rfl
    | value v => exact denoteWith_value outer v
  case lam domain body _ =>
    rw [lift_substitution]
    exact congrArg pure (closeValue_compose inner outer ⟨.lam domain body, .lam _ _⟩)

private theorem beta_environment (body : Expr) (v : Value) :
    body.subst (Environment.empty.extend v).substitution = body.beta v.val := by
  unfold Expr.beta
  congr 1
  funext i
  cases i <;> rfl

theorem denote_beta (body : Expr) (v : Value) :
    denote (body.beta v.val) = denoteWith (Environment.empty.extend v) body := by
  rw [denote, ← beta_environment body v, denoteWith_subst, compose_empty]

private theorem Fragment.subst_environment {e : Expr} (admitted : Fragment e)
    (env : Environment) : Fragment (e.subst env.substitution) := by
  induction admitted generalizing env with
  | value ready => exact .value (ready.subst _)
  | bvar i =>
      change Fragment ((env i).expr)
      cases env i with
      | index j => exact .bvar j
      | value v => exact .value v.property
  | letE _ _ ihv ihb =>
      simp only [Expr.subst, ← lift_substitution]
      exact .letE (ihv env) (ihb env.lift)
  | matchSum _ _ _ ihe ihl ihr =>
      simp only [Expr.subst, ← lift_substitution]
      exact .matchSum (ihe env) (ihl env.lift) (ihr env.lift)
  | binary _ _ ihl ihr => exact .binary (ihl env) (ihr env)
  | cond _ _ _ ihc iha ihb => exact .cond (ihc env) (iha env) (ihb env)
  | seq _ _ iha ihb => exact .seq (iha env) (ihb env)
  | loop _ _ ihc ihb => exact .loop (ihc env) (ihb env)
  | pair _ _ iha ihb => exact .pair (iha env) (ihb env)
  | fst _ ih => exact .fst (ih env)
  | snd _ ih => exact .snd (ih env)
  | inl _ ih => exact .inl (ih env)
  | inr _ ih => exact .inr (ih env)
  | record _ ih => exact .record (fun i => ih i env)
  | project _ ih => exact .project (ih env)
  | ref _ ih => exact .ref (ih env)
  | deref _ ih => exact .deref (ih env)
  | assign _ _ ihl ihr => exact .assign (ihl env) (ihr env)

private theorem Fragment.beta {body : Expr} (admitted : Fragment body) (v : Value) :
    Fragment (body.beta v.val) := by
  rw [← beta_environment body v]
  exact admitted.subst_environment (Environment.empty.extend v)

private theorem Steps.in_frame (plug : Expr → Expr)
    (lift : ∀ {e e' : Expr} {s s' : Store}, Step ⟨e, s⟩ ⟨e', s'⟩ →
      Step ⟨plug e, s⟩ ⟨plug e', s'⟩)
    {e e' : Expr} {s s' : Store} (trace : Steps ⟨e, s⟩ ⟨e', s'⟩) :
    Steps ⟨plug e, s⟩ ⟨plug e', s'⟩ :=
  trace.lift (fun c => (⟨plug c.expr, c.store⟩ : Config)) (fun ⟨_, _⟩ ⟨_, _⟩ step => lift step)

private theorem record_steps {labels : RecordLabels} {es : labels.Index → Expr}
    {vs : labels.Index → Value} {denotations : labels.Index → Computation Value} {s t : Store}
    (trace : ∀ (i : labels.Index) {start finish : Store},
      Returns (denotations i) start (vs i) finish →
        Steps ⟨es i, start⟩ ⟨(vs i).val, finish⟩)
    (returned : Returns (fields denotations) s vs t) :
    Steps ⟨.record labels es, s⟩ ⟨(record labels vs).val, t⟩ := by
  obtain ⟨stores, start, finish, each⟩ := returns_fields.mp returned
  let n := labels.names.length
  let atPrefix (k : Nat) (j : labels.Index) : Expr :=
    if j.val < k then (vs j).val else es j
  have prefixTrace : ∀ k (bound : k ≤ n),
      Steps ⟨.record labels es, s⟩ ⟨.record labels (atPrefix k), stores ⟨k, by omega⟩⟩ := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa [atPrefix, start] using (Relation.ReflTransGen.refl (a := (⟨.record labels es, s⟩ : Config)) :
          Steps ⟨.record labels es, s⟩ ⟨.record labels es, s⟩)
    | succ k ih =>
        intro bound
        let i : labels.Index := ⟨k, by omega⟩
        let plug (e : Expr) := Expr.record labels (Function.update (atPrefix k) i e)
        have here : atPrefix k i = es i := ite_eq_right (Nat.lt_irrefl _)
        have before : plug (es i) = .record labels (atPrefix k) := by
          simp [plug, ← here]
        have after : plug (vs i).val = .record labels (atPrefix (k + 1)) := by
          unfold plug
          congr 1
          funext j
          by_cases same : j = i
          · subst j
            simp [atPrefix, i]
          · have different : j.val ≠ k := fun eq => same (Fin.ext eq)
            have earlier : j.val < k + 1 ↔ j.val < k := by omega
            simp [Function.update_of_ne same, atPrefix, earlier]
        have lift {e e' : Expr} {s s' : Store} (step : Step ⟨e, s⟩ ⟨e', s'⟩) :
            Step ⟨plug e, s⟩ ⟨plug e', s'⟩ := by
          let updated := Function.update (atPrefix k) i e
          have earlierReady (j : labels.Index) (earlier : j < i) : IsValue (updated j) := by
            have different : j ≠ i := fun eq => Nat.lt_irrefl _ (eq ▸ earlier)
            simpa only [updated, Function.update_of_ne different, atPrefix,
              ite_eq_left (show j.val < k from earlier)] using (vs j).property
          have inner : Step ⟨updated i, s⟩ ⟨e', s'⟩ := by
            simpa only [updated, Function.update_self] using step
          simpa only [plug, updated, Function.update_idem] using
            Step.recordStep i earlierReady inner
        exact (ih (by omega)).trans (by
          rw [← before, ← after]
          exact Steps.in_frame plug lift (trace i (each i)))
  have all : atPrefix n = fun j => (vs j).val := by
    funext j
    exact ite_eq_left j.isLt
  rw [← finish]
  change Steps ⟨.record labels es, s⟩ ⟨.record labels (fun j => (vs j).val), _⟩
  rw [← all]
  exact prefixTrace n (Nat.le_refl _)

private theorem binary_step {a b v : Value} {op : Op} {s t : Store}
    (result : Returns (binary op a b) s v t) :
    Step ⟨.binary a.val op b.val, s⟩ ⟨v.val, t⟩ := by
  rcases a with ⟨a, va⟩
  rcases b with ⟨b, vb⟩
  cases op <;> cases va <;> cases vb <;> simp [binary] at result
  · obtain ⟨rfl, rfl⟩ := result
    exact .add _ _ _
  · obtain ⟨rfl, rfl⟩ := result
    exact .ge _ _ _

private theorem first_step {a v : Value} {s t : Store}
    (result : Returns (first a) s v t) : Step ⟨.fst a.val, s⟩ ⟨v.val, t⟩ := by
  rcases a with ⟨_, ready⟩
  cases ready <;> simp [first] at result
  obtain ⟨rfl, rfl⟩ := result
  exact .fstValue ‹_› ‹_›

private theorem second_step {a v : Value} {s t : Store}
    (result : Returns (second a) s v t) : Step ⟨.snd a.val, s⟩ ⟨v.val, t⟩ := by
  rcases a with ⟨_, ready⟩
  cases ready <;> simp [second] at result
  obtain ⟨rfl, rfl⟩ := result
  exact .sndValue ‹_› ‹_›

private theorem field_step {a v : Value} {label : Label} {s t : Store}
    (result : Returns (field a label) s v t) : Step ⟨.project a.val label, s⟩ ⟨v.val, t⟩ := by
  rcases a with ⟨_, ready⟩
  cases ready <;> try contradiction
  case record labels fs ready =>
    change ∃ i, labels.label i = label ∧ (v, t) = (_, s) at result
    obtain ⟨i, rfl, eq⟩ := result
    cases eq
    exact .projectValue i ready

private theorem read_step {a v : Value} {s t : Store}
    (result : Returns (read a) s v t) : Step ⟨.deref a.val, s⟩ ⟨v.val, t⟩ := by
  rcases a with ⟨_, ready⟩
  cases ready <;> try contradiction
  case loc loc =>
    change s.lookup loc = some v ∧ t = s at result
    obtain ⟨found, rfl⟩ := result
    exact .derefValue found

private theorem while_transition {test body : Computation Value} (start : Unit × Store)
    (outcome : (Value × Store) ⊕ (Unit × Store)) :
    outcome ∈ₘ Silmaril.Elgot.StateT.body (whileBody test body) start ↔
      match outcome with
      | .inl (v, t) => v = unit ∧ Returns test start.2 (boolean false) t
      | .inr (_, t) =>
          ∃ middle, Returns test start.2 (boolean true) middle ∧ Returns body middle unit t := by
  rw [Silmaril.Elgot.StateT.body, Silmaril.Elgot.Nondet.mem_bind_iff]
  simp only [Function.comp_apply, Silmaril.Elgot.Nondet.mem_pure_iff]
  constructor
  · rintro ⟨⟨tag, t⟩, event, rfl⟩
    change (tag = .inl unit ∧ Returns test start.2 (boolean false) t) ∨
      (tag = .inr () ∧ ∃ middle,
        Returns test start.2 (boolean true) middle ∧ Returns body middle unit t) at event
    rcases event with ⟨rfl, done⟩ | ⟨rfl, again⟩
    · exact ⟨rfl, done⟩
    · exact again
  · cases outcome with
    | inl out =>
        rcases out with ⟨v, t⟩
        rintro ⟨rfl, done⟩
        exact ⟨(.inl unit, t), Or.inl ⟨rfl, done⟩, rfl⟩
    | inr out =>
        rcases out with ⟨⟨⟩, t⟩
        intro again
        exact ⟨(.inr (), t), Or.inr ⟨rfl, again⟩, rfl⟩

private theorem loop_steps {test body : Expr} {s t : Store} {v : Value}
    {testDenotation bodyDenotation : Computation Value}
    (testTrace : ∀ {u w x}, Returns testDenotation u x w → Steps ⟨test, u⟩ ⟨x.val, w⟩)
    (bodyTrace : ∀ {u w x}, Returns bodyDenotation u x w → Steps ⟨body, u⟩ ⟨x.val, w⟩)
    (returned : Returns (whileLoop testDenotation bodyDenotation) s v t) :
    Steps ⟨.loop test body, s⟩ ⟨v.val, t⟩ := by
  let f := Silmaril.Elgot.StateT.body (whileBody testDenotation bodyDenotation)
  have finite {start : Unit × Store} {finish : Value × Store}
      (runs : Silmaril.Elgot.Nondet.Runs f start finish) :
      Steps ⟨.loop test body, start.2⟩ ⟨finish.1.val, finish.2⟩ := by
    induction runs with
    | @done start finish event =>
        rcases finish with ⟨v, t⟩
        obtain ⟨rfl, tested⟩ := (while_transition start _).mp event
        exact ((Steps.in_frame (fun c => .cond c (.seq body (.loop test body)) .skip)
          Step.ifStep (testTrace tested)).head .while).tail .ifFalse
    | @more start next finish event _ ih =>
        obtain ⟨mid, tested, executed⟩ := (while_transition start _).mp event
        have testedTrace := (Steps.in_frame
          (fun c => .cond c (.seq body (.loop test body)) .skip)
          Step.ifStep (testTrace tested)).head Step.while
        have executedTrace := (Steps.in_frame (fun e => .seq e (.loop test body))
          Step.seqStep (bodyTrace executed)).head (Step.ifTrue (no := .skip))
        exact (testedTrace.trans (executedTrace.tail .seqSkip)).trans ih
  change (v, t) ∈ₘ (whileLoop testDenotation bodyDenotation).run s at returned
  rw [whileLoop, Silmaril.Elgot.StateT.run_iter] at returned
  exact finite ((Silmaril.Elgot.Nondet.mem_iter_iff f ((), s) (v, t)).mp returned)

private theorem returns_while {test body : Computation Value} {s t : Store} {v : Value} :
    Returns (whileLoop test body) s v t ↔
      (v = unit ∧ Returns test s (boolean false) t) ∨
      ∃ mid next, Returns test s (boolean true) mid ∧ Returns body mid unit next ∧
        Returns (whileLoop test body) next v t := by
  conv_lhs => rw [whileLoop, congrFun (Silmaril.Elgot.StateT.fixpoint (whileBody test body)) ()]
  rw [returns_bind]
  constructor
  · rintro ⟨tag, next, event, continued⟩
    change (tag = .inl unit ∧ Returns test s (boolean false) next) ∨
      (tag = .inr () ∧ ∃ mid, Returns test s (boolean true) mid ∧
        Returns body mid unit next) at event
    rcases event with ⟨rfl, done⟩ | ⟨rfl, mid, tested, executed⟩
    · obtain ⟨eq, rfl⟩ := (returns_pure _ _ _ _).mp continued
      exact Or.inl ⟨eq, done⟩
    · exact Or.inr ⟨mid, next, tested, executed, continued⟩
  · rintro (⟨rfl, done⟩ | ⟨mid, next, tested, executed, continued⟩)
    · exact ⟨.inl unit, t, Or.inl ⟨rfl, done⟩, (returns_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
    · exact ⟨.inr (), next, Or.inr ⟨rfl, mid, tested, executed⟩, continued⟩

/-- An environment closes the source by capture-avoiding substitution. Every
lexical return has a trace from that instance in the original rules. -/
theorem soundWith {e : Expr} {v : Value} {s t : Store}
    (env : Environment) (fragment : Fragment e) (returned : Returns (denoteWith env e) s v t) :
    Steps ⟨e.subst env.substitution, s⟩ ⟨v.val, t⟩ := by
  induction fragment generalizing env v s t with
  | value ready =>
      rw [denoteWith_value env ⟨_, ready⟩] at returned
      obtain ⟨rfl, rfl⟩ := (returns_pure _ _ _ _).mp returned
      exact .refl
  | bvar i =>
      rw [denoteWith] at returned
      cases entry : env i with
      | index j =>
          rw [entry, Binding.denote] at returned
          exact (not_returns_fail _ _ _ returned).elim
      | value w =>
          rw [entry, Binding.denote] at returned
          obtain ⟨equal, storeEqual⟩ := (returns_pure _ _ _ _).mp returned
          subst v t
          simp only [Expr.subst, Environment.substitution, entry, Binding.expr]
          exact .refl
  | @letE A value body _ _ ihv ihb =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨w, middle, evaluated, result⟩ := returned
      have bound := Steps.in_frame
        (fun e => .letE A e (body.subst (Expr.liftSubst env.substitution)))
        Step.letStep (ihv env evaluated)
      have instantiate : Step
          ⟨.letE A w.val (body.subst (Expr.liftSubst env.substitution)), middle⟩
          ⟨body.subst (env.extend w).substitution, middle⟩ := by
        rw [← beta_after_subst]
        exact .letValue w.property
      exact (bound.tail instantiate).trans (ihb (env.extend w) result)
  | @matchSum e left right A B _ _ _ ihe ihl ihr =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨w, middle, evaluated, result⟩ := returned
      let closeBody (branch : Expr) := branch.subst (Expr.liftSubst env.substitution)
      have tested := Steps.in_frame (fun e => .matchSum e A (closeBody left) B (closeBody right))
        Step.matchStep (ihe env evaluated)
      rcases w with ⟨_, ready⟩
      cases ready <;> try contradiction
      case inl payload T ready =>
        let argument : Value := ⟨payload, ready⟩
        have instantiate : Step
            ⟨.matchSum (.inl payload T) A (closeBody left) B (closeBody right), middle⟩
            ⟨left.subst (env.extend argument).substitution, middle⟩ := by
          rw [← beta_after_subst]
          exact .matchLeft ready
        exact (tested.tail instantiate).trans (ihl (env.extend argument) result)
      case inr payload T ready =>
        let argument : Value := ⟨payload, ready⟩
        have instantiate : Step
            ⟨.matchSum (.inr payload T) A (closeBody left) B (closeBody right), middle⟩
            ⟨right.subst (env.extend argument).substitution, middle⟩ := by
          rw [← beta_after_subst]
          exact .matchRight ready
        exact (tested.tail instantiate).trans (ihr (env.extend argument) result)
  | @binary a b op _ _ iha ihb =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, s₁, ha, bv, s₂, hb, result⟩ := returned
      have left := Steps.in_frame (fun e => .binary e op (b.subst env.substitution))
        Step.binaryLeft (iha env ha)
      have right := Steps.in_frame (Expr.binary av.val op) (Step.binaryRight av.property) (ihb env hb)
      exact (left.trans right).tail (binary_step result)
  | @cond c yes no _ _ _ ihc ihy ihn =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨cv, middle, evaluated, result⟩ := returned
      have contextTrace := Steps.in_frame
        (fun e => .cond e (yes.subst env.substitution) (no.subst env.substitution))
        Step.ifStep (ihc env evaluated)
      obtain ⟨_, ready⟩ := cv
      cases ready <;> try contradiction
      case bool b =>
        cases b
        · exact contextTrace.trans ((ihn env result).head Step.ifFalse)
        · exact contextTrace.trans ((ihy env result).head Step.ifTrue)
  | @seq a b _ _ iha ihb =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, middle, evaluated, result⟩ := returned
      have contextTrace := Steps.in_frame (fun e => .seq e (b.subst env.substitution))
        Step.seqStep (iha env evaluated)
      obtain ⟨_, ready⟩ := av
      cases ready <;> try contradiction
      exact contextTrace.trans ((ihb env result).head Step.seqSkip)
  | loop _ _ ihTest ihBody =>
      exact loop_steps (fun h => ihTest env h) (fun h => ihBody env h) returned
  | @pair a b _ _ iha ihb =>
      simp only [denoteWith, returns_bind, returns_pure] at returned
      obtain ⟨av, _, ha, bv, _, hb, rfl, rfl⟩ := returned
      exact (Steps.in_frame (fun e => .pair e (b.subst env.substitution)) Step.pairLeft (iha env ha)).trans
        (Steps.in_frame (Expr.pair av.val) (Step.pairRight av.property) (ihb env hb))
  | fst _ ih =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, _, ha, result⟩ := returned
      exact (Steps.in_frame Expr.fst Step.fstStep (ih env ha)).tail (first_step result)
  | snd _ ih =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, _, ha, result⟩ := returned
      exact (Steps.in_frame Expr.snd Step.sndStep (ih env ha)).tail (second_step result)
  | @inl e T _ ih =>
      simp only [denoteWith, returns_bind, returns_pure] at returned
      obtain ⟨av, _, evaluated, rfl, rfl⟩ := returned
      exact Steps.in_frame (fun e => .inl e T) Step.inl (ih env evaluated)
  | @inr e T _ ih =>
      simp only [denoteWith, returns_bind, returns_pure] at returned
      obtain ⟨av, _, evaluated, rfl, rfl⟩ := returned
      exact Steps.in_frame (fun e => .inr e T) Step.inr (ih env evaluated)
  | record _ ih =>
      simp only [denoteWith, returns_bind, returns_pure] at returned
      obtain ⟨vs, _, evaluated, rfl, rfl⟩ := returned
      exact record_steps (fun i {_ _} returned => ih i env returned) evaluated
  | @project e label _ ih =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, _, evaluated, result⟩ := returned
      exact (Steps.in_frame (fun e => .project e label) Step.projectStep (ih env evaluated)).tail
        (field_step result)
  | ref _ ih =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, middle, evaluated, result⟩ := returned
      have multi := Steps.in_frame Expr.ref Step.refStep (ih env evaluated)
      change ∃ a, a ∉ middle ∧ (v, t) = (address a, middle.insert a av) at result
      obtain ⟨a, fresh, eq⟩ := result
      cases eq
      exact multi.tail (.refValue av fresh)
  | deref _ ih =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨av, _, evaluated, result⟩ := returned
      exact (Steps.in_frame Expr.deref Step.derefStep (ih env evaluated)).tail (read_step result)
  | @assign lhs rhs _ _ ihl ihr =>
      simp only [denoteWith, returns_bind] at returned
      obtain ⟨lv, _, leftEval, result⟩ := returned
      have leftTrace := Steps.in_frame (fun e => .assign e (rhs.subst env.substitution))
        Step.assignLeft (ihl env leftEval)
      obtain ⟨_, ready⟩ := lv
      cases ready <;> try contradiction
      case loc loc =>
        simp only [assign, returns_bind] at result
        obtain ⟨rv, middle, rightEval, result⟩ := result
        have rightTrace := Steps.in_frame (Expr.assign (.loc loc)) Step.assignRight (ihr env rightEval)
        change loc ∈ middle ∧ (v, t) = (unit, middle.insert loc rv) at result
        obtain ⟨present, eq⟩ := result
        cases eq
        exact (leftTrace.trans rightTrace).tail (.assignValue rv present)

/-- Every denotational result has a finite trace in the original rules. -/
theorem sound {e : Expr} {v : Value} {s t : Store}
    (fragment : Fragment e) (returned : Returns (denote e) s v t) :
    Steps ⟨e, s⟩ ⟨v.val, t⟩ := by
  simpa only [empty_substitution, Expr.subst_id] using soundWith Environment.empty fragment returned

private theorem no_value_step {e : Expr} {s : Store} {next : Config}
    (ready : IsValue e) (step : Step ⟨e, s⟩ next) : False := by
  induction ready generalizing s next with
  | int | bool | skip | loc | lam => cases step
  | pair _ _ iha ihb =>
      cases step with
      | pairLeft inner => exact iha inner
      | pairRight _ inner => exact ihb inner
  | inl _ ih => cases step with | inl inner => exact ih inner
  | inr _ ih => cases step with | inr inner => exact ih inner
  | record _ ih => cases step with | recordStep i _ inner => exact ih i inner

private def Includes {A : Type}
    (before : Computation A) (s : Store) (after : Computation A) (s' : Store) : Prop :=
  ∀ ⦃v t⦄, Returns after s' v t → Returns before s v t

private theorem Includes.bind {A B : Type} {before after : Computation A} {s s' : Store}
    (h : Includes before s after s') (k : A → Computation B) :
    Includes (before >>= k) s (after >>= k) s' := by
  intro v t result
  obtain ⟨a, middle, ha, hk⟩ := (returns_bind _ _ _ _ _).mp result
  exact (returns_bind _ _ _ _ _).mpr ⟨a, middle, h ha, hk⟩

private theorem fields_backward {labels : RecordLabels} {es : labels.Index → Expr}
    {s s' : Store} (i : labels.Index) (e' : Expr) (ready : ∀ j, j < i → IsValue (es j))
    (back : Includes (denote (es i)) s (denote e') s') :
    Includes (fields (fun j => denote (es j))) s
      (fields (fun j => denote (Function.update es i e' j))) s' := by
  intro vs t returned
  obtain ⟨stores, start, finish, each⟩ := returns_fields.mp returned
  have stable (k : Nat) (bound : k ≤ i.val) (h : k < labels.names.length + 1) :
      stores ⟨k, h⟩ = s' := by
    induction k with
    | zero => exact start
    | succ k ih =>
        let j : labels.Index := ⟨k, by have := i.isLt; omega⟩
        have earlier : j < i := by change k < i.val; omega
        have different : j ≠ i := fun eq => Nat.lt_irrefl _ (eq ▸ earlier)
        have thisField := each j
        rw [Function.update_of_ne different, denote_value ⟨es j, ready j earlier⟩] at thisField
        exact ((returns_pure _ _ _ _).mp thisField).2.trans (ih (by omega) (by omega))
  let stores' (j : Fin (labels.names.length + 1)) := if j.val ≤ i.val then s else stores j
  refine returns_fields.mpr ⟨stores', by simp [stores'], ?_, ?_⟩
  · have last : ¬ (Fin.last labels.names.length).val ≤ i.val := Nat.not_le_of_gt i.isLt
    simpa only [stores', ite_eq_right last] using finish
  · intro j
    rcases Nat.lt_trichotomy j.val i.val with earlier | same | later
    · have earlier' : j < i := earlier
      have different : j ≠ i := fun eq => Nat.lt_irrefl _ (eq ▸ earlier')
      have thisField := each j
      rw [Function.update_of_ne different, denote_value ⟨es j, ready j earlier'⟩] at thisField
      have valueEq := ((returns_pure _ _ _ _).mp thisField).1
      rw [denote_value ⟨es j, ready j earlier'⟩]
      exact (returns_pure _ _ _ _).mpr ⟨valueEq, by
        have h₁ : j.castSucc.val ≤ i.val := by simpa using Nat.le_of_lt earlier
        have h₂ : j.succ.val ≤ i.val := earlier
        simp only [stores', ite_eq_left h₁, ite_eq_left h₂]⟩
    · have equal : j = i := Fin.ext same
      subst j
      have thisField := each i
      have atStart : stores i.castSucc = s' :=
        stable i.val (Nat.le_refl _) (by have := i.isLt; omega)
      rw [Function.update_self, atStart] at thisField
      have h₁ : i.castSucc.val ≤ i.val := Nat.le_refl _
      have h₂ : ¬ i.succ.val ≤ i.val := Nat.not_succ_le_self _
      simpa only [stores', ite_eq_left h₁, ite_eq_right h₂] using back thisField
    · have different : j ≠ i := fun eq => Nat.lt_irrefl _ (eq ▸ later)
      have h₁ : ¬ j.castSucc.val ≤ i.val := Nat.not_le_of_gt later
      have h₂ : ¬ j.succ.val ≤ i.val := by change ¬ j.val + 1 ≤ i.val; omega
      simpa only [stores', ite_eq_right h₁, ite_eq_right h₂, Function.update_of_ne different]
        using each j

private theorem reflect {e : Expr} {s : Store} {next : Config}
    (fragment : Fragment e) (step : Step ⟨e, s⟩ next) :
    Fragment next.expr ∧ Includes (denote e) s (denote next.expr) next.store := by
  induction fragment generalizing s next with
  | value ready => exact (no_value_step ready step).elim
  | bvar _ => cases step
  | @letE A value body hv hb ihv _ =>
      cases step with
      | letStep inner =>
          obtain ⟨admitted, back⟩ := ihv inner
          exact ⟨.letE admitted hb, back.bind _⟩
      | letValue ready =>
          let v : Value := ⟨value, ready⟩
          refine ⟨hb.beta v, ?_⟩
          rw [denote_beta body v]
          change Includes (denote value >>= fun w => denoteWith (Environment.empty.extend w) body)
            s _ s
          rw [denote_value v, pure_bind]
          exact fun {_ _} result => result
  | @matchSum e left right A B _ hl hr ihe _ _ =>
      cases step with
      | matchStep inner =>
          obtain ⟨admitted, back⟩ := ihe inner
          exact ⟨.matchSum admitted hl hr, back.bind _⟩
      | @matchLeft payload _ _ _ _ T _ ready =>
          let v : Value := ⟨payload, ready⟩
          refine ⟨hl.beta v, ?_⟩
          rw [denote_beta left v]
          change Includes (denote (.inl payload T) >>= fun w => splitSum w
            (fun arg => denoteWith (Environment.empty.extend arg) left)
            (fun arg => denoteWith (Environment.empty.extend arg) right)) s _ s
          rw [denote_value ⟨_, .inl ready⟩, pure_bind]
          exact fun {_ _} result => result
      | @matchRight payload _ _ _ _ T _ ready =>
          let v : Value := ⟨payload, ready⟩
          refine ⟨hr.beta v, ?_⟩
          rw [denote_beta right v]
          change Includes (denote (.inr payload T) >>= fun w => splitSum w
            (fun arg => denoteWith (Environment.empty.extend arg) left)
            (fun arg => denoteWith (Environment.empty.extend arg) right)) s _ s
          rw [denote_value ⟨_, .inr ready⟩, pure_bind]
          exact fun {_ _} result => result
  | @binary a b op ha hb iha ihb =>
      cases step with
      | add x y =>
          exact ⟨.value (.int (x + y)), by simp [Includes, denote, denoteWith, pure_bind, binary, integer]⟩
      | ge x y =>
          exact ⟨.value (.bool (x ≥ y)), by simp [Includes, denote, denoteWith, pure_bind, binary, integer]⟩
      | binaryLeft inner =>
          obtain ⟨admitted, back⟩ := iha inner
          exact ⟨.binary admitted hb, back.bind _⟩
      | binaryRight ready inner =>
          obtain ⟨admitted, back⟩ := ihb inner
          refine ⟨.binary ha admitted, ?_⟩
          simp only [denote, denoteWith, denoteWith_value Environment.empty ⟨a, ready⟩,
            closeValue_empty, pure_bind]
          exact back.bind _
  | cond _ hy hn ihc _ _ =>
      cases step with
      | ifTrue => exact ⟨hy, by simp [Includes, denote, denoteWith, pure_bind, branch, boolean]⟩
      | ifFalse => exact ⟨hn, by simp [Includes, denote, denoteWith, pure_bind, branch, boolean]⟩
      | ifStep inner =>
          obtain ⟨admitted, back⟩ := ihc inner
          exact ⟨.cond admitted hy hn, back.bind _⟩
  | seq _ hb iha _ =>
      cases step with
      | seqSkip => exact ⟨hb, by simp [Includes, denote, denoteWith, pure_bind, sequence, unit]⟩
      | seqStep inner =>
          obtain ⟨admitted, back⟩ := iha inner
          exact ⟨.seq admitted hb, back.bind _⟩
  | loop ht hb _ _ =>
      cases step with
      | «while» =>
          refine ⟨.cond ht (.seq hb (.loop ht hb)) (.value .skip), ?_⟩
          intro v t result
          simp only [denote, denoteWith, returns_bind] at result
          obtain ⟨guardValue, mid, tested, result⟩ := result
          obtain ⟨_, ready⟩ := guardValue
          apply returns_while.mpr
          cases ready <;> try contradiction
          case bool b =>
            cases b
            · obtain ⟨eq, rfl⟩ := (returns_pure _ _ _ _).mp result
              exact Or.inl ⟨eq, tested⟩
            · simp only [branch, returns_bind] at result
              obtain ⟨bodyValue, next, evaluated, continued⟩ := result
              obtain ⟨_, ready⟩ := bodyValue
              cases ready <;> try contradiction
              exact Or.inr ⟨mid, next, tested, evaluated, continued⟩
  | @pair a b ha hb iha ihb =>
      cases step with
      | pairLeft inner =>
          obtain ⟨admitted, back⟩ := iha inner
          exact ⟨.pair admitted hb, back.bind _⟩
      | pairRight ready inner =>
          obtain ⟨admitted, back⟩ := ihb inner
          refine ⟨.pair ha admitted, ?_⟩
          simp only [denote, denoteWith, denoteWith_value Environment.empty ⟨a, ready⟩,
            closeValue_empty, pure_bind]
          exact back.bind _
  | fst _ ih =>
      cases step with
      | fstValue vl vr =>
          refine ⟨.value vl, ?_⟩
          rw [show denote (.fst _) = (denote _ >>= first) from rfl,
            denote_value ⟨_, IsValue.pair vl vr⟩, pure_bind, denote_value ⟨_, vl⟩]
          exact fun {_ _} result => result
      | fstStep inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.fst admitted, back.bind _⟩
  | snd _ ih =>
      cases step with
      | sndValue vl vr =>
          refine ⟨.value vr, ?_⟩
          rw [show denote (.snd _) = (denote _ >>= second) from rfl,
            denote_value ⟨_, IsValue.pair vl vr⟩, pure_bind, denote_value ⟨_, vr⟩]
          exact fun {_ _} result => result
      | sndStep inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.snd admitted, back.bind _⟩
  | inl _ ih =>
      cases step with
      | inl inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.inl admitted, back.bind _⟩
  | inr _ ih =>
      cases step with
      | inr inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.inr admitted, back.bind _⟩
  | @record labels es admitted ih =>
      cases step with
      | recordStep i ready inner =>
          obtain ⟨newField, back⟩ := ih i inner
          refine ⟨.record ?_, (fields_backward i _ ready back).bind _⟩
          intro j
          by_cases same : j = i
          · subst j
            simpa only [Function.update_self] using newField
          · simpa only [Function.update_of_ne same] using admitted j
  | project _ ih =>
      cases step with
      | projectStep inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.project admitted, back.bind _⟩
      | projectValue i ready =>
          refine ⟨.value (ready i), ?_⟩
          rw [show denote (.project _ _) = (denote _ >>= fun v => field v _) from rfl,
            denote_value ⟨_, .record ready⟩, pure_bind, denote_value ⟨_, ready i⟩]
          intro v t result
          obtain ⟨rfl, rfl⟩ := (returns_pure _ _ _ _).mp result
          exact ⟨i, rfl, rfl⟩
  | ref _ ih =>
      cases step with
      | refStep inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.ref admitted, back.bind _⟩
      | @refValue _ v a fresh =>
          refine ⟨.value (.loc a), ?_⟩
          simp only [denote, denoteWith, denoteWith_value Environment.empty v,
            closeValue_empty, pure_bind]
          intro w t result
          obtain ⟨rfl, rfl⟩ := (returns_pure _ _ _ _).mp result
          exact ⟨a, fresh, rfl⟩
  | deref _ ih =>
      cases step with
      | derefStep inner =>
          obtain ⟨admitted, back⟩ := ih inner
          exact ⟨.deref admitted, back.bind _⟩
      | @derefValue _ a v found =>
          refine ⟨.value v.property, ?_⟩
          simp only [denote, denoteWith, pure_bind, denoteWith_value Environment.empty v,
            closeValue_empty]
          intro w t result
          obtain ⟨rfl, rfl⟩ := (returns_pure _ _ _ _).mp result
          exact ⟨found, rfl⟩
  | assign hl hr ihl ihr =>
      cases step with
      | assignLeft inner =>
          obtain ⟨admitted, back⟩ := ihl inner
          exact ⟨.assign admitted hr, back.bind _⟩
      | assignRight inner =>
          obtain ⟨admitted, back⟩ := ihr inner
          refine ⟨.assign hl admitted, ?_⟩
          simp only [denote, denoteWith, pure_bind, assign, address]
          exact back.bind _
      | @assignValue _ a v present =>
          refine ⟨.value .skip, ?_⟩
          simp only [denote, denoteWith, pure_bind, assign, address,
            denoteWith_value Environment.empty v, closeValue_empty]
          intro w t result
          obtain ⟨rfl, rfl⟩ := (returns_pure _ _ _ _).mp result
          exact ⟨present, rfl⟩

theorem complete {e : Expr} {v : Value} {s t : Store}
    (fragment : Fragment e) (trace : Steps ⟨e, s⟩ ⟨v.val, t⟩) :
    Returns (denote e) s v t := by
  have all {before after : Config} (trace : Steps before after) (admitted : Fragment before.expr) :
      Fragment after.expr ∧ Includes (denote before.expr) before.store (denote after.expr) after.store := by
    induction trace with
    | refl => exact ⟨admitted, fun {_ _} result => result⟩
    | tail _ step ih =>
        obtain ⟨admitted', back⟩ := ih
        obtain ⟨admitted'', back'⟩ := reflect admitted' step
        exact ⟨admitted'', fun {_ _} result => back (back' result)⟩
  apply (all trace fragment).2
  rw [denote_value]
  exact (returns_pure _ _ _ _).mpr ⟨rfl, rfl⟩

/-- Exact may adequacy at concrete values and final stores, including every
fresh choice made by the source relation. -/
theorem adequate {e : Expr} {v : Value} {s t : Store} (fragment : Fragment e) :
    Returns (denote e) s v t ↔ Steps ⟨e, s⟩ ⟨v.val, t⟩ :=
  ⟨sound fragment, complete fragment⟩

/-- Exact may adequacy for an open expression after instantiating it with a
lexical environment. Both sides retain the returned expression and store. -/
theorem adequateWith {e : Expr} {v : Value} {s t : Store}
    (env : Environment) (fragment : Fragment e) :
    Returns (denoteWith env e) s v t ↔ Steps ⟨e.subst env.substitution, s⟩ ⟨v.val, t⟩ := by
  have instantiated : denote (e.subst env.substitution) = denoteWith env e := by
    rw [denote, denoteWith_subst, compose_empty]
  rw [← instantiated]
  exact adequate (fragment.subst_environment env)

/-- Interpretation preserves the result type and tracks each possible extension
of the location environment through the source preservation theorem. -/
theorem typed_return {Θ : LocTypes} {e : Expr} {T : Ty} {s t : Store} {v : Value}
    (fragment : Fragment e) (typed : HasType Θ .empty e T) (store : StoreTyped Θ s)
    (returned : Returns (denote e) s v t) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty v.val T ∧ StoreTyped Θ' t :=
  preservation_steps (sound fragment returned) typed store

theorem typed_returnWith {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    {s t : Store} {v : Value} (env : Environment) (fragment : Fragment e)
    (typed : HasType Θ Γ e T) (noFree : Γ.free = ∅)
    (bindings : TypedSubst Θ Γ.bound .empty env.substitution) (store : StoreTyped Θ s)
    (returned : Returns (denoteWith env e) s v t) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty v.val T ∧ StoreTyped Θ' t :=
  preservation_steps (soundWith env fragment returned)
    (typed.subst env.substitution noFree bindings) store

theorem adequate_data {T : Ty} {shape : DataType T} {e : Expr} {s t : Store}
    {result : shape.Result} (fragment : Fragment e) :
    shape.Observes e s result t ↔ Steps ⟨e, s⟩ ⟨(shape.value result).val, t⟩ :=
  adequate fragment

theorem DataType.value_typed {T : Ty} (shape : DataType T) (result : shape.Result)
    (Θ : LocTypes) (Γ : VarTypes) : HasType Θ Γ (shape.value result).val T := by
  induction shape with
  | int => exact .int result
  | bool => exact .bool result
  | unit => exact .skip
  | prod _ _ ihl ihr => exact .pair (ihl result.1) (ihr result.2)
  | sum _ _ ihl ihr =>
      cases result with
      | inl x => exact .inl (ihl x)
      | inr x => exact .inr (ihr x)
  | record _ ih => exact .record (fun i => ih i (result i))

theorem DataType.exists_result {T : Ty} (shape : DataType T) {Θ : LocTypes} {v : Value}
    (typed : HasType Θ .empty v.val T) :
    ∃ result : shape.Result, shape.value result = v := by
  induction shape generalizing v with
  | int =>
      rcases v with ⟨_, ready⟩
      cases ready <;> cases typed
      exact ⟨_, rfl⟩
  | bool =>
      rcases v with ⟨_, ready⟩
      cases ready <;> cases typed
      exact ⟨_, rfl⟩
  | unit =>
      rcases v with ⟨_, ready⟩
      cases ready <;> cases typed
      exact ⟨(), rfl⟩
  | prod _ _ ihl ihr =>
      rcases v with ⟨_, ready⟩
      cases ready <;> cases typed
      rename_i a b va vb ha hb
      obtain ⟨left, eqL⟩ := ihl (v := ⟨a, va⟩) ha
      obtain ⟨right, eqR⟩ := ihr (v := ⟨b, vb⟩) hb
      refine ⟨(left, right), ?_⟩
      simp only [DataType.value, eqL, eqR]
      rfl
  | sum _ _ ihl ihr =>
      rcases v with ⟨_, ready⟩
      cases ready <;> cases typed
      · obtain ⟨left, eq⟩ := ihl (v := ⟨_, by assumption⟩) (by assumption)
        exact ⟨.inl left, by simp only [DataType.value, eq]; rfl⟩
      · obtain ⟨right, eq⟩ := ihr (v := ⟨_, by assumption⟩) (by assumption)
        exact ⟨.inr right, by simp only [DataType.value, eq]; rfl⟩
  | record fs ih =>
      rcases v with ⟨_, ready⟩
      cases ready <;> cases typed
      rename_i labels _ _ ready typed
      have each i := ih i (v := ⟨_, ready i⟩) (typed i)
      choose data eq using each
      refine ⟨data, Subtype.ext ?_⟩
      change Expr.record labels (fun i => ((fs i).value (data i)).val) = _
      congr 1
      funext i
      exact congrArg Subtype.val (eq i)

/-- Every return of a typed data program has an observation at its declared
type. This includes the ground types, products, sums and records. -/
theorem data_return {T : Ty} (shape : DataType T) {Θ : LocTypes} {e : Expr} {s t : Store}
    {v : Value} (fragment : Fragment e) (typed : HasType Θ .empty e T) (store : StoreTyped Θ s)
    (returned : Returns (denote e) s v t) :
    ∃ result : shape.Result, shape.Observes e s result t ∧ shape.value result = v := by
  obtain ⟨_, _, typed', _⟩ := typed_return fragment typed store returned
  obtain ⟨result, rfl⟩ := shape.exists_result typed'
  exact ⟨result, returned, rfl⟩

end Silmaril.Courses.Cambridge.L3.Denotation
