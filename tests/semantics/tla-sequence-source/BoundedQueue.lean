module

public import Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Thms
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Defs
public import Lean
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Defs
public meta import Lean

/-! Checked equations for selected definitions of the original BoundedQueue fixture. -/

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.BoundedQueue

open Resolution DataElab Data.Tagged

private meta abbrev root : ModuleId := "fixture/BoundedQueue"
private meta abbrev declaration (index : Nat) : BindingId := .declared ⟨root, [.unit index]⟩
private meta abbrev messagesId : BindingId := .declared ⟨root, [.unit 0, .member 0]⟩
private meta abbrev capacityId : BindingId := .declared ⟨root, [.unit 0, .member 1]⟩
private meta abbrev queueId : BindingId := .declared ⟨root, [.unit 1, .member 0]⟩

meta section

open Lean
open Elab.Term (TermElabM)

private def parse (path : System.FilePath) : TermElabM Surface.Module := do
  match Surface.Parser.parseModule (← IO.FS.readFile path) with
  | .ok source => return source
  | .error error => throwError "{path}: {reprStr error}"

private def declaredOperator : Surface.ModuleUnit → Option (Resolution.Name × Nat)
  | .definition (.operator .ordinary (.ident name params) _) => some (.ident name, params.length)
  | .definition (.operator .ordinary (.infix _ (.symbol name) _) _) =>
      some ((Resolution.Name.symbol .infix name).canonical, 2)
  | _ => none

private def verifyLibrary (dir : System.FilePath) : TermElabM Unit := do
  unless (← IO.getEnv "SILMARIL_TLA_SEQUENCE_REVISION") = some Sequences.revision do
    throwError "standard library revision does not match the interpretation"
  for (_, input) in Sequences.inputs do
    let .signature name [] declarations := input | throwError "unexpected library input"
    let source ← parse (dir / (name ++ ".tla"))
    unless source.name = name ∧ source.extendsModules = [] do
      throwError "unexpected header or EXTENDS in {name}"
    if name = "Sequences" then
      let some (Surface.ModuleUnit.instantiation .local instance_) := source.units[0]?
        | throwError "expected LOCAL INSTANCE Naturals in Sequences"
      unless instance_.moduleName = "Naturals" ∧ instance_.substitutions.isEmpty do
        throwError "unexpected Sequences instance"
    for entry in declarations do
      let .operator operator slots := entry | throwError "expected an operator signature"
      unless (source.units.filterMap declaredOperator).count (operator.canonical, slots.length) = 1 do
        throwError "{name}: expected one declaration of {reprStr operator} with arity {slots.length}"

private def checkedRegistry : TermElabM CheckedRegistry := do
  let some library ← IO.getEnv "SILMARIL_TLA_SEQUENCE_FIXTURES"
    | throwError "stage the pinned standard library with tla-sequence-source/check.py"
  let some fixture ← IO.getEnv "SILMARIL_TLA_QUEUE_FIXTURE"
    | throwError "stage the BoundedQueue fixture with tla-sequence-source/check.py"
  verifyLibrary library
  let source ← parse fixture
  unless source.name = "BoundedQueue" ∧ source.extendsModules = ["Naturals", "Sequences"] do
    throwError "unexpected BoundedQueue header"
  let [.constants _, .variables ["q"], .assumption none _, .definition init, .definition enqueue,
       .definition dequeue, .definition next, .definition typeOK, .definition spec,
       .theoremDecl ⟨some "QueueSafety", _, some _⟩] := source.units
    | throwError "unexpected BoundedQueue units"
  let selected := { source with units := source.units.take 2 ++
    [.definition init, .definition enqueue, .definition dequeue, .definition next,
      .definition typeOK, .definition spec] }
  let imports := [("Naturals", Sequences.naturalsId), ("Sequences", Sequences.sequencesId)]
  let inputs := (root, ModuleInput.parsed selected imports) :: Sequences.inputs
  let registry ← match resolveWith .levelSyntax inputs root with
    | .ok registry => pure registry
    | .error error => throwError "BoundedQueue resolution: {reprStr error}"
  let some checked := registry.moduleAt root | throwError "missing BoundedQueue registry entry"
  for (name, id) in [("Init", declaration 2), ("Next", declaration 5), ("TypeOK", declaration 6),
      ("Messages", messagesId), ("Capacity", capacityId), ("q", queueId)] do
    unless (checked.bindingAt (.ident name)).map (·.id) = some id do
      throwError "unexpected BoundedQueue declaration for {name}"
  return registry

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId
deriving instance ToExpr for Surface.Junction
deriving instance ToExpr for Surface.Quantifier
deriving instance ToExpr for BinderMap
deriving instance ToExpr for BinderPattern
deriving instance ToExpr for Bounded

private partial def quoteTerm (term : Term Sequences.signature .collections) : TermElabM Lean.Expr := do
  let signature := mkConst ``Sequences.signature
  let ctor := fun name => mkApp2 (mkConst name) signature (mkConst ``Fragment.collections)
  let type := ctor ``DataElab.Term
  let node := fun name args => mkAppN (ctor name) args
  let list := fun args => do Meta.mkListLit type (← args.mapM quoteTerm)
  let enabled ← Meta.mkEqRefl (mkConst ``Fragment.collections)
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .flexible id => return node ``Term.flexible #[toExpr id]
  | .witness slot => return node ``Term.witness #[toExpr slot]
  | .prime site operand => return node ``Term.prime #[toExpr site, ← quoteTerm operand]
  | .eq negated left right =>
    return node ``Term.eq #[toExpr negated, ← quoteTerm left, ← quoteTerm right]
  | .mem negated element set =>
    return node ``Term.mem #[toExpr negated, ← quoteTerm element, ← quoteTerm set]
  | .junction kind args => return node ``Term.junction #[toExpr kind, ← list args]
  | .bounded _ kind groups body =>
    let groupType := mkApp2 (mkConst ``Prod [0, 0])
      (mkApp (mkConst ``List [0]) (mkConst ``BinderPattern)) type
    let entries ← groups.mapM fun (patterns, bound) => do
      Meta.mkAppM ``Prod.mk #[toExpr patterns, ← quoteTerm bound]
    return node ``Term.bounded #[enabled, toExpr kind, ← Meta.mkListLit groupType entries,
      ← quoteTerm body]
  | .tuple _ args => return node ``Term.tuple #[enabled, ← list args]
  | .external id arity _ args =>
    let .declared site := id | throwError "unexpected external ID: {reprStr id}"
    let library ←
      if site.moduleId = Sequences.sequencesId then pure (mkConst ``Sequences.sequencesId)
      else if site.moduleId = Sequences.naturalsId then pure (mkConst ``Sequences.naturalsId)
      else throwError "unexpected external module: {site.moduleId}"
    let key := mkApp (mkConst ``BindingId.declared)
      (mkApp2 (mkConst ``Site.mk) library (toExpr site.path))
    let admitted ← Meta.mkEqRefl (toExpr (some arity))
    return node ``Term.external #[key, toExpr arity, admitted, ← list args]
  | other => throwError "unexpected expanded BoundedQueue term: {reprStr other}"

private def quoteChecked (expression : CheckedExpr Sequences.signature .collections) :
    TermElabM Lean.Expr :=
  return mkApp4 (mkConst ``CheckedExpr.mk) (mkConst ``Sequences.signature)
    (mkConst ``Fragment.collections) (← quoteTerm expression.term) (← Meta.mkEqRefl (toExpr true))

private def emitSelections : TermElabM Lean.Expr := do
  let registry ← checkedRegistry
  let state := fun id => Collections.lowerState registry Sequences.levels Sequences.signature 16 id
  let action := Collections.lowerAction registry Sequences.levels Sequences.signature 16 (declaration 5)
  let init ← match state (declaration 2) with
    | .ok expr => pure expr
    | .error diagnostic => throwError "Init lowering: {reprStr diagnostic}"
  let typeOK ← match state (declaration 6) with
    | .ok expr => pure expr
    | .error diagnostic => throwError "TypeOK lowering: {reprStr diagnostic}"
  let next ← match action with
    | .ok expr => pure expr
    | .error diagnostic => throwError "Next lowering: {reprStr diagnostic}"
  let next ← Meta.mkAppM ``Collections.CheckedAction.mk #[← quoteChecked next.expression]
  let pair ← Meta.mkAppM ``Prod.mk #[← quoteChecked typeOK, next]
  logInfo "Pinned BoundedQueue: checked the definition fragment and selected Init, TypeOK and Next"
  Meta.mkAppM ``Prod.mk #[← quoteChecked init, pair]

end

private noncomputable def selections : CheckedExpr Sequences.signature .collections ×
    CheckedExpr Sequences.signature .collections × Collections.CheckedAction Sequences.signature :=
  by_elab emitSelections

open DataElab.Tagged (Policy CollectionPolicy)

private abbrev V := Value.{0}

private structure Profile where
  tagged : Policy.{0}
  invalidCollection : CollectionPolicy.{0}
  invalidSequence : SequencePolicy.{0}

private noncomputable def Profile.holds (profile : Profile)
    (expr : CheckedExpr Sequences.signature .collections) (env : Valuation V) : Prop :=
  profile.tagged.booleans.holds (expr.eval
    (profile.tagged.collectionOperations profile.invalidCollection) profile.tagged.booleans
    (Sequences.external profile.tagged profile.invalidSequence) env)

private noncomputable def Profile.step (profile : Profile) (env : Endpoints.EndpointValuation V) : Prop :=
  profile.tagged.booleans.holds (selections.2.2.eval
    (profile.tagged.collectionOperations profile.invalidCollection) profile.tagged.booleans
    (Sequences.external profile.tagged profile.invalidSequence) env)

private theorem init_iff (profile : Profile) (env : Valuation V) :
    profile.holds selections.1 env ↔ env.flexible queueId = Value.tuple [] := by
  exact Booleans.holds_ofProp profile.tagged.booleans _

private theorem isBoolean_ofProp (B : Booleans V) (p : Prop) :
    B.IsBoolean (B.ofProp p) := by
  classical
  by_cases h : p <;> simp [Booleans.IsBoolean, h]

private theorem true_eq_ofProp (B : Booleans V) (p : Prop) :
    B.trueValue = B.ofProp p ↔ p := by
  classical
  have different : B.trueValue ≠ B.falseValue := fun eq => B.not_holds_false (eq ▸ B.holds_true)
  by_cases h : p <;> simp [h, different]

private theorem false_eq_ofProp (B : Booleans V) (p : Prop) :
    B.falseValue = B.ofProp p ↔ ¬ p := by
  classical
  have different : B.falseValue ≠ B.trueValue := fun eq => B.not_holds_false (eq ▸ B.holds_true)
  by_cases h : p <;> simp [h, different]

open Classical in
private theorem junction_and (B : Booleans V) (p q : Prop) :
    (if B.falseValue ∈ [B.ofProp p, B.ofProp q] then B.falseValue
     else if ∀ v ∈ [B.ofProp p, B.ofProp q], B.IsBoolean v then B.trueValue
     else B.invalid (.junction .conjunction) [B.ofProp p, B.ofProp q]) = B.ofProp (p ∧ q) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, false_eq_ofProp, forall_eq_or_imp,
    forall_eq, isBoolean_ofProp, and_true, ite_true]
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

open Classical in
private theorem junction_or (B : Booleans V) (p q : Prop) :
    (if B.trueValue ∈ [B.ofProp p, B.ofProp q] then B.trueValue
     else if ∀ v ∈ [B.ofProp p, B.ofProp q], B.IsBoolean v then B.falseValue
     else B.invalid (.junction .disjunction) [B.ofProp p, B.ofProp q]) = B.ofProp (p ∨ q) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, true_eq_ofProp, forall_eq_or_imp,
    forall_eq, isBoolean_ofProp, and_true, ite_true]
  by_cases h : p ∨ q <;> simp [h]

private theorem seqSelected :
    Sequences.operatorAt (.declared ⟨Sequences.sequencesId, [.member 0]⟩) = some (.inr .seq) := by rfl

private theorem lenSelected :
    Sequences.operatorAt (.declared ⟨Sequences.sequencesId, [.member 1]⟩) = some (.inr .len) := by rfl

private theorem leSelected :
    Sequences.operatorAt (.declared ⟨Sequences.naturalsId, [.member 2]⟩) = some (.inl .le) := by rfl

private theorem typeOK_iff (profile : Profile) (env : Valuation V) (alphabet : SetData.{0})
    (capacity : Nat) (xs : List V)
    (messages : env.rigid messagesId = Value.set alphabet)
    (bound : env.rigid capacityId = Value.integer capacity)
    (queue : env.flexible queueId = Value.tuple xs) :
    profile.holds selections.2.1 env ↔
      (∀ m ∈ xs, alphabet.mem m) ∧ xs.length ≤ capacity := by
  classical
  simp only [Profile.holds, selections, CheckedExpr.eval, Term.eval, Term.evalList,
    Bool.false_eq_true, ite_false]
  simp only [Sequences.external_apply profile.tagged profile.invalidSequence (arity := 1)
      seqSelected (by rfl),
    Sequences.external_apply profile.tagged profile.invalidSequence (arity := 1)
      lenSelected (by rfl),
    Sequences.external_apply profile.tagged profile.invalidSequence (arity := 2)
      leSelected (by rfl)]
  rw [queue, messages, bound]
  simp only [Operations.base, DataElab.Tagged.Policy.collectionOperations, DataElab.Tagged.Policy.mem_value,
    Sequences.seq_apply, Sequences.len_apply, Sequences.numeric_apply,
    DataElab.Tagged.Policy.le_apply, Value.seq_set, Value.mem_set, SetData.tuple_mem_sequences,
    Value.len_tuple, Value.le_integer, Int.ofNat_le]
  rw [← DataElab.Tagged.Policy.ofProp_eq profile.tagged]
  rw [junction_and, Booleans.holds_ofProp]

private theorem ltSelected :
    Sequences.operatorAt (.declared ⟨Sequences.naturalsId, [.member 1]⟩) = some (.inl .lt) := by rfl

private theorem appendSelected :
    Sequences.operatorAt (.declared ⟨Sequences.sequencesId, [.member 2]⟩) = some (.inr .append) := by rfl

private theorem tailSelected :
    Sequences.operatorAt (.declared ⟨Sequences.sequencesId, [.member 4]⟩) = some (.inr .tail) := by rfl

private theorem lt_of_integers (policy : Policy.{0}) (a b : Int) :
    Value.lt policy.numeric (.integer a) (.integer b) = policy.booleans.ofProp (a < b) := by
  simp only [Value.lt, Value.le_integer, Value.isTrue_ofProp, ne_eq, Value.integer_injective.eq_iff]
  rw [← lt_iff_le_and_ne, DataElab.Tagged.Policy.ofProp_eq]

/-- The original disjunction selects an admitted enqueue with a message
witness, or a guarded dequeue. Both branches read the prime at the target. -/
private theorem next_iff (profile : Profile) (env : Endpoints.EndpointValuation V)
    (alphabet : SetData.{0}) (capacity : Nat) (xs : List V)
    (messages : env.rigid messagesId = Value.set alphabet)
    (bound : env.rigid capacityId = Value.integer capacity)
    (queue : env.source queueId = Value.tuple xs) :
    profile.step env ↔
      (∃ m, alphabet.mem m ∧ xs.length < capacity ∧ env.target queueId = Value.tuple (xs ++ [m])) ∨
      (∃ m rest, xs = m :: rest ∧ env.target queueId = Value.tuple rest) := by
  classical
  simp only [Profile.step, selections, Collections.CheckedAction.eval, Term.eval, Term.evalList,
    Term.evalBounds, Bool.false_eq_true, ite_false, ite_true, Bounded.axes, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil, Bounded.quantify, BinderPattern.bind]
  simp only [Sequences.external_apply profile.tagged profile.invalidSequence (arity := 2)
      ltSelected (by rfl),
    Sequences.external_apply profile.tagged profile.invalidSequence (arity := 1)
      lenSelected (by rfl),
    Sequences.external_apply profile.tagged profile.invalidSequence (arity := 2)
      appendSelected (by rfl),
    Sequences.external_apply profile.tagged profile.invalidSequence (arity := 1)
      tailSelected (by rfl)]
  rw [queue, messages, bound]
  simp only [Sequences.numeric_apply, DataElab.Tagged.Policy.lt_apply, Sequences.len_apply,
    Sequences.append_apply, Sequences.tail_apply, Value.len_tuple, Value.append_tuple, lt_of_integers,
    Int.ofNat_lt, Operations.collection, cast_eq, DataElab.Tagged.Policy.collectionOperations,
    DataElab.Tagged.Policy.mem_value, Value.mem_set, Option.some.injEq,
    Value.tuple_injective.eq_iff, junction_and, junction_or, Booleans.holds_ofProp]
  cases xs <;> simp [queueId, root, withWitness]

private def QueueInvariant (alphabet : SetData.{0}) (capacity : Nat) (queue : V) : Prop :=
  ∃ xs : List V, queue = Value.tuple xs ∧ (∀ m ∈ xs, alphabet.mem m) ∧ xs.length ≤ capacity

private theorem init_establishes (profile : Profile) (env : Valuation V)
    (alphabet : SetData.{0}) (capacity : Nat) (init : profile.holds selections.1 env) :
    QueueInvariant alphabet capacity (env.flexible queueId) :=
  ⟨[], (init_iff profile env).mp init, by simp, Nat.zero_le _⟩

private theorem next_preserves (profile : Profile) (env : Endpoints.EndpointValuation V)
    (alphabet : SetData.{0}) (capacity : Nat)
    (messages : env.rigid messagesId = Value.set alphabet)
    (bound : env.rigid capacityId = Value.integer capacity)
    (source : QueueInvariant alphabet capacity (env.source queueId))
    (step : profile.step env ∨ env.target queueId = env.source queueId) :
    QueueInvariant alphabet capacity (env.target queueId) := by
  rcases step with action | same
  · obtain ⟨xs, queue, contents, size⟩ := source
    rcases (next_iff profile env alphabet capacity xs messages bound queue).mp action with
      ⟨m, member, room, target⟩ | ⟨m, rest, rfl, target⟩
    · refine ⟨xs ++ [m], target, ?_, by simpa using Nat.succ_le_of_lt room⟩
      intro x hx
      rcases List.mem_append.mp hx with old | new
      · exact contents x old
      · simpa [List.mem_singleton.mp new] using member
    · exact ⟨rest, target, fun x hx => contents x (List.mem_cons_of_mem _ hx), by
        simp only [List.length_cons] at size
        omega⟩
  · exact same ▸ source

private theorem invariant_typeOK (profile : Profile) (env : Valuation V)
    (alphabet : SetData.{0}) (capacity : Nat)
    (messages : env.rigid messagesId = Value.set alphabet)
    (bound : env.rigid capacityId = Value.integer capacity)
    (invariant : QueueInvariant alphabet capacity (env.flexible queueId)) :
    profile.holds selections.2.1 env := by
  obtain ⟨xs, queue, contents, size⟩ := invariant
  exact (typeOK_iff profile env alphabet capacity xs messages bound queue).mpr ⟨contents, size⟩

private theorem zero_based_graph (invalid : SequencePolicy.{0}) (x : V) :
    let g := Graph.ofFn (SetData.intRange 0 1) (fun _ => x)
    let s := Value.function g
    s.len invalid = invalid .len [s] ∧ s.head invalid = x := by
  intro g s
  have zeroKey : g.domain.mem (.integer 0) := by
    simp [g, SetData.integer_mem_intRange]
  refine ⟨Value.len_nonsequence invalid (Value.asSequence_eq_none.mpr ?_), ?_⟩
  · rintro ⟨h, same, n, shape⟩
    have sameGraph : h = g := Value.function_injective same
    rw [← sameGraph, shape, SetData.integer_mem_intRange] at zeroKey
    omega
  · exact Value.head_function invalid (Graph.relates_ofFn.mpr
      ⟨(SetData.integer_mem_intRange 0 1 1).mpr (by decide), rfl⟩)

private theorem singleton_every_length (x : V) (n : Nat) :
    (SetData.enum [x]).sequences.mem (Value.tuple (List.replicate n x)) := by
  rw [SetData.tuple_mem_sequences]
  intro m hm
  simpa using (List.eq_of_mem_replicate hm)

example : Sequences.signature (.declared ⟨"Sequences", [.member 0]⟩) = none := by rfl

open Lean in
run_cmd do
  let declarations := [``Graph.tuple_of_domain, ``SetData.mem_sequences,
    ``SetData.mem_sequences_iff_tuple, ``Value.asSequence_eq_none, ``Value.seq_set,
    ``Value.len_tuple, ``Value.append_tuple, ``Value.head_cons, ``Value.tail_cons,
    ``Value.head_empty, ``Value.tail_empty, ``Sequences.external_apply,
    ``init_iff, ``typeOK_iff, ``next_iff, ``init_establishes, ``next_preserves,
    ``invariant_typeOK, ``zero_based_graph, ``singleton_every_length]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in declarations do
    let axioms ← collectAxioms name
    unless axioms.all (· ∈ allowed) do
      throwError "unexpected axioms for {name}: {axioms}"
  logInfo m!"Axiom audit passed for {declarations.length} sequence and queue theorems"

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.BoundedQueue
