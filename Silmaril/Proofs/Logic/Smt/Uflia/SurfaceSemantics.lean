module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Defs

/-!
# Compositional preservation for direct surface evaluation

The hypotheses below are recursive induction hypotheses about children, not an
external semantic certificate accepted by the frontend. The results connect
actual decoder equations to the independently defined surface relation.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface

open Silmaril.Logic.Algebraic

attribute [local instance] Classical.propDecidable

variable {input output : SortCode String}

def Unary.operation {E : Environment} : Unary input output →
    Operation E.signature 1 (fun _ => input) output
  | .not => .not
  | .neg => .scale (-1)

/-- Literal evaluation is independent of decoding and of UF interpretations. -/
theorem boolean_holds (E : Environment) (M : Packaged.GlobalModel) :
    Holds E M (.atom "true") := Evaluates.boolean true

/-- Arbitrary recursive operands: unary elaboration preserves direct meaning. -/
theorem unary_preserves {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (op : Unary input output) (e : Expr) (t : Uflia.Term E.signature input)
    (decoded : recur e = some ⟨input, t⟩) :
    ∃ result : PackedTerm E,
      unary? recur op.operation e = some result ∧
      Evaluates E M scope (.list [.atom op.token, e]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  let result : PackedTerm E := ⟨output, .app op.operation (fun _ => t)⟩
  refine ⟨result, ?_, ?_⟩
  · simp [unary?, decoded, PackedTerm.expect?, result]
  · have child := sound e ⟨input, t⟩ decoded
    have direct := Evaluates.unary op child
    cases op with
    | not => exact direct
    | neg =>
      change Evaluates E M scope (.list [.atom "-", e]) .int
        ((-1) * (M.reduct (Packaged.nameMap E)).eval t)
      simpa [Unary.token, Unary.value] using direct

/-- Equality elaboration compares the actual carrier values, including user
sorts; it does not use syntactic equality or an SMT solver's answer. -/
theorem equality_preserves {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (sort : SortCode String) (a b : Expr) (x y : Uflia.Term E.signature sort)
    (left : recur a = some ⟨sort, x⟩) (right : recur b = some ⟨sort, y⟩) :
    ∃ result : PackedTerm E,
      equality? recur a b = some result ∧
      Evaluates E M scope (.list [.atom "=", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨.bool, .app (.eq sort) (Fin.cases x (fun _ => y))⟩, ?_, ?_⟩
  · simp [equality?, left, right, PackedTerm.expect?]
  · exact Evaluates.equality (sound a ⟨sort, x⟩ left) (sound b ⟨sort, y⟩ right)

/-- Conditional elaboration preserves arbitrary-sort branches recursively. -/
theorem ite_preserves {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (sort : SortCode String) (c a b : Expr)
    (test : Uflia.Term E.signature .bool) (x y : Uflia.Term E.signature sort)
    (condition : recur c = some ⟨.bool, test⟩)
    (left : recur a = some ⟨sort, x⟩) (right : recur b = some ⟨sort, y⟩) :
    ∃ result : PackedTerm E,
      ite? recur c a b = some result ∧
      Evaluates E M scope (.list [.atom "ite", c, a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨sort, .app (.ite sort) (Fin.cases test (Fin.cases x (fun _ => y)))⟩, ?_, ?_⟩
  · simp [ite?, condition, left, right, PackedTerm.expect?]
  · have direct := Evaluates.ite (sound c ⟨.bool, test⟩ condition)
      (sound a ⟨sort, x⟩ left) (sound b ⟨sort, y⟩ right)
    have evaluation :
        (M.reduct (Packaged.nameMap E)).eval
          (.app (.ite sort) (Fin.cases test (Fin.cases x (fun _ => y)))) =
        (if (M.reduct (Packaged.nameMap E)).eval test = true then
          (M.reduct (Packaged.nameMap E)).eval x else
          (M.reduct (Packaged.nameMap E)).eval y) := by
      dsimp only [Model.eval, Model.algebra, ManySorted.Model.eval, Model.apply]
      congr 1
    change Evaluates E M scope (.list [.atom "ite", c, a, b]) sort _
    rw [evaluation]
    exact direct


/-- One full recursive decoder branch, with arbitrary outer locals and arbitrary
accepted child syntax. The operand's independent meaning is the induction
hypothesis. This theorem does not identify direct meaning with decoding. -/
theorem decode_not_preserves {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (e : Expr) (t : Uflia.Term E.signature .bool)
    (decoded : decodeScopedFuel? E fuel locals e = some ⟨.bool, t⟩) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list [.atom "not", e]) = some result ∧
      Evaluates E M scope (.list [.atom "not", e]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  exact unary_preserves M scope (decodeScopedFuel? E fuel locals) sound .not e t decoded

/-- A binary conjunction uses the actual variadic decoder branch. Its children
may be any independently justified accepted syntax, not just Boolean literals. -/
theorem decode_and_preserves {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (a b : Expr) (x y : Uflia.Term E.signature .bool)
    (left : decodeScopedFuel? E fuel locals a = some ⟨.bool, x⟩)
    (right : decodeScopedFuel? E fuel locals b = some ⟨.bool, y⟩) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list [.atom "and", a, b]) = some result ∧
      Evaluates E M scope (.list [.atom "and", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨.bool, .app .and (Fin.cases x (fun _ => y))⟩, ?_, ?_⟩
  · change fold? (decodeScopedFuel? E fuel locals) .and [a, b] = _
    simp [fold?, typedTerms?, left, right, PackedTerm.expect?, foldTerms, pair]
  · exact Evaluates.binary .and (sound a ⟨.bool, x⟩ left) (sound b ⟨.bool, y⟩ right)

/-- Binary equality uses the real chained-equality branch; the helper theorem
above is not silently substituted for the frontend's actual dispatch. -/
theorem decode_equality_preserves {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (sort : SortCode String) (a b : Expr) (x y : Uflia.Term E.signature sort)
    (left : decodeScopedFuel? E fuel locals a = some ⟨sort, x⟩)
    (right : decodeScopedFuel? E fuel locals b = some ⟨sort, y⟩) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list [.atom "=", a, b]) = some result ∧
      Evaluates E M scope (.list [.atom "=", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨.bool, .app (.eq sort) (Fin.cases x (fun _ => y))⟩, ?_, ?_⟩
  · change equalities? (decodeScopedFuel? E fuel locals) false [a, b] = _
    simp [equalities?, typedTerms?, left, right, PackedTerm.expect?,
      adjacent, conjunction, foldTerms]
  · exact Evaluates.equality (sound a ⟨sort, x⟩ left) (sound b ⟨sort, y⟩ right)

def FoldOp.operation {E : Environment} {sort : SortCode String} : FoldOp sort →
    Operation E.signature 2 (fun _ => sort) sort
  | .and => .and
  | .or => .or
  | .add => .add
  | .sub => .sub

/-- Successful typed child checks preserve the child's value after sort casting. -/
theorem typed_child_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (sort : SortCode String) (e : Expr) (t : Uflia.Term E.signature sort)
    (decoded : (do let packed ← recur e; packed.expect? sort) = some t) :
    Evaluates E M scope e sort ((M.reduct (Packaged.nameMap E)).eval t) := by
  cases h : recur e with
  | none => simp [h] at decoded
  | some packed =>
    rcases packed with ⟨result, term⟩
    by_cases same : result = sort
    · subst result
      simp [h, PackedTerm.expect?] at decoded
      subst t
      exact sound e ⟨sort, term⟩ h
    · simp [h, PackedTerm.expect?, same] at decoded

/-- A successful monadic list traversal retains a pointwise relation. -/
theorem mapM_forall₂ {α β : Type} (f : α → Option β) (R : α → β → Prop)
    (pointwise : ∀ a b, f a = some b → R a b)
    (as : List α) (bs : List β) (decoded : as.mapM f = some bs) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil =>
    simp at decoded
    subst bs
    exact .nil
  | cons a as ih =>
    cases first : f a with
    | none => simp [first] at decoded
    | some b =>
      cases rest : as.mapM f with
      | none => simp [first, rest] at decoded
      | some bs' =>
        have step : (a :: as).mapM f = some (b :: bs') := by simp [first, rest]
        rw [step] at decoded
        cases decoded
        exact .cons (pointwise a b first) (ih bs' rest)

/-- Every successfully decoded typed operand list has direct source meanings. -/
theorem typedTerms_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (sort : SortCode String) (es : List Expr) (ts : List (Uflia.Term E.signature sort))
    (decoded : typedTerms? recur sort es = some ts) :
    OperandsEvaluate E M scope sort es
      (ts.map (fun t => (M.reduct (Packaged.nameMap E)).eval t)) := by
  have paired := mapM_forall₂ (fun e => do let t ← recur e; t.expect? sort)
    (fun e t => Evaluates E M scope e sort ((M.reduct (Packaged.nameMap E)).eval t))
    (typed_child_preserves M scope recur sound sort) es ts decoded
  clear decoded
  induction paired with
  | nil => exact .nil scope sort
  | cons h rest ih => exact .cons h ih

/-- Left folding elaborated terms agrees with left folding carrier values. -/
theorem foldTerms_value {E : Environment} (M : Packaged.GlobalModel)
    {sort : SortCode String} (op : FoldOp sort)
    (first : Uflia.Term E.signature sort) (rest : List (Uflia.Term E.signature sort)) :
    (M.reduct (Packaged.nameMap E)).eval (foldTerms op.operation first rest) =
      (rest.map (fun t => (M.reduct (Packaged.nameMap E)).eval t)).foldl (op.value M)
        ((M.reduct (Packaged.nameMap E)).eval first) := by
  have pairValue (x y : Uflia.Term E.signature sort) :
      (M.reduct (Packaged.nameMap E)).eval (pair op.operation x y) =
        op.value M ((M.reduct (Packaged.nameMap E)).eval x)
          ((M.reduct (Packaged.nameMap E)).eval y) := by cases op <;> rfl
  induction rest generalizing first with
  | nil => rfl
  | cons t ts ih =>
    change (M.reduct (Packaged.nameMap E)).eval
      (foldTerms op.operation (pair op.operation first t) ts) = _
    rw [ih, pairValue]
    rfl

/-- All admitted variadic folds preserve meaning at every arity, using actual
recursive operand results and the typed-list traversal. -/
theorem fold_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    {sort : SortCode String} (op : FoldOp sort) (a b : Expr) (rest : List Expr)
    (x : Uflia.Term E.signature sort) (xs : List (Uflia.Term E.signature sort))
    (first : recur a = some ⟨sort, x⟩)
    (remaining : typedTerms? recur sort (b :: rest) = some xs) :
    ∃ result : PackedTerm E,
      fold? recur op.operation (a :: b :: rest) = some result ∧
      Evaluates E M scope (.list (.atom op.token :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨sort, foldTerms op.operation x xs⟩, ?_, ?_⟩
  · simp [fold?, first, PackedTerm.expect?, remaining]
  · change Evaluates E M scope _ sort _
    rw [foldTerms_value]
    exact Evaluates.fold op a b rest _ _ (sound a ⟨sort, x⟩ first)
      (typedTerms_preserves M scope recur sound sort (b :: rest) xs remaining)

/-- The actual decoder dispatch for and/or/add/sub is covered at arbitrary
accepted arity; subtraction's unary case remains the separate negation rule. -/
theorem decode_fold_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    {sort : SortCode String} (op : FoldOp sort) (a b : Expr) (rest : List Expr)
    (x : Uflia.Term E.signature sort) (xs : List (Uflia.Term E.signature sort))
    (first : decodeScopedFuel? E fuel locals a = some ⟨sort, x⟩)
    (remaining : typedTerms? (decodeScopedFuel? E fuel locals) sort (b :: rest) = some xs) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals
        (.list (.atom op.token :: a :: b :: rest)) = some result ∧
      Evaluates E M scope (.list (.atom op.token :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have preserved := fold_preserves M scope (decodeScopedFuel? E fuel locals)
    sound op a b rest x xs first remaining
  cases op <;> exact preserved

/-- Boolean left folds coincide with conjunction over the operand list. -/
theorem bool_fold_and (values : List Bool) (initial : Bool) :
    values.foldl (fun x y => x && y) initial = (initial && values.all id) := by
  induction values generalizing initial with
  | nil => simp
  | cons b bs ih => simp [ih, Bool.and_assoc]

/-- Conjunction of elaborated formulas evaluates to conjunction of their values. -/
theorem conjunction_value {E : Environment} (M : Packaged.GlobalModel)
    (formulas : List (Formula E.signature)) :
    (M.reduct (Packaged.nameMap E)).eval (conjunction formulas) =
      formulas.all (fun formula => (M.reduct (Packaged.nameMap E)).eval formula) := by
  cases formulas with
  | nil => rfl
  | cons first rest =>
    change (M.reduct (Packaged.nameMap E)).eval (foldTerms FoldOp.and.operation first rest) = _
    rw [foldTerms_value]
    change (rest.map (fun t => (M.reduct (Packaged.nameMap E)).eval t)).foldl
      (fun x y : Bool => x && y) ((M.reduct (Packaged.nameMap E)).eval first) = _
    simpa only [List.all_map, List.all_cons, Function.comp_def, id] using bool_fold_and
      (rest.map (fun t => (M.reduct (Packaged.nameMap E)).eval t))
      ((M.reduct (Packaged.nameMap E)).eval first)

/-- List adjacency commutes with evaluation into carrier values. -/
theorem all_adjacent {α β : Type} (relation : α → α → β) (value : β → Bool)
    (as : List α) : (adjacent relation as).all value =
      adjacentValue (fun x y => value (relation x y)) as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b rest => simpa [adjacent, adjacentValue] using congrArg (value (relation a b) && ·) ih

/-- Mapping operands before an adjacent chain preserves source order. -/
theorem adjacentValue_map {α β : Type} (relation : β → β → Bool) (f : α → β)
    (as : List α) : adjacentValue relation (as.map f) =
      adjacentValue (fun a b => relation (f a) (f b)) as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b rest => simpa [adjacentValue] using congrArg (relation (f a) (f b) && ·) ih

/-- Every generated comparison link has the direct integer comparison value. -/
def CompareOp.operation {E : Environment} : CompareOp →
    Operation E.signature 2 (fun _ => .int) .bool
  | .le | .ge => .le
  | .lt | .gt => .lt

def CompareOp.reverse : CompareOp → Bool
  | .le | .lt => false
  | .ge | .gt => true

/-- Arbitrary-length comparison chains preserve direct values. -/
theorem compare_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (op : CompareOp) (a b : Expr) (rest : List Expr)
    (terms : List (Uflia.Term E.signature .int))
    (decoded : typedTerms? recur .int (a :: b :: rest) = some terms) :
    ∃ result : PackedTerm E,
      compare? recur op.operation op.reverse (a :: b :: rest) = some result ∧
      Evaluates E M scope (.list (.atom op.token :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  let relation : Uflia.Term E.signature .int → Uflia.Term E.signature .int →
      Formula E.signature := fun x y =>
    .app op.operation (Fin.cases (if op.reverse then y else x)
      (fun _ => if op.reverse then x else y))
  refine ⟨⟨.bool, conjunction (adjacent relation terms)⟩, ?_, ?_⟩
  · simp [compare?, decoded, relation]
  · change Evaluates E M scope _ .bool _
    rw [conjunction_value, all_adjacent]
    have links (x y : Uflia.Term E.signature .int) :
        (M.reduct (Packaged.nameMap E)).eval (relation x y) =
          op.value ((M.reduct (Packaged.nameMap E)).eval x)
            ((M.reduct (Packaged.nameMap E)).eval y) := by cases op <;> rfl
    simp_rw [links]
    rw [← adjacentValue_map]
    exact Evaluates.comparison op a b rest _
      (typedTerms_preserves M scope recur sound .int (a :: b :: rest) terms decoded)

/-- The decoder's actual comparison dispatch is covered for all four directions
and every accepted number of operands. -/
theorem decode_compare_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (op : CompareOp) (a b : Expr) (rest : List Expr)
    (terms : List (Uflia.Term E.signature .int))
    (decoded : typedTerms? (decodeScopedFuel? E fuel locals) .int (a :: b :: rest) = some terms) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list (.atom op.token :: a :: b :: rest)) = some result ∧
      Evaluates E M scope (.list (.atom op.token :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have preserved := compare_preserves M scope (decodeScopedFuel? E fuel locals)
    sound op a b rest terms decoded
  cases op <;> exact preserved

/-- The decoder's adjacent equalities have the direct carrier equality values. -/
theorem equalities_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (sort : SortCode String) (a b : Expr) (rest : List Expr)
    (first : Uflia.Term E.signature sort) (terms : List (Uflia.Term E.signature sort))
    (head : recur a = some ⟨sort, first⟩)
    (tail : typedTerms? recur sort (b :: rest) = some terms) :
    ∃ result : PackedTerm E,
      equalities? recur false (a :: b :: rest) = some result ∧
      Evaluates E M scope (.list (.atom "=" :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  let relation : Uflia.Term E.signature sort → Uflia.Term E.signature sort →
      Formula E.signature := fun x y => .app (.eq sort) (Fin.cases x (fun _ => y))
  refine ⟨⟨.bool, conjunction (adjacent relation (first :: terms))⟩, ?_, ?_⟩
  · simp [equalities?, head, tail, relation]
  · change Evaluates E M scope _ .bool _
    rw [conjunction_value, all_adjacent]
    have links (x y : Uflia.Term E.signature sort) :
        (M.reduct (Packaged.nameMap E)).eval (relation x y) =
          decide ((M.reduct (Packaged.nameMap E)).eval x =
            (M.reduct (Packaged.nameMap E)).eval y) := by rfl
    simp_rw [links]
    have direct := Evaluates.equalChain a b rest _
      (.cons (sound a ⟨sort, first⟩ head)
        (typedTerms_preserves M scope recur sound sort (b :: rest) terms tail))
    have mapping :
        adjacentValue (fun x y : M.carriers.value sort => decide (x = y))
          ((first :: terms).map (fun t => (M.reduct (Packaged.nameMap E)).eval t)) =
        adjacentValue (fun x y : Uflia.Term E.signature sort =>
          decide ((M.reduct (Packaged.nameMap E)).eval x =
            (M.reduct (Packaged.nameMap E)).eval y)) (first :: terms) := by
      erw [adjacentValue_map]
      apply congrArg (fun relation => adjacentValue relation (first :: terms))
      funext x y
      simp only [decide_eq_decide]
      rfl
    exact mapping ▸ direct

def disequalityTerm {E : Environment} (sort : SortCode String)
    (x y : Uflia.Term E.signature sort) : Formula E.signature :=
  .app .not (fun _ => .app (.eq sort) (Fin.cases x (fun _ => y)))

/-- Pairwise disequality evaluates all pairs, not merely adjacent values. -/
theorem distinctPairs_value {E : Environment} (M : Packaged.GlobalModel)
    (sort : SortCode String) (terms : List (Uflia.Term E.signature sort)) :
    (allPairs (disequalityTerm sort) terms).all
        (fun formula => (M.reduct (Packaged.nameMap E)).eval formula) =
      distinctValue (terms.map (fun term => (M.reduct (Packaged.nameMap E)).eval term)) := by
  induction terms with
  | nil => rfl
  | cons first rest ih =>
    simp only [allPairs, List.all_append, List.all_map, List.map_cons, distinctValue]
    apply congrArg₂ (fun a b => a && b) _ ih
    rfl

/-- The accepted distinct operator preserves direct all-pairs semantics at
arbitrary arity and over every admitted carrier sort. -/
theorem distinct_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (sort : SortCode String) (a b : Expr) (rest : List Expr)
    (first : Uflia.Term E.signature sort) (terms : List (Uflia.Term E.signature sort))
    (head : recur a = some ⟨sort, first⟩)
    (tail : typedTerms? recur sort (b :: rest) = some terms) :
    ∃ result : PackedTerm E,
      equalities? recur true (a :: b :: rest) = some result ∧
      Evaluates E M scope (.list (.atom "distinct" :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  let relation := disequalityTerm (E := E) sort
  refine ⟨⟨.bool, conjunction (allPairs relation (first :: terms))⟩, ?_, ?_⟩
  · simp [equalities?, head, tail, relation]
    rfl
  · change Evaluates E M scope _ .bool _
    rw [conjunction_value]
    change Evaluates E M scope _ .bool
      ((allPairs (disequalityTerm sort) (first :: terms)).all _)
    rw [distinctPairs_value]
    exact Evaluates.distinct a b rest _
      (.cons (sound a ⟨sort, first⟩ head)
        (typedTerms_preserves M scope recur sound sort (b :: rest) terms tail))

/-- Actual dispatch for equality chains and distinct, at every admitted arity.
The Boolean parameter selects source spelling, not the semantic outcome. -/
theorem decode_equalities_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (different : Bool) (sort : SortCode String) (a b : Expr) (rest : List Expr)
    (first : Uflia.Term E.signature sort) (terms : List (Uflia.Term E.signature sort))
    (head : decodeScopedFuel? E fuel locals a = some ⟨sort, first⟩)
    (tail : typedTerms? (decodeScopedFuel? E fuel locals) sort (b :: rest) = some terms) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals
        (.list (.atom (if different then "distinct" else "=") :: a :: b :: rest)) = some result ∧
      Evaluates E M scope
        (.list (.atom (if different then "distinct" else "=") :: a :: b :: rest)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  cases different with
  | false => exact equalities_preserves M scope _ sound sort a b rest first terms head tail
  | true => exact distinct_preserves M scope _ sound sort a b rest first terms head tail

/-- Recognized integer coefficients denote their actual standard integer value.
The other sorts cannot contain a recognized coefficient. -/
theorem integerValue_sound {E : Environment} (M : Model E.signature)
    {sort : SortCode String} (term : Uflia.Term E.signature sort)
    (n : Int) (found : integerValue? term = some n) :
    match sort with
    | .int => M.eval term = n
    | _ => False := by
  induction term generalizing n with
  | var i => exact Fin.elim0 i
  | app op args ih =>
    cases op <;> try (simp only [integerValue?, reduceCtorEq] at found)
    case integer k => cases found; rfl
    case scale k found =>
      cases recognized : integerValue? (args 0) with
      | none => simp only [recognized, Option.map_none, reduceCtorEq] at found
      | some m =>
        simp only [recognized, Option.map_some, Option.some.injEq] at found
        subst n
        change k * M.eval (args 0) = k * m
        rw [ih 0 m recognized]

noncomputable def factorValue {E : Environment} (M : Model E.signature) :
    Option (Uflia.Term E.signature .int) → Int
  | none => 1
  | some term => M.eval term

/-- Multiplication's accumulator invariant. The current coefficient and optional
nonliteral factor, multiplied by all remaining source values, equal the result.
This proves value preservation without importing the normalization as semantics. -/
theorem multiplyFactors_value {E : Environment} (M : Model E.signature)
    (terms : List (Uflia.Term E.signature .int)) (coefficient : Int)
    (factor : Option (Uflia.Term E.signature .int)) (result : Uflia.Term E.signature .int)
    (decoded : multiplyFactors? terms coefficient factor = some result) :
    M.eval result = coefficient * factorValue M factor * (terms.map M.eval).prod := by
  induction terms generalizing coefficient factor result with
  | nil =>
    cases factor with
    | none =>
      simp only [multiplyFactors?, Option.some.injEq] at decoded
      subst result
      simp [factorValue, Model.eval, Model.algebra, ManySorted.Model.eval, Model.apply,
        Uflia.Term.integer]
    | some term =>
      simp only [multiplyFactors?, Option.some.injEq] at decoded
      subst result
      simpa [factorValue] using eval_scaleLinear_int M coefficient term
  | cons term rest ih =>
    cases recognized : integerValue? term with
    | some n =>
      have next : multiplyFactors? rest (coefficient * n) factor = some result := by
        simpa only [multiplyFactors?, recognized] using decoded
      have resultValue := ih (coefficient * n) factor result next
      have termValue : M.eval term = n := integerValue_sound M term n recognized
      simp only [List.map_cons, List.prod_cons, termValue]
      rw [resultValue]
      rw [Int.mul_assoc coefficient n (factorValue M factor),
        Int.mul_comm n (factorValue M factor),
        ← Int.mul_assoc coefficient (factorValue M factor) n, Int.mul_assoc]
    | none =>
      cases factor with
      | some prior => simp [multiplyFactors?, recognized] at decoded
      | none =>
        have next : multiplyFactors? rest coefficient (some term) = some result := by
          simpa only [multiplyFactors?, recognized] using decoded
        have resultValue := ih coefficient (some term) result next
        simpa only [List.map_cons, List.prod_cons, factorValue, Int.mul_one,
          Int.mul_assoc] using resultValue

/-- The surface product is the product of independently interpreted operands;
coefficient normalization in the accepted decoder preserves this direct value. -/
theorem multiply_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (a b : Expr) (rest : List Expr) (terms : List (Uflia.Term E.signature .int))
    (result : Uflia.Term E.signature .int)
    (operands : typedTerms? recur .int (a :: b :: rest) = some terms)
    (product : multiplyFactors? terms 1 none = some result) :
    multiply? recur (a :: b :: rest) = some ⟨.int, result⟩ ∧
      Evaluates E M scope (.list (.atom "*" :: a :: b :: rest)) .int
        ((M.reduct (Packaged.nameMap E)).eval result) := by
  constructor
  · simp [multiply?, operands, product]
  · have value := multiplyFactors_value (M.reduct (Packaged.nameMap E)) terms 1 none result product
    simp only [factorValue, Int.mul_one, Int.one_mul] at value
    rw [value]
    exact Evaluates.multiply a b rest _
      (typedTerms_preserves M scope recur sound .int (a :: b :: rest) terms operands)

/-- Actual multiplication dispatch preserves the direct source product whenever
its typed traversal and one-nonliteral-factor normalization accept. -/
theorem decode_multiply_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (a b : Expr) (rest : List Expr) (terms : List (Uflia.Term E.signature .int))
    (result : Uflia.Term E.signature .int)
    (operands : typedTerms? (decodeScopedFuel? E fuel locals) .int (a :: b :: rest) = some terms)
    (product : multiplyFactors? terms 1 none = some result) :
    decodeScopedFuel? E (fuel + 1) locals (.list (.atom "*" :: a :: b :: rest)) =
        some ⟨.int, result⟩ ∧
      Evaluates E M scope (.list (.atom "*" :: a :: b :: rest)) .int
        ((M.reduct (Packaged.nameMap E)).eval result) :=
  multiply_preserves M scope _ sound a b rest terms result operands product

/-- Successful heterogeneous UF argument decoding preserves every argument in
source order at its declared sort, for arbitrary arity. -/
theorem decodeArguments_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (inputs : List (SortCode String)) (es : List Expr)
    (terms : (i : Fin inputs.length) → Uflia.Term E.signature (inputs.get i))
    (decoded : decodeArguments? recur inputs es = some terms) :
    ArgumentsEvaluate E M scope inputs es
      (fun i => (M.reduct (Packaged.nameMap E)).eval (terms i)) := by
  induction inputs generalizing es with
  | nil =>
    cases es with
    | cons e es => simp [decodeArguments?] at decoded
    | nil =>
      have empty : (fun i => (M.reduct (Packaged.nameMap E)).eval (terms i)) =
          (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
      rw [empty]
      exact ArgumentsEvaluate.nil scope
  | cons input inputs ih =>
    cases es with
    | nil => simp [decodeArguments?] at decoded
    | cons e es =>
      cases head : recur e with
      | none => simp [decodeArguments?, head] at decoded
      | some packed =>
        cases checked : packed.expect? input with
        | none => simp [decodeArguments?, head, checked] at decoded
        | some term =>
          cases tail : decodeArguments? recur inputs es with
          | none => simp [decodeArguments?, head, tail] at decoded
          | some args =>
            have step : decodeArguments? recur (input :: inputs) (e :: es) =
                some (Fin.cases term args) := by simp [decodeArguments?, head, checked, tail]
            rw [step] at decoded
            cases decoded
            have values : (fun i : Fin (input :: inputs).length =>
                (M.reduct (Packaged.nameMap E)).eval
                  (Fin.cases (motive := fun i =>
                    Uflia.Term E.signature ((input :: inputs).get i)) term args i)) =
                Fin.cases (motive := fun i => M.carriers.value ((input :: inputs).get i))
                  ((M.reduct (Packaged.nameMap E)).eval term)
                  (fun i => (M.reduct (Packaged.nameMap E)).eval (args i)) := by
              funext i
              refine Fin.cases ?_ (fun j => ?_) i <;> rfl
            rw [values]
            exact ArgumentsEvaluate.cons _ _
              (typed_child_preserves M scope recur sound input e term
                (by simp [head, checked])) (ih es args tail)

/-- Arbitrary-arity UF application preserves direct global name interpretation.
The explicit unbound/unreserved premises are the source dispatch conditions. -/
theorem applyUF_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (name : String) (i : Fin E.declarations.length) (es : List Expr)
    (unreserved : reserved.contains name = false) (unbound : lookupValue? scope name = none)
    (found : lookup? E name = some i) (nonempty : es ≠ [])
    (terms : (j : Fin (E.declarations.get i).inputs.length) →
      Uflia.Term E.signature ((E.declarations.get i).inputs.get j))
    (decoded : decodeArguments? recur (E.declarations.get i).inputs es = some terms) :
    ∃ result : PackedTerm E, applyUF? E recur name es = some result ∧
      Evaluates E M scope (.list (.atom name :: es)) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩, ?_, ?_⟩
  · simp [applyUF?, found]
    erw [decoded]
    rfl
  · exact Evaluates.app name i unreserved unbound found es nonempty
      (fun j => (M.reduct (Packaged.nameMap E)).eval (terms j))
      (decodeArguments_preserves M scope recur sound (E.declarations.get i).inputs es terms decoded)

/-- Actual implication dispatch has the standard Boolean truth function. -/
theorem decode_implies_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (a b : Expr) (x y : Formula E.signature)
    (left : decodeScopedFuel? E fuel locals a = some ⟨.bool, x⟩)
    (right : decodeScopedFuel? E fuel locals b = some ⟨.bool, y⟩) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list [.atom "=>", a, b]) = some result ∧
      Evaluates E M scope (.list [.atom "=>", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨.bool, .app .or (Fin.cases (.app .not (fun _ => x)) (fun _ => y))⟩, ?_, ?_⟩
  · change implication? (decodeScopedFuel? E fuel locals) a b = _
    simp [implication?, left, right, PackedTerm.expect?]
  · exact Evaluates.binary .implies (sound a ⟨.bool, x⟩ left) (sound b ⟨.bool, y⟩ right)

/-- Xor's disequality lowering agrees with its direct Boolean truth function. -/
theorem decode_xor_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (a b : Expr) (x y : Formula E.signature)
    (left : decodeScopedFuel? E fuel locals a = some ⟨.bool, x⟩)
    (right : decodeScopedFuel? E fuel locals b = some ⟨.bool, y⟩) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list [.atom "xor", a, b]) = some result ∧
      Evaluates E M scope (.list [.atom "xor", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  let term : Formula E.signature := .app .not
    (fun _ => .app (.eq .bool) (Fin.cases x (fun _ => y)))
  refine ⟨⟨.bool, term⟩, ?_, ?_⟩
  · change xor? (decodeScopedFuel? E fuel locals) a b = _
    simp [xor?, left, right, PackedTerm.expect?, term]
  · have value : (M.reduct (Packaged.nameMap E)).eval term =
        Binary.xor.value M ((M.reduct (Packaged.nameMap E)).eval x)
          ((M.reduct (Packaged.nameMap E)).eval y) := by
      dsimp only [term, Model.eval, Model.algebra, ManySorted.Model.eval,
        Model.apply, Binary.value]
      simp only [Bool.not_inj_iff, Bool.beq_eq_decide_eq, decide_eq_decide]
      rfl
    change Evaluates E M scope _ .bool _
    rw [value]
    exact Evaluates.binary .xor (sound a ⟨.bool, x⟩ left) (sound b ⟨.bool, y⟩ right)

/-- Actual polymorphic conditional dispatch preserves the direct branch value. -/
theorem decode_ite_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (fuel : Nat) (locals : Locals E)
    (sound : Sound E M scope (decodeScopedFuel? E fuel locals))
    (sort : SortCode String) (c a b : Expr)
    (test : Formula E.signature) (x y : Uflia.Term E.signature sort)
    (condition : decodeScopedFuel? E fuel locals c = some ⟨.bool, test⟩)
    (left : decodeScopedFuel? E fuel locals a = some ⟨sort, x⟩)
    (right : decodeScopedFuel? E fuel locals b = some ⟨sort, y⟩) :
    ∃ result : PackedTerm E,
      decodeScopedFuel? E (fuel + 1) locals (.list [.atom "ite", c, a, b]) = some result ∧
      Evaluates E M scope (.list [.atom "ite", c, a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) :=
  ite_preserves M scope _ sound sort c a b test x y condition left right

/-- A successful empty argument list has a genuinely nullary declaration. -/
theorem decodeArguments_nil_inputs {E : Environment}
    (recur : Expr → Option (PackedTerm E)) (inputs : List (SortCode String))
    (terms : (i : Fin inputs.length) → Uflia.Term E.signature (inputs.get i))
    (decoded : decodeArguments? recur inputs [] = some terms) : inputs = [] := by
  cases inputs with
  | nil => rfl
  | cons input rest => simp [decodeArguments?] at decoded

/-- Nullary UF atoms obey the same lexical dispatch and global profile as
nonempty applications; an empty source argument list forces a nullary profile. -/
theorem constant_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E))
    (name : String) (i : Fin E.declarations.length)
    (unreserved : reserved.contains name = false) (unbound : lookupValue? scope name = none)
    (notNumeral : naturalNumeral? name = none) (found : lookup? E name = some i)
    (terms : (j : Fin (E.declarations.get i).inputs.length) →
      Uflia.Term E.signature ((E.declarations.get i).inputs.get j))
    (decoded : decodeArguments? recur (E.declarations.get i).inputs [] = some terms) :
    ∃ result : PackedTerm E, applyUF? E recur name [] = some result ∧
      Evaluates E M scope (.atom name) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩, ?_, ?_⟩
  · simp [applyUF?, found]
    erw [decoded]
    rfl
  · exact Evaluates.constant name i unreserved unbound notNumeral found
      (decodeArguments_nil_inputs recur _ terms decoded)
      (fun j => (M.reduct (Packaged.nameMap E)).eval (terms j))

/-- Interpreting a decoded local environment preserves first-match lookup. -/
theorem lookup_interpretLocals {E : Environment} (M : Packaged.GlobalModel)
    (locals : Locals E) (name : String) :
    lookupValue? (interpretLocals M locals) name =
      (local? locals name).map (interpretTerm M) := by
  induction locals with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, term⟩
    simp only [interpretLocals, List.map_cons, lookupValue?, local?]
    split
    · rfl
    · exact ih

/-- Literal atom dispatch preserves the standard integer interpretation after
checking the local scope first. -/
theorem decode_numeral_preserves {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals : Locals E) (text : String) (n : Nat)
    (notTrue : text ≠ "true") (notFalse : text ≠ "false")
    (unbound : local? locals text = none) (parsed : naturalNumeral? text = some n) :
    decodeScopedFuel? E (fuel + 1) locals (.atom text) = some ⟨.int, Uflia.Term.integer n⟩ ∧
      Evaluates E M (interpretLocals M locals) (.atom text) .int (n : Int) := by
  constructor
  · simp [decodeScopedFuel?, unbound, numeral?, parsed]
  · apply Evaluates.numeral text n parsed
    rw [lookup_interpretLocals, unbound]
    rfl

@[simp] theorem interpretLocals_append {E : Environment} (M : Packaged.GlobalModel)
    (a b : Locals E) : interpretLocals M (a ++ b) = interpretLocals M a ++ interpretLocals M b :=
  List.map_append

/-- Scalar lookup preserves direct local semantics, including shadowing. -/
theorem local_preserves {E : Environment} (M : Packaged.GlobalModel)
    (locals : Locals E) (name : String) (t : PackedTerm E)
    (notTrue : name ≠ "true") (notFalse : name ≠ "false")
    (found : local? locals name = some t) :
    Evaluates E M (interpretLocals M locals) (.atom name) t.sort
      ((M.reduct (Packaged.nameMap E)).eval t.term) := by
  apply Evaluates.local name (interpretTerm M t) notTrue notFalse
  rw [lookup_interpretLocals, found]
  rfl

/-- The actual atom-dispatch branch uses the first local value and never falls
back to global UF lookup when that value is present. -/
theorem decode_local_preserves {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals : Locals E) (name : String) (t : PackedTerm E)
    (notTrue : name ≠ "true") (notFalse : name ≠ "false")
    (found : local? locals name = some t) :
    decodeScopedFuel? E (fuel + 1) locals (.atom name) = some t ∧
      Evaluates E M (interpretLocals M locals) (.atom name) t.sort
        ((M.reduct (Packaged.nameMap E)).eval t.term) := by
  constructor
  · simp [decodeScopedFuel?, found]
  · exact local_preserves M locals name t notTrue notFalse found

/-- Binding interpretation preserves names, so duplicate-name checks agree. -/
theorem interpretLocals_any_name {E : Environment} (M : Packaged.GlobalModel)
    (locals : Locals E) (name : String) :
    (interpretLocals M locals).any (fun pair => pair.1 == name) =
      locals.any (fun pair => pair.1 == name) := by
  simp [interpretLocals, List.any_map, Function.comp_def]

/-- One parallel binding step uses the same semantic outer scope for its RHS
and all remaining RHSs. It preserves the actual executable binding decoder. -/
theorem letBindings_cons_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E))
    (sound : Sound E M scope recur)
    (name : String) (e : Expr) (rest : List Expr) (term : PackedTerm E) (terms : Locals E)
    (legal : simpleSymbol name = true) (unreserved : reserved.contains name = false)
    (fresh : terms.any (fun pair => pair.1 == name) = false)
    (rhs : recur e = some term) (tail : letBindings? recur rest = some terms)
    (tailValue : BindingsEvaluate E M scope rest (interpretLocals M terms)) :
    letBindings? recur (.list [.atom name, e] :: rest) = some ((name, term) :: terms) ∧
      BindingsEvaluate E M scope (.list [.atom name, e] :: rest)
        (interpretLocals M ((name, term) :: terms)) := by
  constructor
  · have notReserved : name ∉ reserved := by simpa using unreserved
    have freshNames : ∀ (a : String) (b : PackedTerm E), (a, b) ∈ terms → a ≠ name := by
      simpa using fresh
    have notDuplicate : ∀ x : PackedTerm E, (name, x) ∉ terms := by
      intro x member
      exact freshNames name x member rfl
    simp [letBindings?, legal, notReserved, rhs, tail, notDuplicate]
  · exact BindingsEvaluate.cons name (interpretTerm M term) legal unreserved
      (by change (interpretLocals M terms).any _ = false
          rw [interpretLocals_any_name]; exact fresh) (sound e term rhs) tailValue

/-- Every successful binding list preserves direct parallel semantics. There is
no restriction on list length or on the accepted recursive RHS expressions. -/
theorem letBindings_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E))
    (sound : Sound E M scope recur) (bindings : List Expr) (values : Locals E)
    (decoded : letBindings? recur bindings = some values) :
    BindingsEvaluate E M scope bindings (interpretLocals M values) := by
  induction bindings generalizing values with
  | nil =>
    simp only [letBindings?, Option.some.injEq] at decoded
    subst values
    exact BindingsEvaluate.nil scope
  | cons binding rest ih =>
    cases binding with
    | atom text => simp [letBindings?] at decoded
    | list parts =>
      cases parts with
      | nil => simp [letBindings?] at decoded
      | cons head tailParts =>
        cases head with
        | list xs => simp [letBindings?] at decoded
        | atom name =>
          cases tailParts with
          | nil => simp [letBindings?] at decoded
          | cons e more =>
            cases more with
            | cons extra extras => simp [letBindings?] at decoded
            | nil =>
              cases legal : simpleSymbol name with
              | false => simp [letBindings?, legal] at decoded
              | true =>
                cases unreserved : reserved.contains name with
                | true =>
                  have member : name ∈ reserved := by simpa using unreserved
                  simp [letBindings?, member] at decoded
                | false =>
                  cases rhs : recur e with
                  | none => simp [letBindings?, rhs] at decoded
                  | some term =>
                    cases tail : letBindings? recur rest with
                    | none => simp [letBindings?, rhs, tail] at decoded
                    | some terms =>
                      cases fresh : terms.any (fun pair => pair.1 == name) with
                      | true =>
                        have duplicate : ∃ pair ∈ terms, pair.1 = name := by simpa using fresh
                        rcases duplicate with ⟨⟨key, value⟩, member, equal⟩
                        change key = name at equal
                        subst key
                        have duplicate : ∃ x : PackedTerm E, (name, x) ∈ terms := ⟨value, member⟩
                        simp [letBindings?, rhs, tail, duplicate] at decoded
                      | false =>
                        have step := letBindings_cons_preserves M scope recur sound
                          name e rest term terms legal unreserved fresh rhs tail (ih terms tail)
                        rw [step.1] at decoded
                        cases decoded
                        exact step.2

/-- The actual recursive let branch extends the body scope simultaneously.
The body induction hypothesis is at the extended scope, while every RHS is
justified at the unchanged outer scope. -/
theorem decode_let_preserves {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals values : Locals E) (bindings : List Expr) (body : Expr)
    (nonempty : bindings ≠ [])
    (decodedBindings : letBindings? (decodeScopedFuel? E fuel locals) bindings = some values)
    (rhsSound : Sound E M (interpretLocals M locals)
      (decodeScopedFuel? E fuel locals))
    (bodySound : Sound E M (interpretLocals M (values ++ locals))
      (decodeScopedFuel? E fuel (values ++ locals)))
    (t : PackedTerm E)
    (decodedBody : decodeScopedFuel? E fuel (values ++ locals) body = some t) :
    decodeScopedFuel? E (fuel + 1) locals (.list [.atom "let", .list bindings, body]) = some t ∧
      Evaluates E M (interpretLocals M locals)
        (.list [.atom "let", .list bindings, body]) t.sort
        ((M.reduct (Packaged.nameMap E)).eval t.term) := by
  constructor
  · cases bindings with
    | nil => exact (nonempty rfl).elim
    | cons first rest =>
      change (do let values ← letBindings? (decodeScopedFuel? E fuel locals) (first :: rest)
                 decodeScopedFuel? E fuel (values ++ locals) body) = some t
      rw [decodedBindings]
      exact decodedBody
  · apply Evaluates.letExpr nonempty
      (letBindings_preserves M (interpretLocals M locals)
        (decodeScopedFuel? E fuel locals) rhsSound bindings values decodedBindings)
    simpa using bodySound body t decodedBody

/-- A successful sort check identifies the entire dependent packed term. -/
theorem expect_result {E : Environment} (sort : SortCode String)
    (packed : PackedTerm E) (term : Uflia.Term E.signature sort)
    (checked : packed.expect? sort = some term) : packed = ⟨sort, term⟩ := by
  rcases packed with ⟨actual, value⟩
  by_cases same : actual = sort
  · subst actual
    simp [PackedTerm.expect?] at checked
    subst term
    rfl
  · simp [PackedTerm.expect?, same] at checked

/-- Determinism of an Option result transports a compositional preservation
witness to the actual returned dependent packed value. -/
theorem preserved_result {E : Environment} (M : Packaged.GlobalModel) (scope : Scope M)
    (expression : Expr) (output : Option (PackedTerm E)) (result : PackedTerm E)
    (decoded : output = some result)
    (preserved : ∃ term, output = some term ∧ Evaluates E M scope expression term.sort
      ((M.reduct (Packaged.nameMap E)).eval term.term)) :
    Evaluates E M scope expression result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  rcases preserved with ⟨term, returned, meaning⟩
  have same : term = result := Option.some.inj (returned.symm.trans decoded)
  cases same
  exact meaning

/-- Preservation for every successful unary helper result, without requiring
callers to expose intermediate decoder values. -/
theorem unary_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    {input output : SortCode String} (op : Unary input output) (e : Expr)
    (result : PackedTerm E) (decoded : unary? recur op.operation e = some result) :
    Evaluates E M scope (.list [.atom op.token, e]) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have parsed := decoded
  unfold unary? at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨packed, child, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with ⟨term, checked, _finish⟩
  have shape := expect_result input packed term checked
  cases shape
  exact preserved_result M scope _ _ result decoded
    (unary_preserves M scope recur sound op e term child)

/-- Arbitrary successful fold results preserve all source operands. -/
theorem fold_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    {sort : SortCode String} (op : FoldOp sort) (es : List Expr)
    (result : PackedTerm E) (decoded : fold? recur op.operation es = some result) :
    Evaluates E M scope (.list (.atom op.token :: es)) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  cases es with
  | nil => simp [fold?] at decoded
  | cons a es =>
    cases es with
    | nil => simp [fold?] at decoded
    | cons b rest =>
      have parsed := decoded
      unfold fold? at parsed
      rcases Option.bind_eq_some_iff.mp parsed with ⟨packed, child, following⟩
      rcases Option.bind_eq_some_iff.mp following with ⟨term, checked, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with ⟨terms, tail, _finish⟩
      have shape := expect_result sort packed term checked
      cases shape
      exact preserved_result M scope _ _ result decoded
        (fold_preserves M scope recur sound op a b rest term terms child tail)

/-- Every accepted comparison chain result has its independently defined value. -/
theorem compare_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (op : CompareOp) (es : List Expr) (result : PackedTerm E)
    (decoded : compare? recur op.operation op.reverse es = some result) :
    Evaluates E M scope (.list (.atom op.token :: es)) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  cases es with
  | nil => simp [compare?] at decoded
  | cons a es =>
    cases es with
    | nil => simp [compare?] at decoded
    | cons b rest =>
      have parsed := decoded
      unfold compare? at parsed
      rcases Option.bind_eq_some_iff.mp parsed with ⟨terms, operands, _finish⟩
      exact preserved_result M scope _ _ result decoded
        (compare_preserves M scope recur sound op a b rest terms operands)

/-- Every successful multiplication result preserves the original source product. -/
theorem multiply_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (es : List Expr) (result : PackedTerm E)
    (decoded : multiply? recur es = some result) :
    Evaluates E M scope (.list (.atom "*" :: es)) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  cases es with
  | nil => simp [multiply?] at decoded
  | cons a es =>
    cases es with
    | nil => simp [multiply?] at decoded
    | cons b rest =>
      have parsed := decoded
      unfold multiply? at parsed
      rcases Option.bind_eq_some_iff.mp parsed with ⟨terms, operands, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with ⟨term, product, _finish⟩
      have preserved := multiply_preserves M scope recur sound a b rest terms term operands product
      exact preserved_result M scope _ _ result decoded ⟨⟨.int, term⟩, preserved.1, preserved.2⟩

/-- All successful equality/distinct results preserve direct chained/pairwise meaning. -/
theorem equalities_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (different : Bool) (es : List Expr) (result : PackedTerm E)
    (decoded : equalities? recur different es = some result) :
    Evaluates E M scope
      (.list (.atom (if different then "distinct" else "=") :: es)) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  cases es with
  | nil => simp [equalities?] at decoded
  | cons a es =>
    cases es with
    | nil => simp [equalities?] at decoded
    | cons b rest =>
      have parsed := decoded
      unfold equalities? at parsed
      rcases Option.bind_eq_some_iff.mp parsed with ⟨packed, child, following⟩
      rcases packed with ⟨sort, first⟩
      rcases Option.bind_eq_some_iff.mp following with ⟨terms, tail, _finish⟩
      cases different with
      | false =>
        exact preserved_result M scope _ _ result decoded
          (equalities_preserves M scope recur sound sort a b rest first terms child tail)
      | true =>
        exact preserved_result M scope _ _ result decoded
          (distinct_preserves M scope recur sound sort a b rest first terms child tail)

/-- Every successful polymorphic conditional preserves its direct value. -/
theorem ite_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (c a b : Expr) (result : PackedTerm E) (decoded : ite? recur c a b = some result) :
    Evaluates E M scope (.list [.atom "ite", c, a, b]) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have parsed := decoded
  unfold ite? at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨pc, condition, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨test, conditionSort, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨pa, left, remaining⟩
  rcases pa with ⟨sort, x⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨pb, right, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨y, rightSort, _finish⟩
  have conditionShape := expect_result .bool pc test conditionSort
  have rightShape := expect_result sort pb y rightSort
  cases conditionShape
  cases rightShape
  exact preserved_result M scope _ _ result decoded
    (ite_preserves M scope recur sound sort c a b test x y condition left right)

/-- A successful global lookup cannot use a reserved operator name. -/
theorem lookup_unreserved (E : Environment) (name : String) (i : Fin E.declarations.length)
    (found : lookup? E name = some i) : reserved.contains name = false := by
  cases reservedName : reserved.contains name with
  | false => rfl
  | true =>
    have member : name ∈ reserved := by simpa using reservedName
    simp [lookup?, member] at found

/-- Every successful nonempty global application preserves the global model. -/
theorem applyUF_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (name : String) (es : List Expr) (nonempty : es ≠ [])
    (unbound : lookupValue? scope name = none) (result : PackedTerm E)
    (decoded : applyUF? E recur name es = some result) :
    Evaluates E M scope (.list (.atom name :: es)) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have parsed := decoded
  unfold applyUF? at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨i, found, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨terms, arguments, _finish⟩
  exact preserved_result M scope _ _ result decoded
    (applyUF_preserves M scope recur sound name i es (lookup_unreserved E name i found)
      unbound found nonempty terms arguments)

/-- Successful nullary global atoms obey lexical dispatch and preserve meaning. -/
theorem constant_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E))
    (name : String) (unbound : lookupValue? scope name = none)
    (notNumeral : naturalNumeral? name = none) (result : PackedTerm E)
    (decoded : applyUF? E recur name [] = some result) :
    Evaluates E M scope (.atom name) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have parsed := decoded
  unfold applyUF? at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨i, found, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨terms, arguments, _finish⟩
  exact preserved_result M scope _ _ result decoded
    (constant_preserves M scope recur name i (lookup_unreserved E name i found)
      unbound notNumeral found terms arguments)

/-- The Boolean helper preserves the independent source truth function. -/
theorem implication_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E))
    (sound : Sound E M scope recur)
    (a b : Expr) (x y : Formula E.signature)
    (left : recur a = some ⟨.bool, x⟩)
    (right : recur b = some ⟨.bool, y⟩) :
    ∃ result : PackedTerm E,
      implication? recur a b = some result ∧
      Evaluates E M scope (.list [.atom "=>", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  refine ⟨⟨.bool, .app .or (Fin.cases (.app .not (fun _ => x)) (fun _ => y))⟩, ?_, ?_⟩
  · simp [implication?, left, right, PackedTerm.expect?]
  · exact Evaluates.binary .implies (sound a ⟨.bool, x⟩ left) (sound b ⟨.bool, y⟩ right)

/-- The Boolean helper preserves the independent source truth function. -/
theorem xor_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E))
    (sound : Sound E M scope recur)
    (a b : Expr) (x y : Formula E.signature)
    (left : recur a = some ⟨.bool, x⟩)
    (right : recur b = some ⟨.bool, y⟩) :
    ∃ result : PackedTerm E,
      xor? recur a b = some result ∧
      Evaluates E M scope (.list [.atom "xor", a, b]) result.sort
        ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  let term : Formula E.signature := .app .not
    (fun _ => .app (.eq .bool) (Fin.cases x (fun _ => y)))
  refine ⟨⟨.bool, term⟩, ?_, ?_⟩
  · simp [xor?, left, right, PackedTerm.expect?, term]
  · have value : (M.reduct (Packaged.nameMap E)).eval term =
        Binary.xor.value M ((M.reduct (Packaged.nameMap E)).eval x)
          ((M.reduct (Packaged.nameMap E)).eval y) := by
      dsimp only [term, Model.eval, Model.algebra, ManySorted.Model.eval,
        Model.apply, Binary.value]
      simp only [Bool.not_inj_iff, Bool.beq_eq_decide_eq, decide_eq_decide]
      rfl
    change Evaluates E M scope _ .bool _
    rw [value]
    exact Evaluates.binary .xor (sound a ⟨.bool, x⟩ left) (sound b ⟨.bool, y⟩ right)

/-- Every successful Boolean binary helper result preserves its meaning. -/
theorem implication_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (a b : Expr) (result : PackedTerm E) (decoded : implication? recur a b = some result) :
    Evaluates E M scope (.list [.atom "=>", a, b]) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have parsed := decoded
  unfold implication? at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨pa, left, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨x, leftSort, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨pb, right, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨y, rightSort, _finish⟩
  have leftShape := expect_result .bool pa x leftSort
  have rightShape := expect_result .bool pb y rightSort
  cases leftShape
  cases rightShape
  exact preserved_result M scope _ _ result decoded
    (implication_preserves M scope recur sound a b x y left right)

/-- Every successful Boolean binary helper result preserves its meaning. -/
theorem xor_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (scope : Scope M) (recur : Expr → Option (PackedTerm E)) (sound : Sound E M scope recur)
    (a b : Expr) (result : PackedTerm E) (decoded : xor? recur a b = some result) :
    Evaluates E M scope (.list [.atom "xor", a, b]) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  have parsed := decoded
  unfold xor? at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨pa, left, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨x, leftSort, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨pb, right, remaining⟩
  rcases Option.bind_eq_some_iff.mp remaining with ⟨y, rightSort, _finish⟩
  have leftShape := expect_result .bool pa x leftSort
  have rightShape := expect_result .bool pb y rightSort
  cases leftShape
  cases rightShape
  exact preserved_result M scope _ _ result decoded
    (xor_preserves M scope recur sound a b x y left right)


/-- Successful atom dispatch preserves literals, first-match locals, and nullary globals. -/
theorem atom_result_preserves {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals : Locals E) (name : String) (result : PackedTerm E)
    (decoded : decodeScopedFuel? E (fuel + 1) locals (.atom name) = some result) :
    Evaluates E M (interpretLocals M locals) (.atom name) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  by_cases notTrue : name = "true"
  · subst name
    simp only [decodeScopedFuel?, Option.some.injEq] at decoded
    subst result
    exact Evaluates.boolean true
  by_cases notFalse : name = "false"
  · subst name
    simp only [decodeScopedFuel?, Option.some.injEq] at decoded
    subst result
    exact Evaluates.boolean false
  cases found : local? locals name with
  | some term =>
    have same : term = result := by
      simpa [decodeScopedFuel?, notTrue, notFalse, found] using decoded
    subst result
    exact local_preserves M locals name term notTrue notFalse found
  | none =>
    have unbound : lookupValue? (interpretLocals M locals) name = none := by
      rw [lookup_interpretLocals, found]
      rfl
    cases parsed : naturalNumeral? name with
    | some n =>
      have same : (⟨.int, Uflia.Term.integer (n : Int)⟩ : PackedTerm E) = result := by
        simpa [decodeScopedFuel?, notTrue, notFalse, found, numeral?, parsed] using decoded
      subst result
      exact Evaluates.numeral name n parsed unbound
    | none =>
      apply constant_result_preserves M (interpretLocals M locals)
        (decodeScopedFuel? E fuel locals) name unbound parsed result
      simpa [decodeScopedFuel?, notTrue, notFalse, found, numeral?, parsed] using decoded


/-- The guarded nonempty application dispatcher preserves its lexical scope. -/
theorem application_dispatch_preserves {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals : Locals E)
    (sound : Sound E M (interpretLocals M locals) (decodeScopedFuel? E fuel locals))
    (name : String) (args : List Expr) (result : PackedTerm E)
    (decoded : (if args.isEmpty || reserved.contains name || (local? locals name).isSome
      then none else applyUF? E (decodeScopedFuel? E fuel locals) name args) = some result) :
    Evaluates E M (interpretLocals M locals) (.list (.atom name :: args)) result.sort
      ((M.reduct (Packaged.nameMap E)).eval result.term) := by
  cases args with
  | nil => simp at decoded
  | cons a args =>
    cases found : local? locals name with
    | some term => simp [found] at decoded
    | none =>
      have unbound : lookupValue? (interpretLocals M locals) name = none := by
        rw [lookup_interpretLocals, found]
        rfl
      simp only [List.isEmpty_cons, Bool.false_or, found, Option.isSome_none,
        Bool.or_false] at decoded
      split at decoded
      · contradiction
      · exact applyUF_result_preserves M _ _ sound name (a :: args) (by simp)
          unbound result decoded

/-- Fuel induction preserves every successful scoped frontend result. -/
theorem decodeScopedFuel_preserves {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals : Locals E) :
    Sound E M (interpretLocals M locals) (decodeScopedFuel? E fuel locals) := by
  induction fuel generalizing locals with
  | zero =>
    intro e result decoded
    simp [decodeScopedFuel?] at decoded
  | succ fuel ih =>
    intro e result decoded
    cases e with
    | atom name => exact atom_result_preserves M fuel locals name result decoded
    | list es =>
      unfold decodeScopedFuel? at decoded
      dsimp only at decoded
      split at decoded
      all_goals try (rename_i equation; rw [equation])
      all_goals try first
        | exact unary_result_preserves M _ _ (ih locals) .not _ result decoded
        | exact unary_result_preserves M _ _ (ih locals) .neg _ result decoded
        | exact fold_result_preserves M _ _ (ih locals) .and _ result decoded
        | exact fold_result_preserves M _ _ (ih locals) .or _ result decoded
        | exact fold_result_preserves M _ _ (ih locals) .add _ result decoded
        | exact fold_result_preserves M _ _ (ih locals) .sub _ result decoded
        | exact compare_result_preserves M _ _ (ih locals) .le _ result decoded
        | exact compare_result_preserves M _ _ (ih locals) .lt _ result decoded
        | exact compare_result_preserves M _ _ (ih locals) .ge _ result decoded
        | exact compare_result_preserves M _ _ (ih locals) .gt _ result decoded
        | exact equalities_result_preserves M _ _ (ih locals) false _ result decoded
        | exact equalities_result_preserves M _ _ (ih locals) true _ result decoded
        | exact implication_result_preserves M _ _ (ih locals) _ _ result decoded
        | exact xor_result_preserves M _ _ (ih locals) _ _ result decoded
        | exact ite_result_preserves M _ _ (ih locals) _ _ _ result decoded
        | exact multiply_result_preserves M _ _ (ih locals) _ result decoded
        | exact application_dispatch_preserves M fuel locals (ih locals) _ _ result decoded
        | contradiction
      case h_4 =>
        rename_i e head tail body
        rcases Option.bind_eq_some_iff.mp decoded with ⟨values, bindings, bodyDecoded⟩
        exact (decode_let_preserves M fuel locals values (head :: tail) body (by simp)
          bindings (ih locals) (ih (values ++ locals)) result bodyDecoded).2


/-- The public decoder preserves independent source evaluation in the empty scope. -/
theorem decodeTerm_preserves {E : Environment} (M : Packaged.GlobalModel)
    (e : Expr) (result : PackedTerm E) (decoded : decodeTerm? E e = some result) :
    Evaluates E M [] e result.sort ((M.reduct (Packaged.nameMap E)).eval result.term) :=
  decodeScopedFuel_preserves M (expressionFuel e) [] e result decoded

/-- Successful formula decoding preserves the source Boolean value. -/
theorem decodeFormula_preserves {E : Environment} (M : Packaged.GlobalModel)
    (e : Expr) (formula : Formula E.signature)
    (decoded : decodeFormula? E e = some formula) :
    Evaluates E M [] e .bool ((M.reduct (Packaged.nameMap E)).eval formula) := by
  unfold decodeFormula? at decoded
  rcases Option.bind_eq_some_iff.mp decoded with ⟨packed, term, checked⟩
  have shape := expect_result .bool packed formula checked
  cases shape
  exact decodeTerm_preserves M e ⟨.bool, formula⟩ term

/-- Accepted assertions inherit source preservation without an external certificate. -/
theorem assertion_preserves {E : Environment} (M : Packaged.GlobalModel) (a : Assertion E) :
    Evaluates E M [] a.expression .bool ((M.reduct (Packaged.nameMap E)).eval a.formula) :=
  decodeFormula_preserves M a.expression a.formula a.decoded

/-- Existing assertion satisfaction implies independent source truth in one model. -/
theorem expressionHolds_implies {E : Environment} (M : Packaged.GlobalModel)
    (e : Expr) (holds : ExpressionHolds E e (M.reduct (Packaged.nameMap E))) :
    Holds E M e := by
  rcases holds with ⟨formula, decoded, truth⟩
  have evaluated := decodeFormula_preserves M e formula decoded
  change (M.reduct (Packaged.nameMap E)).eval formula = true at truth
  rw [truth] at evaluated
  exact evaluated

/-- Every satisfied assertion list has direct source truth in the same global model. -/
theorem assertionsHolds_implies {E : Environment} (M : Packaged.GlobalModel)
    (assertions : List (Assertion E))
    (holds : AssertionsHolds assertions (M.reduct (Packaged.nameMap E))) :
    ∀ a ∈ assertions, Holds E M a.expression := by
  intro a member
  exact expressionHolds_implies M a.expression (holds a member)

end Silmaril.Logic.Smt.Uflia.SExpr.Surface
