module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Variables

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment} (f : E.signature ⟶ F.signature)
variable {k : Nat} {Γ : Fin k → SortCode String}

@[simp] theorem expect_map (term : PackedTerm E Γ) (sort : SortCode String) :
    (mapPacked f term).expect? sort = (term.expect? sort).map (Term.map f) := by
  rcases term with ⟨s, term⟩
  by_cases h : s = sort
  · subst s
    simp [PackedTerm.expect?, mapPacked]
  · simp [PackedTerm.expect?, mapPacked, h]

@[simp] theorem expect_map_value (term : PackedTerm E Γ) (sort : SortCode String) :
    PackedTerm.expect? sort ⟨term.sort, term.term.map f⟩ =
      (term.expect? sort).map (Term.map f) := expect_map f term sort

theorem map_finCases {n : Nat} {sorts : Fin (n + 1) → SortCode String}
    (first : Term E.signature Γ (sorts 0))
    (rest : ∀ i, Term E.signature Γ (sorts i.succ)) :
    (fun i => (Fin.cases (motive := fun j => Term E.signature Γ (sorts j)) first rest i).map f) =
      Fin.cases (motive := fun j => Term F.signature Γ (sorts j))
        (first.map f) (fun i => (rest i).map f) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem map_finCases_apply {n : Nat} {sorts : Fin (n + 1) → SortCode String}
    (first : Term E.signature Γ (sorts 0))
    (rest : ∀ i, Term E.signature Γ (sorts i.succ)) (i : Fin (n + 1)) :
    (Fin.cases (motive := fun j => Term E.signature Γ (sorts j)) first rest i).map f =
      Fin.cases (motive := fun j => Term F.signature Γ (sorts j))
        (first.map f) (fun i => (rest i).map f) i := by
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem map_homCases_apply {n : Nat} {sort : SortCode String}
    (first : Term E.signature Γ sort) (rest : Fin n → Term E.signature Γ sort)
    (i : Fin (n + 1)) :
    (Fin.cases (motive := fun _ => Term E.signature Γ sort) first rest i).map f =
      Fin.cases (motive := fun _ => Term F.signature Γ sort)
        (first.map f) (fun i => (rest i).map f) i := by
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem map_iteCases_apply {sort : SortCode String}
    (c : Term E.signature Γ .bool) (a b : Term E.signature Γ sort) (i : Fin 3) :
    (Fin.cases (motive := fun j => Term E.signature Γ
      (Fin.cases (motive := fun _ => SortCode String) .bool (fun _ : Fin 2 => sort) j)) c (Fin.cases a (fun _ => b)) i).map f =
    Fin.cases (motive := fun j => Term F.signature Γ
      (Fin.cases (motive := fun _ => SortCode String) .bool (fun _ : Fin 2 => sort) j)) (c.map f)
      (Fin.cases (a.map f) (fun _ => b.map f)) i := by
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

@[simp] theorem map_integer (value : Int) :
    (Term.integer (A := E.signature) (Γ := Γ) value).map f = Term.integer value := by
  simp only [Term.integer, Term.map, Operation.map]
  congr 1
  funext i
  exact i.elim0

@[simp 1100] theorem map_app2 {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a b : Term E.signature Γ input) :
    (Term.app op (Fin.cases a (fun _ => b))).map f =
      .app (Operation.map f op) (Fin.cases (a.map f) (fun _ => b.map f)) := by
  simp only [Term.map]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp 1100] theorem map_ite {sort : SortCode String}
    (c : Term E.signature Γ .bool) (a b : Term E.signature Γ sort) :
    (Term.app (.ite sort) (Fin.cases c (Fin.cases a (fun _ => b)))).map f =
      .app (.ite sort) (Fin.cases (c.map f) (Fin.cases (a.map f) (fun _ => b.map f))) := by
  simp only [Term.map, Operation.map]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

@[simp] theorem map_pair {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort) (a b : Term E.signature Γ sort) :
    (SExpr.pair op a b).map f = SExpr.pair (Operation.map f op) (a.map f) (b.map f) :=
  map_app2 f op a b

@[simp] theorem map_cases_apply {input : SortCode String} {inputs : List (SortCode String)}
    (first : Term E.signature Γ input)
    (rest : ∀ i, Term E.signature Γ (inputs.get i)) (i : Fin (input :: inputs).length) :
    (Fin.cases (motive := fun j => Term E.signature Γ ((input :: inputs).get j)) first rest i).map f =
      Fin.cases (motive := fun j => Term F.signature Γ ((input :: inputs).get j))
        (first.map f) (fun i => (rest i).map f) i := by
  exact Fin.cases rfl (fun _ => rfl) i

/-- Global operation maps cannot turn a runtime constant into literal syntax. -/
theorem integerValue_map {sort : SortCode String} (term : Term E.signature Γ sort) :
    integerValue? (term.map f) = integerValue? term := by
  induction term with
  | var i => rfl
  | @app k Γ n inputs output op args ih =>
    cases op <;> try rfl
    · cases output <;> rcases n with _ | (_ | n) <;> rfl
    · exact congrArg (Option.map _) (ih 0)
  | all sort body ih => rfl
  | ex sort body ih => rfl

/-- Linear normalization commutes with every profile-preserving global map. -/
theorem scaleLinear_map {sort : SortCode String} (term : Term E.signature Γ sort)
    (coefficient : Int) :
    (scaleLinear coefficient term).map f = scaleLinear coefficient (term.map f) := by
  induction term generalizing coefficient with
  | @var k Γ i =>
    unfold scaleLinear
    simp only [Term.map]
    generalize hs : (Term.var i : Term E.signature Γ (Γ i)) = source
    generalize ht : (Term.var i : Term F.signature Γ (Γ i)) = target
    have mapped : source.map f = target := by rw [← hs, ← ht]; rfl
    clear hs ht
    generalize Γ i = sort at source target mapped ⊢
    cases sort <;> simp_all only [Term.map, Operation.map]
  | @app k Γ n inputs output op args ih =>
    cases op with
    | uf symbol =>
      cases output <;> rcases n with _ | (_ | n) <;>
        simp [scaleLinear, Term.map, Operation.map]
    | integer value => simp only [scaleLinear, map_integer, Term.map, Operation.map]
    | add => simp only [scaleLinear, Term.map, Operation.map, map_pair, ih]
    | sub => simp only [scaleLinear, Term.map, Operation.map, map_pair, ih]
    | scale scalar => simpa only [scaleLinear, Term.map, Operation.map] using ih 0 (coefficient * scalar)
    | boolean value => rfl
    | le => rfl
    | lt => rfl
    | eq s => rfl
    | not => rfl
    | and => rfl
    | or => rfl
    | ite s => cases output <;> rfl
  | all sort body ih => rfl
  | ex sort body ih => rfl

theorem multiplyFactors_map (terms : List (Term E.signature Γ .int))
    (coefficient : Int) (factor : Option (Term E.signature Γ .int)) :
    multiplyFactors? (terms.map (Term.map f)) coefficient (factor.map (Term.map f)) =
      (multiplyFactors? terms coefficient factor).map (Term.map f) := by
  induction terms generalizing coefficient factor with
  | nil =>
    cases factor with
    | none => simp only [List.map_nil, Option.map_none, multiplyFactors?, Option.map_some, map_integer]
    | some term => simp [multiplyFactors?, scaleLinear_map]
  | cons term terms ih =>
    simp only [List.map_cons, multiplyFactors?, integerValue_map]
    cases h : integerValue? term with
    | some value => simpa only [h] using ih (coefficient * value) factor
    | none =>
      cases factor with
      | none => simpa only [h, Option.map_none, Option.map_some] using ih coefficient (some term)
      | some other => simp only [Option.map_some, Option.map_none]

@[simp] theorem multiplyFactors_map_none (terms : List (Term E.signature Γ .int))
    (coefficient : Int) :
    multiplyFactors? (terms.map (Term.map f)) coefficient none =
      (multiplyFactors? terms coefficient none).map (Term.map f) := by
  simpa only [Option.map_none] using multiplyFactors_map f terms coefficient none

theorem foldTerms_map {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (first : Term E.signature Γ sort) (rest : List (Term E.signature Γ sort)) :
    (foldTerms op first rest).map f =
      foldTerms (Operation.map f op) (first.map f) (rest.map (Term.map f)) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simpa only [foldTerms, List.foldl_cons, List.map_cons, map_pair] using ih (pair op first next)

theorem conjunction_map (terms : List (Formula E.signature Γ)) :
    (conjunction terms).map f = conjunction (terms.map (Term.map f)) := by
  cases terms with
  | nil =>
    simp only [conjunction, Term.boolean, Term.map, Operation.map, List.map_nil]
    congr 1
    funext i
    exact i.elim0
  | cons first rest => exact foldTerms_map f .and first rest

/-- Natural action on a recursive decoding oracle, before transforming source
syntax. Source traversal uses these laws at every ordinary operator position. -/
theorem unary_map (recur : Expr → Option (PackedTerm E Γ))
    {input output} (op : Operation E.signature 1 (fun _ => input) output) (a : Expr) :
    unary? (fun e => (recur e).map (mapPacked f)) (Operation.map f op) a =
      (unary? recur op a).map (mapPacked f) := by
  simp [unary?, Option.bind_map, Option.map_bind, mapPacked, Term.map]

theorem binary_map (recur : Expr → Option (PackedTerm E Γ))
    {input output} (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr) :
    binary? (fun e => (recur e).map (mapPacked f)) (Operation.map f op) a b =
      (binary? recur op a b).map (mapPacked f) := by
  simp [binary?, Option.bind_map, Option.map_bind, mapPacked, Term.map]

theorem implication_map (recur : Expr → Option (PackedTerm E Γ)) (a b : Expr) :
    implication? (fun e => (recur e).map (mapPacked f)) a b =
      (implication? recur a b).map (mapPacked f) := by
  simp [implication?, Option.bind_map, Option.map_bind, mapPacked, Term.map,
    Operation.map]

theorem xor_map (recur : Expr → Option (PackedTerm E Γ)) (a b : Expr) :
    xor? (fun e => (recur e).map (mapPacked f)) a b =
      (xor? recur a b).map (mapPacked f) := by
  simp [xor?, Option.bind_map, Option.map_bind, mapPacked, Term.map, Operation.map]

theorem ite_map (recur : Expr → Option (PackedTerm E Γ)) (c a b : Expr) :
    ite? (fun e => (recur e).map (mapPacked f)) c a b =
      (ite? recur c a b).map (mapPacked f) := by
  simp [ite?, Option.bind_map, Option.map_bind, mapPacked, Term.map, Operation.map]

theorem typedTerms_map (recur : Expr → Option (PackedTerm E Γ))
    (sort : SortCode String) (expressions : List Expr) :
    typedTerms? (fun e => (recur e).map (mapPacked f)) sort expressions =
      (typedTerms? recur sort expressions).map (List.map (Term.map f)) := by
  have natural : (fun e => do let t ← (recur e).map (mapPacked f); t.expect? sort) =
      (fun e => ((recur e).bind (PackedTerm.expect? sort)).map (Term.map f)) := by
    funext e
    simp [Option.bind_map, Option.map_bind]
  unfold typedTerms?
  rw [natural, Surface.mapM_natural]
  rfl

theorem fold_map (recur : Expr → Option (PackedTerm E Γ)) {sort}
    (op : Operation E.signature 2 (fun _ => sort) sort) (es : List Expr) :
    fold? (fun e => (recur e).map (mapPacked f)) (Operation.map f op) es =
      (fold? recur op es).map (mapPacked f) := by
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b rest =>
      simp [fold?, typedTerms_map, Option.bind_map, Option.map_bind, mapPacked, foldTerms_map]

theorem multiply_map (recur : Expr → Option (PackedTerm E Γ)) (es : List Expr) :
    multiply? (fun e => (recur e).map (mapPacked f)) es =
      (multiply? recur es).map (mapPacked f) := by
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b rest =>
      simp [multiply?, typedTerms_map, Option.bind_map, Option.map_bind, mapPacked]

theorem compare_map (recur : Expr → Option (PackedTerm E Γ))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool) (es : List Expr) :
    compare? (fun e => (recur e).map (mapPacked f)) (Operation.map f op) reverse es =
      (compare? recur op reverse es).map (mapPacked f) := by
  have relation (a b : Term E.signature Γ .int) :
      (Term.app op (Fin.cases (if reverse then b else a)
        (fun _ => if reverse then a else b))).map f =
        .app (Operation.map f op) (Fin.cases (if reverse then b.map f else a.map f)
          (fun _ => if reverse then a.map f else b.map f)) := by
    cases reverse <;> simp [Bool.false_eq_true]
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b rest =>
      simp [compare?, typedTerms_map, Option.bind_map, Option.map_bind, mapPacked,
        conjunction_map, Surface.adjacent_natural (Term.map f) (Term.map f)
          (fun a b => .app op (Fin.cases (if reverse then b else a)
            (fun _ => if reverse then a else b)))
          (fun a b => .app (Operation.map f op) (Fin.cases (if reverse then b else a)
            (fun _ => if reverse then a else b))) (fun a b => (relation a b).symm)]

theorem equalities_map (recur : Expr → Option (PackedTerm E Γ))
    (distinct : Bool) (es : List Expr) :
    equalities? (fun e => (recur e).map (mapPacked f)) distinct es =
      (equalities? recur distinct es).map (mapPacked f) := by
  have relation {sort} (a b : Term E.signature Γ sort) :
      (if distinct then Term.app .not (fun _ => .app (.eq sort) (Fin.cases a (fun _ => b)))
        else .app (.eq sort) (Fin.cases a (fun _ => b))).map f =
      (if distinct then .app .not (fun _ => .app (.eq sort) (Fin.cases (a.map f) (fun _ => b.map f)))
        else .app (.eq sort) (Fin.cases (a.map f) (fun _ => b.map f))) := by
    cases distinct <;> simp [Term.map, Operation.map]
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b rest =>
      simp [equalities?, typedTerms_map, Option.bind_map, Option.map_bind, mapPacked]
      congr 1
      funext first
      congr 1
      funext tail
      have adjacent := Surface.adjacent_natural (Term.map f) (Term.map f)
        (fun a b => if distinct then Term.app .not (fun _ =>
          .app (.eq first.sort) (Fin.cases a (fun _ => b)))
          else .app (.eq first.sort) (Fin.cases a (fun _ => b)))
        (fun a b => if distinct then Term.app .not (fun _ =>
          .app (.eq first.sort) (Fin.cases a (fun _ => b)))
          else .app (.eq first.sort) (Fin.cases a (fun _ => b)))
        (fun a b => (relation a b).symm) (first.term :: tail)
      have pairs := Surface.allPairs_natural (Term.map f) (Term.map f)
        (fun a b => if distinct then Term.app .not (fun _ =>
          .app (.eq first.sort) (Fin.cases a (fun _ => b)))
          else .app (.eq first.sort) (Fin.cases a (fun _ => b)))
        (fun a b => if distinct then Term.app .not (fun _ =>
          .app (.eq first.sort) (Fin.cases a (fun _ => b)))
          else .app (.eq first.sort) (Fin.cases a (fun _ => b)))
        (fun a b => (relation a b).symm) (first.term :: tail)
      cases distinct with
      | false =>
        simpa only [Bool.false_eq_true, ↓reduceIte, List.map_cons, conjunction_map]
          using congrArg (fun terms => some (⟨.bool, conjunction terms⟩ : PackedTerm F Γ)) adjacent
      | true =>
        simpa only [↓reduceIte, List.map_cons, conjunction_map]
          using congrArg (fun terms => some (⟨.bool, conjunction terms⟩ : PackedTerm F Γ)) pairs

theorem arguments_map (recur : Expr → Option (PackedTerm E Γ))
    (inputs : List (SortCode String)) (es : List Expr) :
    decodeArguments? (fun e => (recur e).map (mapPacked f)) inputs es =
      (decodeArguments? recur inputs es).map (fun terms i => (terms i).map f) := by
  induction inputs generalizing es with
  | nil =>
    cases es with
    | nil =>
      simp only [decodeArguments?, Option.map_some]
      congr 1
      funext i
      exact i.elim0
    | cons e es => rfl
  | cons input inputs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp [decodeArguments?, Option.bind_map, Option.map_bind, ih]

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
