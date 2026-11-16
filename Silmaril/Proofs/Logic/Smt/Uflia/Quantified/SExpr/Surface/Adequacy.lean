module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Defs
public import Silmaril.Logic.Smt.Uflia.Quantified.Substitution.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
open Silmaril.Logic.Smt.Uflia.SExpr
variable {E : Environment} (M : Model E.signature)
variable {k : Nat} {Γ : Fin k → SortCode String}
variable (ρ : ∀ i, M.carriers.value (Γ i))

def denoteData {s} (t : Quantified.Term E.signature Γ s) : Data M s :=
  ⟨Quantified.eval M ρ t, SExpr.integerValue? t⟩
def denote (t : SExpr.PackedTerm E Γ) : Value M := ⟨t.sort, denoteData M ρ t.term⟩
def denoteLocals (locals : SExpr.Locals E Γ) : Locals M :=
  locals.map (fun entry => (entry.1, denote M ρ entry.2))

@[simp] theorem denote_app {n inputs output} (op : Operation E.signature n inputs output)
    (args : ∀ i, Quantified.Term E.signature Γ (inputs i)) :
    denoteData M ρ (.app op args) = apply M op (fun i => denoteData M ρ (args i)) := by
  cases op <;> try rfl
  cases output <;> rcases n with _ | (_ | n) <;> rfl

@[simp] theorem expect_denote (t : SExpr.PackedTerm E Γ) (s : SortCode String) :
    (denote M ρ t).expect? s = (t.expect? s).map (denoteData M ρ) := by
  rcases t with ⟨sort, term⟩
  by_cases h : sort = s
  · subst sort; simp [Value.expect?, SExpr.PackedTerm.expect?, denote]
  · simp [Value.expect?, SExpr.PackedTerm.expect?, denote, h]

@[simp] theorem expect_denote_value (t : SExpr.PackedTerm E Γ) (s : SortCode String) :
    Value.expect? s ⟨t.sort, denoteData M ρ t.term⟩ =
      (t.expect? s).map (denoteData M ρ) := expect_denote M ρ t s

theorem denote_cases {input : SortCode String} {inputs : List (SortCode String)}
    (x : Quantified.Term E.signature Γ input)
    (xs : ∀ i, Quantified.Term E.signature Γ (inputs.get i)) :
    (fun i => denoteData M ρ (Fin.cases (motive := fun j =>
      Quantified.Term E.signature Γ ((input :: inputs).get j)) x xs i)) =
      Fin.cases (motive := fun j => Data M ((input :: inputs).get j))
        (denoteData M ρ x) (fun i => denoteData M ρ (xs i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i


theorem denote_finCases {n : Nat} {sorts : Fin (n + 1) → SortCode String}
    (a : Quantified.Term E.signature Γ (sorts 0))
    (bs : ∀ i, Quantified.Term E.signature Γ (sorts i.succ)) :
    (fun i => denoteData M ρ (Fin.cases (motive := fun j =>
      Quantified.Term E.signature Γ (sorts j)) a bs i)) =
      Fin.cases (motive := fun j => Data M (sorts j))
        (denoteData M ρ a) (fun i => denoteData M ρ (bs i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i



theorem denote_finCases_apply {n : Nat} {sorts : Fin (n + 1) → SortCode String}
    (a : Quantified.Term E.signature Γ (sorts 0))
    (bs : ∀ i, Quantified.Term E.signature Γ (sorts i.succ)) (i : Fin (n + 1)) :
    denoteData M ρ (Fin.cases (motive := fun j =>
      Quantified.Term E.signature Γ (sorts j)) a bs i) =
      Fin.cases (motive := fun j => Data M (sorts j))
        (denoteData M ρ a) (fun i => denoteData M ρ (bs i)) i := by
  exact Fin.cases rfl (fun _ => rfl) i



@[simp 1100] theorem denote_app2 {input output}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a b : Quantified.Term E.signature Γ input) :
    denoteData M ρ (.app op (Fin.cases a (fun _ => b))) =
      apply M op (Fin.cases (denoteData M ρ a) (fun _ => denoteData M ρ b)) := by
  rw [denote_app]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp 1100] theorem denote_ite {s} (c : Quantified.Term E.signature Γ .bool)
    (a b : Quantified.Term E.signature Γ s) :
    denoteData M ρ (.app (.ite s) (Fin.cases c (Fin.cases a (fun _ => b)))) =
      apply M (.ite s) (Fin.cases (denoteData M ρ c)
        (Fin.cases (denoteData M ρ a) (fun _ => denoteData M ρ b))) := by
  rw [denote_app]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i


theorem arguments_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    (inputs : List (SortCode String)) (es : List Expr) :
    arguments? M (fun e => (recur e).map (denote M ρ)) inputs es =
      (SExpr.decodeArguments? recur inputs es).map (fun terms i => denoteData M ρ (terms i)) := by
  induction inputs generalizing es with
  | nil =>
    cases es with
    | nil =>
      simp only [arguments?, SExpr.decodeArguments?, Option.map_some]
      congr 1
      funext i
      exact i.elim0
    | cons e es => rfl
  | cons input inputs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp [arguments?, SExpr.decodeArguments?, Option.bind_map, Option.map_bind,
        ih, denote_cases]

theorem uf_commute (recur : Expr → Option (SExpr.PackedTerm E Γ)) (name : String) (es : List Expr) :
    uf? E M (fun e => (recur e).map (denote M ρ)) name es =
      (SExpr.applyUF? E recur name es).map (denote M ρ) := by
  simp [uf?, SExpr.applyUF?, arguments_commute, Option.bind_map, Option.map_bind, denote]

theorem unary_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    {input output} (op : Operation E.signature 1 (fun _ => input) output) (a : Expr) :
    unary? M (fun e => (recur e).map (denote M ρ)) op a =
      (SExpr.unary? recur op a).map (denote M ρ) := by
  simp [unary?, SExpr.unary?, Option.bind_map, Option.map_bind, denote]

theorem binary_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    {input output} (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr) :
    binary? M (fun e => (recur e).map (denote M ρ)) op a b =
      (SExpr.binary? recur op a b).map (denote M ρ) := by
  simp [binary?, SExpr.binary?, Option.bind_map, Option.map_bind, denote]

theorem negate_commute (decoded : Option (SExpr.PackedTerm E Γ)) :
    negate? M (decoded.map (denote M ρ)) = (SExpr.negate? decoded).map (denote M ρ) := by
  simp [negate?, SExpr.negate?, Option.bind_map, Option.map_bind, denote]

theorem implication_commute (recur : Expr → Option (SExpr.PackedTerm E Γ)) (a b : Expr) :
    implication? M (fun e => (recur e).map (denote M ρ)) a b =
      (SExpr.implication? recur a b).map (denote M ρ) := by
  simp [implication?, SExpr.implication?, Option.bind_map, Option.map_bind, denote]

theorem xor_commute (recur : Expr → Option (SExpr.PackedTerm E Γ)) (a b : Expr) :
    xor? M (fun e => (recur e).map (denote M ρ)) a b =
      (SExpr.xor? recur a b).map (denote M ρ) := by
  simp [xor?, SExpr.xor?, Option.bind_map, Option.map_bind, denote]

theorem ite_commute (recur : Expr → Option (SExpr.PackedTerm E Γ)) (c a b : Expr) :
    ite? M (fun e => (recur e).map (denote M ρ)) c a b =
      (SExpr.ite? recur c a b).map (denote M ρ) := by
  simp [ite?, SExpr.ite?, Option.bind_map, Option.map_bind, denote]

@[simp] theorem local_commute (locals : SExpr.Locals E Γ) (name : String) :
    local? (denoteLocals M ρ locals) name = (SExpr.local? locals name).map (denote M ρ) := by
  induction locals with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp [denoteLocals, local?, SExpr.local?]
    split <;> simp_all [denoteLocals]

@[simp] theorem denoteLocals_append (xs ys : SExpr.Locals E Γ) :
    denoteLocals M ρ (xs ++ ys) = denoteLocals M ρ xs ++ denoteLocals M ρ ys := List.map_append


@[simp] theorem localNames_any (xs : SExpr.Locals E Γ) (name : String) :
    ((denoteLocals M ρ xs).any (fun pair => pair.1 == name)) =
      xs.any (fun pair => pair.1 == name) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [denoteLocals, List.map_cons, List.any_cons] at *; rw [ih]


@[simp] theorem mappedNames_any (xs : SExpr.Locals E Γ) (name : String) :
    (xs.map (fun entry => (entry.1, denote M ρ entry.2))).any (fun pair => pair.1 == name) =
      xs.any (fun pair => pair.1 == name) := localNames_any M ρ xs name

theorem letBindings_commute (recur : Expr → Option (SExpr.PackedTerm E Γ)) (es : List Expr) :
    letBindings? M (fun e => (recur e).map (denote M ρ)) es =
      (SExpr.letBindings? recur es).map (denoteLocals M ρ) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    unfold letBindings? SExpr.letBindings?
    split <;> simp_all [Option.bind_map, Option.map_bind, apply_ite]
    simp [denoteLocals, List.any_map, Function.comp_def]
    intro _ _; simp only [mappedNames_any]

theorem mapM_natural {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.mapM (fun a => (f a).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.mapM_cons, ih, Option.bind_map, Option.map_bind]

theorem typedValues_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    (s : SortCode String) (es : List Expr) :
    typedValues? M (fun e => (recur e).map (denote M ρ)) s es =
      (SExpr.typedTerms? recur s es).map (List.map (denoteData M ρ)) := by
  have h : (fun e => do
      let t ← (recur e).map (denote M ρ)
      t.expect? s) = (fun e => ((recur e).bind (SExpr.PackedTerm.expect? s)).map (denoteData M ρ)) := by
    funext e
    simp [Option.bind_map, Option.map_bind]
  unfold typedValues? SExpr.typedTerms?
  rw [h, mapM_natural]
  rfl

theorem foldValues_commute {s} (op : Operation E.signature 2 (fun _ => s) s)
    (first : Quantified.Term E.signature Γ s) (rest : List (Quantified.Term E.signature Γ s)) :
    foldValues M op (denoteData M ρ first) (rest.map (denoteData M ρ)) =
      denoteData M ρ (SExpr.foldTerms op first rest) := by
  induction rest generalizing first with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldValues, SExpr.foldTerms, List.map_cons, List.foldl_cons]
    simpa only [SExpr.pair, denote_app2, pair, foldValues, SExpr.foldTerms] using ih (SExpr.pair op first x)

theorem fold_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    {s} (op : Operation E.signature 2 (fun _ => s) s) (es : List Expr) :
    fold? M (fun e => (recur e).map (denote M ρ)) op es =
      (SExpr.fold? recur op es).map (denote M ρ) := by
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b es =>
      simp [fold?, SExpr.fold?, typedValues_commute, Option.bind_map, Option.map_bind,
        denote, foldValues_commute]

theorem conjunction_commute (ts : List (Quantified.Formula E.signature Γ)) :
    conjunction M (ts.map (denoteData M ρ)) = denoteData M ρ (SExpr.conjunction ts) := by
  cases ts with
  | nil => rfl
  | cons t ts => exact foldValues_commute M ρ .and t ts

theorem literal_ref {l : Nat} {Δ : Fin l → SortCode String} {s} (r : Ref Δ s) :
    SExpr.integerValue? (r.term : Quantified.Term E.signature Δ s) = none := by
  cases r
  rfl

/-- Literal metadata is invariant under bound-index renaming. -/
theorem literal_rename {s} (t : Quantified.Term E.signature Γ s) :
    ∀ {l : Nat} {Δ : Fin l → SortCode String} (r : ∀ i, Ref Δ (Γ i)),
      SExpr.integerValue? (t.rename r) = SExpr.integerValue? t := by
  induction t with
  | var i => intro l Δ r; exact literal_ref (r i)
  | @app k Γ n inputs output op args ih =>
    intro l Δ r
    cases op <;> try rfl
    · cases output <;> rcases n with _ | (_ | n) <;> rfl
    · exact congrArg (Option.map _) (ih 0 r)
  | all sort body ih => intro l Δ r; rfl
  | ex sort body ih => intro l Δ r; rfl

@[simp] theorem denote_weaken {s} (t : Quantified.Term E.signature Γ s)
    (sort : SortCode String) (x : M.carriers.value sort) :
    denoteData M (Fin.cases x ρ) (t.weaken sort) = denoteData M ρ t := by
  unfold denoteData
  rw [eval_weaken, Term.weaken, literal_rename]


theorem adjacent_natural {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (r : α → α → γ) (q : β → β → δ)
    (h : ∀ a b, q (f a) (f b) = g (r a b)) (xs : List α) :
    SExpr.adjacent q (xs.map f) = (SExpr.adjacent r xs).map g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b rest =>
      simp only [List.map_cons] at ih
      simp only [List.map_cons, SExpr.adjacent, h]
      exact congrArg (List.cons (g (r a b))) ih

theorem allPairs_natural {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (r : α → α → γ) (q : β → β → δ)
    (h : ∀ a b, q (f a) (f b) = g (r a b)) (xs : List α) :
    SExpr.allPairs q (xs.map f) = (SExpr.allPairs r xs).map g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [SExpr.allPairs, List.map_map, h, ih, Function.comp_def]

theorem compare_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool) (es : List Expr) :
    compare? M (fun e => (recur e).map (denote M ρ)) op reverse es =
      (SExpr.compare? recur op reverse es).map (denote M ρ) := by
  have rel (a b : Quantified.Term E.signature Γ .int) :
      apply M op (Fin.cases (if reverse then denoteData M ρ b else denoteData M ρ a)
        (fun _ => if reverse then denoteData M ρ a else denoteData M ρ b)) =
      denoteData M ρ (.app op (Fin.cases (if reverse then b else a)
        (fun _ => if reverse then a else b))) := by
    cases reverse <;> simp
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b es =>
      simp [compare?, SExpr.compare?, typedValues_commute, Option.bind_map, Option.map_bind,
        denote, adjacent_natural (denoteData M ρ) (denoteData M ρ)
          (fun a b => .app op (Fin.cases (if reverse then b else a) (fun _ => if reverse then a else b)))
          (fun a b => apply M op (Fin.cases (if reverse then b else a) (fun _ => if reverse then a else b))) rel, conjunction_commute]

theorem relationLists_commute {s}
    (rt : Quantified.Term E.signature Γ s → Quantified.Term E.signature Γ s → Quantified.Formula E.signature Γ)
    (rv : Data M s → Data M s → Data M .bool)
    (h : ∀ a b, rv (denoteData M ρ a) (denoteData M ρ b) = denoteData M ρ (rt a b))
    (all : Bool) (ts : List (Quantified.Term E.signature Γ s)) :
    conjunction M (if all then SExpr.allPairs rv (ts.map (denoteData M ρ))
      else SExpr.adjacent rv (ts.map (denoteData M ρ))) =
    denoteData M ρ (SExpr.conjunction (if all then SExpr.allPairs rt ts else SExpr.adjacent rt ts)) := by
  cases all
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [adjacent_natural (denoteData M ρ) (denoteData M ρ) rt rv h]
    exact conjunction_commute M ρ _
  · simp only [ite_true]
    rw [allPairs_natural (denoteData M ρ) (denoteData M ρ) rt rv h]
    exact conjunction_commute M ρ _

theorem equalities_commute (recur : Expr → Option (SExpr.PackedTerm E Γ))
    (distinct : Bool) (es : List Expr) :
    equalities? M (fun e => (recur e).map (denote M ρ)) distinct es =
      (SExpr.equalities? recur distinct es).map (denote M ρ) := by
  have rel {s} (a b : Quantified.Term E.signature Γ s) :
      (if distinct then apply M .not (fun _ => apply M (.eq s)
        (Fin.cases (denoteData M ρ a) (fun _ => denoteData M ρ b)))
       else apply M (.eq s) (Fin.cases (denoteData M ρ a) (fun _ => denoteData M ρ b))) =
      denoteData M ρ (if distinct then .app .not (fun _ =>
        .app (.eq s) (Fin.cases a (fun _ => b)))
        else .app (.eq s) (Fin.cases a (fun _ => b))) := by
    cases distinct <;> simp
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b es =>
      simp [equalities?, SExpr.equalities?, typedValues_commute, Option.bind_map,
        Option.map_bind, denote]
      congr 1
      funext first
      congr 1
      funext tail
      have h := relationLists_commute M ρ
        (fun a b => if distinct then .app .not (fun _ => .app (.eq first.sort) (Fin.cases a (fun _ => b)))
          else .app (.eq first.sort) (Fin.cases a (fun _ => b)))
        (fun a b => if distinct then apply M .not (fun _ => apply M (.eq first.sort) (Fin.cases a (fun _ => b)))
          else apply M (.eq first.sort) (Fin.cases a (fun _ => b)))
        (rel (s := first.sort)) distinct (first.term :: tail)
      simpa only [List.map_cons] using congrArg (fun v : Data M .bool => some (⟨.bool, v⟩ : Value M)) h

def scaleAny {s} (coefficient : Int) (v : Data M s) : Data M s :=
  match s with
  | .int => scale M coefficient v
  | .bool => v
  | .user _ => v

theorem scaleLinear_commute {s} (t : Quantified.Term E.signature Γ s) (coefficient : Int) :
    denoteData M ρ (SExpr.scaleLinear coefficient t) = scaleAny M coefficient (denoteData M ρ t) := by
  induction t generalizing coefficient with
  | @var k Γ i =>
    unfold SExpr.scaleLinear
    generalize (Quantified.Term.var i : Quantified.Term E.signature Γ (Γ i)) = term
    generalize Γ i = sort at term ⊢
    cases sort <;> rfl
  | @app k Γ n inputs output op args ih =>
    cases op with
    | uf symbol =>
      cases output <;> rcases n with _ | (_ | n) <;>
        simp [SExpr.scaleLinear, scaleAny, denoteData, scale, Quantified.eval,
          Model.apply, SExpr.integerValue?]
    | integer value => rfl
    | add =>
      have h0 := congrArg Data.value (ih 0 ρ coefficient)
      have h1 := congrArg Data.value (ih 1 ρ coefficient)
      simp only [scaleAny, scale, denoteData] at h0 h1
      simp [SExpr.scaleLinear, SExpr.pair, denoteData, Quantified.eval, Model.apply,
        SExpr.integerValue?, Fin.cases, Fin.induction, Fin.induction.go, h0, h1, scaleAny, scale, Int.mul_add]
    | sub =>
      have h0 := congrArg Data.value (ih 0 ρ coefficient)
      have h1 := congrArg Data.value (ih 1 ρ coefficient)
      simp only [scaleAny, scale, denoteData] at h0 h1
      simp [SExpr.scaleLinear, SExpr.pair, denoteData, Quantified.eval, Model.apply,
        SExpr.integerValue?, Fin.cases, Fin.induction, Fin.induction.go, h0, h1, scaleAny, scale, Int.mul_sub]
    | scale scalar =>
      rw [SExpr.scaleLinear, ih]
      simp [scaleAny, scale, denote_app, apply, Model.apply, Int.mul_assoc, Option.map_map,
        Function.comp_def]
    | boolean b => rfl
    | le => rfl
    | lt => rfl
    | eq s => rfl
    | not => rfl
    | and => rfl
    | or => rfl
    | ite s =>
      cases output <;> rfl
  | all sort body ih => rfl
  | ex sort body ih => rfl

theorem multiplyFactors_commute (ts : List (Quantified.Term E.signature Γ .int))
    (coefficient : Int) (factor : Option (Quantified.Term E.signature Γ .int)) :
    multiplyFactors? M (ts.map (denoteData M ρ)) coefficient (factor.map (denoteData M ρ)) =
      (SExpr.multiplyFactors? ts coefficient factor).map (denoteData M ρ) := by
  induction ts generalizing coefficient factor with
  | nil =>
    cases factor with
    | none => rfl
    | some t => simp [multiplyFactors?, SExpr.multiplyFactors?, scaleLinear_commute, scaleAny]
  | cons t ts ih =>
    simp only [List.map_cons, multiplyFactors?]
    change (match SExpr.integerValue? t with
      | some n => multiplyFactors? M (ts.map (denoteData M ρ)) (coefficient * n) (factor.map (denoteData M ρ))
      | none => match factor.map (denoteData M ρ) with
        | some _ => none
        | none => multiplyFactors? M (ts.map (denoteData M ρ)) coefficient (some (denoteData M ρ t))) = _
    cases h : SExpr.integerValue? t with
    | some n => simpa only [SExpr.multiplyFactors?, h] using ih (coefficient * n) factor
    | none =>
      cases factor with
      | none => simpa only [SExpr.multiplyFactors?, h, Option.map_none, Option.map_some] using ih coefficient (some t)
      | some u => simp only [Option.map_some, SExpr.multiplyFactors?, h, Option.map_none]

theorem multiply_commute (recur : Expr → Option (SExpr.PackedTerm E Γ)) (es : List Expr) :
    multiply? M (fun e => (recur e).map (denote M ρ)) es =
      (SExpr.multiply? recur es).map (denote M ρ) := by
  cases es with
  | nil => rfl
  | cons a es =>
    cases es with
    | nil => rfl
    | cons b es =>
      simp [multiply?, SExpr.multiply?, typedValues_commute, Option.bind_map, Option.map_bind,
        denote]
      congr 1
      funext ts
      have h := multiplyFactors_commute M ρ ts 1 none
      simp only [Option.map_none] at h
      rw [h]
      simp only [Option.bind_map, Function.comp_def]

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
