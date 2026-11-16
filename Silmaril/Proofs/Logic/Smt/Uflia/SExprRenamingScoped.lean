module

public import Silmaril.Proofs.Logic.Smt.Uflia.SExprRenamingOperators
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
variable {E F : Environment}

/-- Decimal parsing cannot recover after a failed digit. -/
theorem digits_fold_none (base : Nat) (val : Char → Option Nat) (cs : List Char) :
    cs.foldl (fun acc c => acc.bind (fun a => (val c).map (a * base + ·))) none = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

/-- A decoded decimal numeral starts with an actual decimal digit. -/
theorem decimal_head {c : Char} {cs : List Char} {n : Nat}
    (h : Silmaril.Logic.Smt.digits 10 Silmaril.Logic.Smt.decVal (c :: cs) = some n) :
    ∃ k, Silmaril.Logic.Smt.decVal c = some k := by
  cases hc : Silmaril.Logic.Smt.decVal c with
  | some k => exact ⟨k, rfl⟩
  | none =>
      simp only [Silmaril.Logic.Smt.digits, List.foldl_cons, Option.bind_some, hc,
        Option.map_none, digits_fold_none, reduceCtorEq] at h

/-- Decimal digits are excluded from the initial-character alphabet of symbols. -/
theorem decimal_not_initial {c : Char} {k : Nat}
    (h : Silmaril.Logic.Smt.decVal c = some k) :
    (c.isAlpha || "~!@$%^&*_-+=<>.?/".toList.contains c) = false := by
  unfold Silmaril.Logic.Smt.decVal at h
  split at h
  · rename_i bounds
    have hzero : '0'.toNat = 48 := rfl
    have hnine : '9'.toNat = 57 := rfl
    have hn : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
      simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val, hzero, hnine] using bounds
    obtain ⟨lower, upper⟩ := hn
    interval_cases hc : c.toNat <;>
      have heq := congrArg Char.ofNat hc <;>
      simp only [Char.ofNat_toNat] at heq <;>
      subst c <;> decide
  · contradiction

/-- Numeral atoms cannot also denote declared simple symbols. -/
theorem naturalNumeral_not_simpleSymbol {name : String} {n : Nat}
    (h : naturalNumeral? name = some n) : simpleSymbol name = false := by
  have hd : Silmaril.Logic.Smt.digits 10 Silmaril.Logic.Smt.decVal name.toList = some n := by
    unfold naturalNumeral? at h
    split at h
    · contradiction
    · exact h
  cases hs : name.toList with
  | nil => simp [hs, Silmaril.Logic.Smt.digits] at hd
  | cons c cs =>
      rw [hs] at hd
      obtain ⟨k, hk⟩ := decimal_head hd
      simp only [simpleSymbol, hs, decimal_not_initial hk, Bool.false_and]

/-- Successful declaration lookup certifies both lexical admission checks. -/
theorem lookup_lexical {name : String} {i : Fin E.declarations.length}
    (h : lookup? E name = some i) :
    simpleSymbol name = true ∧ reserved.contains name = false := by
  unfold lookup? at h
  split at h
  · rename_i valid
    simp only [Bool.and_eq_true] at valid
    refine ⟨valid.1, ?_⟩
    cases hr : reserved.contains name <;> simp_all
  · contradiction

/-- A looked-up symbol cannot be interpreted as a numeral atom. -/
theorem lookup_not_numeral {name : String} {i : Fin E.declarations.length}
    (h : lookup? E name = some i) : numeral? (.atom name) = none := by
  have hsimple := (lookup_lexical h).1
  cases hn : naturalNumeral? name with
  | none => simp only [numeral?, hn, Option.map_none]
  | some n =>
      have hnot := naturalNumeral_not_simpleSymbol hn
      rw [hsimple] at hnot
      contradiction

/-- A legal nonliteral atom reaches the actual UF decoder in an empty scope. -/
theorem decodeAtomUF (fuel : Nat) (name : String)
    (hreserved : reserved.contains name = false) (hnumeral : numeral? (.atom name) = none) :
    decodeScopedFuel? E (fuel + 1) [] (.atom name) =
      applyUF? E (decodeScopedFuel? E fuel []) name [] := by
  unfold decodeScopedFuel?
  split <;> simp_all [reserved, local?]

/-- A legal nonempty application reaches UF decoding rather than a builtin. -/
theorem decodeApplicationUF (fuel : Nat) (name : String) (es : List Expr)
    (hreserved : reserved.contains name = false) (hne : es ≠ []) :
    decodeScopedFuel? E (fuel + 1) [] (.list (.atom name :: es)) =
      applyUF? E (decodeScopedFuel? E fuel []) name es := by
  unfold decodeScopedFuel?
  split <;> simp_all [reserved, local?]

/-- A syntax correspondence preserves successful recursive results while
allowing the argument expression itself to change. -/
def DecodeRelated (source target : Expr → Option (PackedTerm E)) (a b : Expr) : Prop :=
  ∀ value, source a = some value → target b = some value

/-- Sequence corresponding expressions without identifying their raw syntax. -/
theorem mapM_related {α β γ : Type} {source : α → Option γ} {target : β → Option γ}
    {xs : List α} {ys : List β}
    (hrelated : List.Forall₂ (fun a b => ∀ value,
      source a = some value → target b = some value) xs ys)
    (values : List γ) (h : xs.mapM source = some values) : ys.mapM target = some values := by
  induction hrelated generalizing values with
  | nil => exact h
  | @cons a b xs ys head tail ih =>
      simp [List.mapM_cons, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨value, hv, values, hvs, rfl⟩ := h
      exact ⟨value, head value hv, values, ih values hvs, rfl⟩

/-- Sort checks preserve a successful syntax correspondence. -/
theorem typedTerms_related {source target : Expr → Option (PackedTerm E)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (sort : SortCode String) (values : List (Uflia.Term E.signature sort))
    (h : typedTerms? source sort xs = some values) : typedTerms? target sort ys = some values := by
  apply mapM_related (values := values) ?_ h
  clear h values
  induction hrelated with
  | nil => exact .nil
  | @cons a b xs ys head tail ih =>
      refine .cons ?_ ih
      intro term decoded
      change (source a).bind (fun value => value.expect? sort) = some term at decoded
      change (target b).bind (fun value => value.expect? sort) = some term
      cases hv : source a with
      | none => simp only [hv, Option.bind_none, reduceCtorEq] at decoded
      | some value =>
          simpa only [head value hv, hv, Option.bind_some] using decoded

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem unary_related {source target : Expr → Option (PackedTerm E)}
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e e' : Expr)
    (hE: DecodeRelated source target e e')
    (value : PackedTerm E) (h : unary? source op e = some value) :
    unary? target op e' = some value := by
  cases he : source e with
  | none => simp [unary?, he] at h
  | some ve =>
      simpa only [unary?, he, hE ve he, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem binary_related {source target : Expr → Option (PackedTerm E)}
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a a' : Expr) (b b' : Expr)
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E) (h : binary? source op a b = some value) :
    binary? target op a' b' = some value := by
  cases ha : source a with
  | none => simp [binary?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [binary?, ha, hb] at h
      | some vb =>
          simpa only [binary?, ha, hb, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem implication_related {source target : Expr → Option (PackedTerm E)}
    (a a' : Expr) (b b' : Expr)
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E) (h : implication? source a b = some value) :
    implication? target a' b' = some value := by
  cases ha : source a with
  | none => simp [implication?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [implication?, ha, hb] at h
      | some vb =>
          simpa only [implication?, ha, hb, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem xor_related {source target : Expr → Option (PackedTerm E)}
    (a a' : Expr) (b b' : Expr)
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E) (h : xor? source a b = some value) :
    xor? target a' b' = some value := by
  cases ha : source a with
  | none => simp [xor?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [xor?, ha, hb] at h
      | some vb =>
          simpa only [xor?, ha, hb, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem ite_related {source target : Expr → Option (PackedTerm E)}
    (c c' : Expr) (a a' : Expr) (b b' : Expr)
    (hC: DecodeRelated source target c c')
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E) (h : ite? source c a b = some value) :
    ite? target c' a' b' = some value := by
  cases hc : source c with
  | none => simp [ite?, hc] at h
  | some vc =>
      cases ha : source a with
      | none => simp [ite?, hc, ha] at h
      | some va =>
          cases hb : source b with
          | none => simp [ite?, hc, ha, hb] at h
          | some vb =>
              simpa only [ite?, hc, ha, hb, hC vc hc, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding argument lists preserve successful folded elaboration. -/
theorem fold_related {source target : Expr → Option (PackedTerm E)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (value : PackedTerm E) (h : fold? source op xs = some value) :
    fold? target op ys = some value := by
  cases hrelated with
  | nil => simp [fold?] at h
  | @cons a a' xs ys first tail =>
      cases tail with
      | nil => simp [fold?] at h
      | @cons b b' xs ys second tail =>
          change (source a).bind _ = some value at h
          obtain ⟨va, ha, h⟩ := Option.bind_eq_some_iff.mp h
          change (va.expect? sort).bind _ = some value at h
          obtain ⟨ta, hta, h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? source sort (b :: xs)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          change (target a').bind _ = some value
          rw [first va ha]
          change (va.expect? sort).bind _ = some value
          rw [hta]
          change (typedTerms? target sort (b' :: ys)).bind _ = some value
          rw [typedTerms_related (.cons second tail) sort ts hts]
          exact h

/-- Chained comparisons retain decoded values under corresponding syntax. -/
theorem compare_related {source target : Expr → Option (PackedTerm E)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (value : PackedTerm E) (h : compare? source op reverse xs = some value) :
    compare? target op reverse ys = some value := by
  cases hrelated with
  | nil => simp [compare?] at h
  | @cons a a' xs ys first tail =>
      cases tail with
      | nil => simp [compare?] at h
      | @cons b b' xs ys second tail =>
          change (typedTerms? source .int (a :: b :: xs)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? target .int (a' :: b' :: ys)).bind _ = some value
          rw [typedTerms_related (.cons first (.cons second tail)) .int ts hts]
          exact h

/-- Adjacent equality and all-pairs distinctness retain their successful values. -/
theorem equalities_related {source target : Expr → Option (PackedTerm E)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (distinct : Bool) (value : PackedTerm E)
    (h : equalities? source distinct xs = some value) :
    equalities? target distinct ys = some value := by
  cases hrelated with
  | nil => simp [equalities?] at h
  | @cons a a' xs ys first tail =>
      cases tail with
      | nil => simp [equalities?] at h
      | @cons b b' xs ys second tail =>
          change (source a).bind _ = some value at h
          obtain ⟨va, ha, h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? source va.sort (b :: xs)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          change (target a').bind _ = some value
          rw [first va ha]
          change (typedTerms? target va.sort (b' :: ys)).bind _ = some value
          rw [typedTerms_related (.cons second tail) va.sort ts hts]
          exact h

/-- Linear multiplication retains its coefficient and factor checks. -/
theorem multiply_related {source target : Expr → Option (PackedTerm E)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (value : PackedTerm E) (h : multiply? source xs = some value) :
    multiply? target ys = some value := by
  cases hrelated with
  | nil => simp [multiply?] at h
  | @cons a a' xs ys first tail =>
      cases tail with
      | nil => simp [multiply?] at h
      | @cons b b' xs ys second tail =>
          change (typedTerms? source .int (a :: b :: xs)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? target .int (a' :: b' :: ys)).bind _ = some value
          rw [typedTerms_related (.cons first (.cons second tail)) .int ts hts]
          exact h

/-- Corresponding raw lists retain their actual number of arguments. -/
theorem forall₂_length {α β : Type} {relation : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ relation xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

/-- Every child node budget fits the sum of all actual output child budgets. -/
theorem expressionFuel_le_sum {output : Expr} {outputs : List Expr}
    (h : output ∈ outputs) : expressionFuel output ≤ expressionsFuel outputs := by
  induction outputs with
  | nil => contradiction
  | cons head tail ih =>
      rcases List.mem_cons.mp h with heq | hmem
      · subst output
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- Successful normalized child witnesses induce a concrete syntax
correspondence at any budget containing all of their actual output sizes. -/
theorem normalizedList_related (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (budget : Nat) {es outputs : List Expr}
    (hbudget : ∀ output ∈ outputs, expressionFuel output ≤ budget)
    (hnormalized : es.mapM normalize = some outputs) :
    List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f))
      (decodeTermFuel? F budget)) es outputs := by
  rw [List.mapM_eq_some_iff_forall₂] at hnormalized
  induction hnormalized with
  | nil => exact .nil
  | @cons e output es outputs ho htail ih =>
      refine .cons ?_ (ih (fun out hm => hbudget out (List.mem_cons_of_mem _ hm)))
      intro mapped decoded
      cases hv : source e with
      | none => simp only [hv, Option.map_none, reduceCtorEq] at decoded
      | some value =>
          simp only [hv, Option.map_some, Option.some.injEq] at decoded
          subst mapped
          obtain ⟨output', ho', hd⟩ := hchildren e value hv
          have heq : output' = output := Option.some.inj (ho'.symm.trans ho)
          subst output'
          exact decodeTermFuel_mono (hbudget output (List.mem_cons_self)) output _ hd

/-- Actual lexical scopes only contain admitted nonreserved binding names. -/
def LegalLocals (locals : Locals E) : Prop :=
  ∀ entry ∈ locals, simpleSymbol entry.1 = true ∧ reserved.contains entry.1 = false

/-- Scope extension preserves admission of every binding name. -/
theorem legalLocals_append {xs ys : Locals E} (hx : LegalLocals xs) (hy : LegalLocals ys) :
    LegalLocals (xs ++ ys) := by
  intro entry hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · exact hx entry hleft
  · exact hy entry hright

/-- Successful binding decoding certifies the name checks independently of
right-hand-side values and duplicate-name rejection. -/
theorem letBindings_legal (source : Expr → Option (PackedTerm E))
    (es : List Expr) (values : Locals E) (h : letBindings? source es = some values) :
    LegalLocals values := by
  induction es generalizing values with
  | nil =>
      have hv : ([] : Locals E) = values := Option.some.inj h
      cases hv
      intro entry hmem
      contradiction
  | cons e es ih =>
      show LegalLocals values
      cases e with
      | atom name =>
          have impossible : (none : Option (Locals E)) = some values := h
          cases impossible
      | list parts =>
          show LegalLocals values
          cases parts with
          | nil =>
              have impossible : (none : Option (Locals E)) = some values := h
              cases impossible
          | cons first rest =>
              show LegalLocals values
              cases first with
              | list xs =>
                  have impossible : (none : Option (Locals E)) = some values := h
                  cases impossible
              | atom name =>
                  show LegalLocals values
                  cases rest with
                  | nil => simp [letBindings?] at h
                  | cons rhs tail =>
                      show LegalLocals values
                      cases tail with
                      | cons x xs => simp [letBindings?] at h
                      | nil =>
                          show LegalLocals values
                          simp only [letBindings?] at h
                          split at h
                          · contradiction
                          · show LegalLocals values
                            rename_i valid
                            have legalName : simpleSymbol name = true ∧ reserved.contains name = false := by
                              cases hs : simpleSymbol name <;>
                                cases hr : reserved.contains name <;> simp_all
                            change (source rhs).bind _ = some values at h
                            obtain ⟨value, hv, h⟩ : ∃ value, source rhs = some value ∧ _ := Option.bind_eq_some_iff.mp h
                            change (letBindings? source es).bind _ = some values at h
                            obtain ⟨vs, hvs, h⟩ : ∃ vs, letBindings? source es = some vs ∧ _ := Option.bind_eq_some_iff.mp h
                            split at h
                            · contradiction
                            · have hvalues : (name, value) :: vs = values := Option.some.inj h
                              cases hvalues
                              intro entry hmem
                              rcases List.mem_cons.mp hmem with heq | htail
                              · subst entry
                                exact legalName
                              · exact ih vs hvs entry htail

/-- Reserved builtin names are absent from every actual lexical scope. -/
theorem legalLocals_reserved_absent {locals : Locals E} (hlegal : LegalLocals locals)
    (name : String) (hreserved : reserved.contains name = true) : local? locals name = none := by
  induction locals with
  | nil => rfl
  | cons entry locals ih =>
      rcases entry with ⟨key, value⟩
      have hkey := (hlegal (key, value) List.mem_cons_self).2
      have htail : LegalLocals locals := fun entry hm => hlegal entry (List.mem_cons_of_mem _ hm)
      by_cases hk : key = name
      · subst key
        rw [hreserved] at hkey
        contradiction
      · simpa only [local?, hk, ite_false] using ih htail

/-- Related local scopes agree on absence as well as successful value decoding. -/
theorem localsRelated_absent (f : E.signature ⟶ F.signature)
    {locals : Locals E} {syntaxLocals : SyntaxLocals}
    (hrelated : LocalsRelated f locals syntaxLocals) (name : String)
    (hlocal : local? locals name = none) : syntaxLocal? syntaxLocals name = none := by
  have h := localsRelated_lookup f hrelated name
  cases hs : syntaxLocal? syntaxLocals name with
  | none => rfl
  | some output => simp only [hlocal, hs] at h

/-- Successful sort checking entails successful decoding of every raw child. -/
theorem typedTerms_source_exists (source : Expr → Option (PackedTerm E))
    (sort : SortCode String) (es : List Expr)
    (ts : List (Uflia.Term E.signature sort)) (h : typedTerms? source sort es = some ts) :
    ∃ values, es.mapM source = some values := by
  change es.mapM (fun e => (source e).bind (fun value => value.expect? sort)) = some ts at h
  rw [List.mapM_eq_some_iff_forall₂] at h
  induction h with
  | nil => exact ⟨[], rfl⟩
  | @cons e term es terms head tail ih =>
      change (source e).bind (fun value => value.expect? sort) = some term at head
      obtain ⟨value, hv, ht⟩ := Option.bind_eq_some_iff.mp head
      obtain ⟨values, hvs⟩ := ih
      exact ⟨value :: values, by simp [hv, hvs]⟩

/-- An accepted list of source children produces actual normalized syntax and
a recursive decoding correspondence at the future parent recursion budget. -/
theorem normalizeChildren_success (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (es : List Expr) (hsource : ∃ values, es.mapM source = some values) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f))
        (decodeTermFuel? F (1 + expressionsFuel outputs))) es outputs := by
  obtain ⟨values, hv⟩ := hsource
  obtain ⟨outputs, hn, _⟩ := normalizeMapM_transport source normalize (decodeTermFuel? F)
    (mapPacked f) (fun n m h e t decoded => decodeTermFuel_mono h e t decoded)
    hchildren es values hv
  refine ⟨outputs, hn, normalizedList_related f source normalize hchildren _ ?_ hn⟩
  intro output hmem
  exact Nat.le_trans (expressionFuel_le_sum hmem) (Nat.le_add_left _ _)

/-- Successful folding decodes every child before constructing its result. -/
theorem fold_source_exists (source : Expr → Option (PackedTerm E))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (value : PackedTerm E) (h : fold? source op es = some value) :
    ∃ values, es.mapM source = some values := by
  cases es with
  | nil => simp [fold?] at h
  | cons a es =>
      cases es with
      | nil => simp [fold?] at h
      | cons b rest =>
          change (source a).bind _ = some value at h
          obtain ⟨va, ha, h⟩ := Option.bind_eq_some_iff.mp h
          change (va.expect? sort).bind _ = some value at h
          obtain ⟨ta, hta, h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? source sort (b :: rest)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨values, hv⟩ := typedTerms_source_exists source sort _ ts hts
          exact ⟨va :: values, by simp [ha, hv]⟩

/-- Successful comparisons decode all operands, in their original order. -/
theorem compare_source_exists (source : Expr → Option (PackedTerm E))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (es : List Expr) (value : PackedTerm E) (h : compare? source op reverse es = some value) :
    ∃ values, es.mapM source = some values := by
  cases es with
  | nil => simp [compare?] at h
  | cons a es =>
      cases es with
      | nil => simp [compare?] at h
      | cons b rest =>
          change (typedTerms? source .int (a :: b :: rest)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          exact typedTerms_source_exists source .int _ ts hts

/-- Successful equalities decode all operands, retaining the first inferred sort. -/
theorem equalities_source_exists (source : Expr → Option (PackedTerm E))
    (distinct : Bool) (es : List Expr) (value : PackedTerm E)
    (h : equalities? source distinct es = some value) :
    ∃ values, es.mapM source = some values := by
  cases es with
  | nil => simp [equalities?] at h
  | cons a es =>
      cases es with
      | nil => simp [equalities?] at h
      | cons b rest =>
          change (source a).bind _ = some value at h
          obtain ⟨va, ha, h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? source va.sort (b :: rest)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨values, hv⟩ := typedTerms_source_exists source va.sort _ ts hts
          exact ⟨va :: values, by simp [ha, hv]⟩

/-- Successful multiplication decodes all operands before its linearity check. -/
theorem multiply_source_exists (source : Expr → Option (PackedTerm E))
    (es : List Expr) (value : PackedTerm E) (h : multiply? source es = some value) :
    ∃ values, es.mapM source = some values := by
  cases es with
  | nil => simp [multiply?] at h
  | cons a es =>
      cases es with
      | nil => simp [multiply?] at h
      | cons b rest =>
          change (typedTerms? source .int (a :: b :: rest)).bind _ = some value at h
          obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
          exact typedTerms_source_exists source .int _ ts hts

/-- A successful fixed-arity operator decodes every one of its children. -/
theorem unary_source_exists (source : Expr → Option (PackedTerm E))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e : Expr) (value : PackedTerm E)
    (h : unary? source op e = some value) :
    ∃ values, [e].mapM source = some values := by
  cases he : source e with
  | none => simp [unary?, he] at h
  | some ve =>
      exact ⟨[ve], by simp [he]⟩

/-- A successful fixed-arity operator decodes every one of its children. -/
theorem binary_source_exists (source : Expr → Option (PackedTerm E))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : binary? source op a b = some value) :
    ∃ values, [a, b].mapM source = some values := by
  cases ha : source a with
  | none => simp [binary?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [binary?, ha, hb] at h
      | some vb =>
          exact ⟨[va, vb], by simp [ha, hb]⟩

/-- A successful fixed-arity operator decodes every one of its children. -/
theorem implication_source_exists (source : Expr → Option (PackedTerm E))
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : implication? source a b = some value) :
    ∃ values, [a, b].mapM source = some values := by
  cases ha : source a with
  | none => simp [implication?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [implication?, ha, hb] at h
      | some vb =>
          exact ⟨[va, vb], by simp [ha, hb]⟩

/-- A successful fixed-arity operator decodes every one of its children. -/
theorem xor_source_exists (source : Expr → Option (PackedTerm E))
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : xor? source a b = some value) :
    ∃ values, [a, b].mapM source = some values := by
  cases ha : source a with
  | none => simp [xor?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [xor?, ha, hb] at h
      | some vb =>
          exact ⟨[va, vb], by simp [ha, hb]⟩

/-- A successful fixed-arity operator decodes every one of its children. -/
theorem ite_source_exists (source : Expr → Option (PackedTerm E))
    (c : Expr) (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : ite? source c a b = some value) :
    ∃ values, [c, a, b].mapM source = some values := by
  cases hc : source c with
  | none => simp [ite?, hc] at h
  | some vc =>
      cases ha : source a with
      | none => simp [ite?, hc, ha] at h
      | some va =>
          cases hb : source b with
          | none => simp [ite?, hc, ha, hb] at h
          | some vb =>
              exact ⟨[vc, va, vb], by simp [hc, ha, hb]⟩

/-- Mapped recursive values form the canonical intermediate decoder. -/
theorem mappedSource_success (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (e : Expr) (value : PackedTerm E)
    (h : source e = some value) :
    (source e).map (mapPacked f) = some (mapPacked f value) := by
  simp only [h, Option.map_some]

/-- Successful source elaboration normalizes all child syntax and preserves
its mapped result at the actual parent recursion budget. -/
theorem normalizeFold_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (value : PackedTerm E)
    (h : fold? source op es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) (Operation.map f op) outputs =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren es
    (fold_source_exists source op es value h)
  refine ⟨outputs, hn, ?_⟩
  exact fold_related hr (Operation.map f op) (mapPacked f value)
    (fold_transport f (mappedSource_success f source) op es value h)

/-- Successful source elaboration normalizes all child syntax and preserves
its mapped result at the actual parent recursion budget. -/
theorem normalizeCompare_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (es : List Expr) (value : PackedTerm E)
    (h : compare? source op reverse es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) (Operation.map f op) reverse outputs =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren es
    (compare_source_exists source op reverse es value h)
  refine ⟨outputs, hn, ?_⟩
  exact compare_related hr (Operation.map f op) reverse (mapPacked f value)
    (compare_transport f (mappedSource_success f source) op reverse es value h)

/-- Successful source elaboration normalizes all child syntax and preserves
its mapped result at the actual parent recursion budget. -/
theorem normalizeEqualities_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (distinct : Bool)
    (es : List Expr) (value : PackedTerm E)
    (h : equalities? source distinct es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      equalities? (decodeTermFuel? F (1 + expressionsFuel outputs)) distinct outputs =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren es
    (equalities_source_exists source distinct es value h)
  refine ⟨outputs, hn, ?_⟩
  exact equalities_related hr distinct (mapPacked f value)
    (equalities_transport f (mappedSource_success f source) distinct es value h)

/-- Successful source elaboration normalizes all child syntax and preserves
its mapped result at the actual parent recursion budget. -/
theorem normalizeMultiply_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (es : List Expr) (value : PackedTerm E)
    (h : multiply? source es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      multiply? (decodeTermFuel? F (1 + expressionsFuel outputs)) outputs =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren es
    (multiply_source_exists source es value h)
  refine ⟨outputs, hn, ?_⟩
  exact multiply_related hr (mapPacked f value)
    (multiply_transport f (mappedSource_success f source) es value h)

/-- Fixed-arity elaboration preserves the mapped result after child syntax
normalization at the actual future parent recursion budget. -/
theorem normalizeUnary_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e : Expr) (value : PackedTerm E)
    (h : unary? source op e = some value) :
    ∃ e', [e].mapM normalize = some [e'] ∧
      unary? (decodeTermFuel? F (1 + expressionsFuel [e'])) (Operation.map f op) e' =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren [e]
    (unary_source_exists source op e value h)
  cases hr with
  | cons he hr =>
      cases hr
      refine ⟨_, hn, ?_⟩
      exact unary_related (Operation.map f op) e _ he (mapPacked f value)
        (unary_transport f (mappedSource_success f source) op e value h)

/-- Fixed-arity elaboration preserves the mapped result after child syntax
normalization at the actual future parent recursion budget. -/
theorem normalizeBinary_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : binary? source op a b = some value) :
    ∃ a' b', [a, b].mapM normalize = some [a', b'] ∧
      binary? (decodeTermFuel? F (1 + expressionsFuel [a', b'])) (Operation.map f op) a' b' =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren [a, b]
    (binary_source_exists source op a b value h)
  cases hr with
  | cons ha hr =>
      cases hr with
      | cons hb hr =>
          cases hr
          refine ⟨_, _, hn, ?_⟩
          exact binary_related (Operation.map f op) a _ b _ ha hb (mapPacked f value)
            (binary_transport f (mappedSource_success f source) op a b value h)

/-- Fixed-arity elaboration preserves the mapped result after child syntax
normalization at the actual future parent recursion budget. -/
theorem normalizeImplication_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : implication? source a b = some value) :
    ∃ a' b', [a, b].mapM normalize = some [a', b'] ∧
      implication? (decodeTermFuel? F (1 + expressionsFuel [a', b'])) a' b' =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren [a, b]
    (implication_source_exists source a b value h)
  cases hr with
  | cons ha hr =>
      cases hr with
      | cons hb hr =>
          cases hr
          refine ⟨_, _, hn, ?_⟩
          exact implication_related a _ b _ ha hb (mapPacked f value)
            (implication_transport f (mappedSource_success f source) a b value h)

/-- Fixed-arity elaboration preserves the mapped result after child syntax
normalization at the actual future parent recursion budget. -/
theorem normalizeXor_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : xor? source a b = some value) :
    ∃ a' b', [a, b].mapM normalize = some [a', b'] ∧
      xor? (decodeTermFuel? F (1 + expressionsFuel [a', b'])) a' b' =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren [a, b]
    (xor_source_exists source a b value h)
  cases hr with
  | cons ha hr =>
      cases hr with
      | cons hb hr =>
          cases hr
          refine ⟨_, _, hn, ?_⟩
          exact xor_related a _ b _ ha hb (mapPacked f value)
            (xor_transport f (mappedSource_success f source) a b value h)

/-- Fixed-arity elaboration preserves the mapped result after child syntax
normalization at the actual future parent recursion budget. -/
theorem normalizeIte_result (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (c : Expr) (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : ite? source c a b = some value) :
    ∃ c' a' b', [c, a, b].mapM normalize = some [c', a', b'] ∧
      ite? (decodeTermFuel? F (1 + expressionsFuel [c', a', b'])) c' a' b' =
        some (mapPacked f value) := by
  obtain ⟨outputs, hn, hr⟩ := normalizeChildren_success f source normalize hchildren [c, a, b]
    (ite_source_exists source c a b value h)
  cases hr with
  | cons hc hr =>
      cases hr with
      | cons ha hr =>
          cases hr with
          | cons hb hr =>
              cases hr
              refine ⟨_, _, _, hn, ?_⟩
              exact ite_related c _ a _ b _ hc ha hb (mapPacked f value)
                (ite_transport f (mappedSource_success f source) c a b value h)

/-- Reserved names are never renamed through declaration lookup. -/
theorem globalName_reserved (rename : String → String) (name : String)
    (h : reserved.contains name = true) : globalName E rename name = name := by
  have hn : lookup? E name = none := by
    unfold lookup?
    rw [h]
    simp only [Bool.not_true, Bool.and_false]
    rfl
  simp only [globalName, hn]

/-- Admitted related lexical scopes cannot block builtin application heads. -/
theorem syntaxLocal_reserved_absent (f : E.signature ⟶ F.signature)
    {locals : Locals E} {syntaxLocals : SyntaxLocals} (hlegal : LegalLocals locals)
    (hrelated : LocalsRelated f locals syntaxLocals) (name : String)
    (h : reserved.contains name = true) : syntaxLocal? syntaxLocals name = none :=
  localsRelated_absent f hrelated name (legalLocals_reserved_absent hlegal name h)

/-- Outside the let branch, normalization sequences exactly the argument list. -/
theorem normalizeApplication_eq (rename : String → String) (fuel : Nat)
    (syntaxLocals : SyntaxLocals) (name : String) (es : List Expr)
    (hlet : name ≠ "let") (hlocal : syntaxLocal? syntaxLocals name = none) :
    normalizeFuel? E rename (fuel + 1) syntaxLocals (.list (.atom name :: es)) =
      (es.mapM (normalizeFuel? E rename fuel syntaxLocals)).map
        (fun outputs => .list (.atom (globalName E rename name) :: outputs)) := by
  cases hargs : es.mapM (normalizeFuel? E rename fuel syntaxLocals) <;>
    unfold normalizeFuel? <;> split <;> simp_all

/-- Nullary UF applications do not inspect the supplied recursive decoder. -/
theorem applyUF_empty_recur (source target : Expr → Option (PackedTerm E)) (name : String) :
    applyUF? E source name [] = applyUF? E target name [] := by
  have hargs : ∀ inputs, decodeArguments? source inputs [] = decodeArguments? target inputs [] := by
    intro inputs
    cases inputs <;> rfl
  unfold applyUF?
  cases hi : lookup? E name with
  | none => rfl
  | some i =>
      change (decodeArguments? source (E.declarations.get i).inputs []).bind _ =
        (decodeArguments? target (E.declarations.get i).inputs []).bind _
      rw [hargs]

/-- Successful folded elaboration requires at least two raw operands. -/
theorem fold_length (source : Expr → Option (PackedTerm E))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (value : PackedTerm E) (h : fold? source op es = some value) :
    2 ≤ es.length := by
  cases es with
  | nil => simp [fold?] at h
  | cons a es =>
      cases es with
      | nil => simp [fold?] at h
      | cons b rest => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))

/-- The binary-or-longer subtraction branch cannot be mistaken for unary minus. -/
theorem decodeSubtract_fold (fuel : Nat) (es : List Expr) (hlength : 2 ≤ es.length) :
    decodeScopedFuel? E (fuel + 1) [] (.list (.atom "-" :: es)) =
      fold? (decodeScopedFuel? E fuel []) .sub es := by
  cases es with
  | nil => contradiction
  | cons a es =>
      cases es with
      | nil => contradiction
      | cons b rest => rfl

/-- The non-Boolean atom branch retains lexical lookup before numeral and UF
elaboration. The two builtin Boolean atoms have priority over arbitrary locals. -/
theorem decodeAtom_eq (fuel : Nat) (locals : Locals E) (name : String)
    (htrue : name ≠ "true") (hfalse : name ≠ "false") :
    decodeScopedFuel? E (fuel + 1) locals (.atom name) =
      match local? locals name with
      | some value => some value
      | none => match numeral? (.atom name) with
        | some n => some ⟨.int, Uflia.Term.integer n⟩
        | none => applyUF? E (decodeScopedFuel? E fuel locals) name [] := by
  unfold decodeScopedFuel?
  split <;> simp_all
  rfl

/-- Non-Boolean atom normalization preserves successful numeral syntax explicitly. -/
theorem normalizeAtom_eq (rename : String → String) (fuel : Nat)
    (syntaxLocals : SyntaxLocals) (name : String)
    (htrue : name ≠ "true") (hfalse : name ≠ "false") :
    normalizeFuel? E rename (fuel + 1) syntaxLocals (.atom name) =
      match syntaxLocal? syntaxLocals name with
      | some output => some output
      | none => match numeral? (.atom name) with
        | some _ => some (.atom name)
        | none => some (.atom (globalName E rename name)) := by
  unfold normalizeFuel?
  split <;> simp_all
  rfl

/-- Builtin application assembly retains the literal head and sequences the
actual normalized child list; legal lexical scopes cannot block the head. -/
theorem normalizeBuiltinApplication_success (f : NameMap E F) (fuel : Nat)
    {locals : Locals E} {syntaxLocals : SyntaxLocals} (hlegal : LegalLocals locals)
    (hrelated : LocalsRelated f.abstract locals syntaxLocals)
    (name : String) (hreserved : reserved.contains name = true) (hlet : name ≠ "let")
    (es outputs : List Expr)
    (hn : es.mapM (normalizeFuel? E f.rename fuel syntaxLocals) = some outputs) :
    normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.list (.atom name :: es)) =
      some (.list (.atom name :: outputs)) := by
  rw [normalizeApplication_eq f.rename fuel syntaxLocals name es hlet
    (syntaxLocal_reserved_absent f.abstract hlegal hrelated name hreserved)]
  rw [globalName_reserved f.rename name hreserved, hn]
  rfl

/-- The scoped induction hypothesis only concerns successful source decodings.
Each target witness is decoded at its own expanded syntax-node budget. -/
def NormalizesAt (f : NameMap E F) (fuel : Nat) (locals : Locals E)
    (syntaxLocals : SyntaxLocals) : Prop :=
  ∀ e value, decodeScopedFuel? E fuel locals e = some value → ∃ output,
    normalizeFuel? E f.rename fuel syntaxLocals e = some output ∧
    decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)

/-- Normalize dependent UF arguments at their combined expanded syntax budget. -/
theorem normalizeArguments_transport (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (inputs : List (SortCode String)) :
    ∀ (es : List Expr) (ts : (i : Fin inputs.length) →
      Uflia.Term E.signature (inputs.get i)),
      decodeArguments? source inputs es = some ts →
      ∃ outputs, es.mapM normalize = some outputs ∧
        decodeArguments? (decodeTermFuel? F (expressionsFuel outputs)) inputs outputs =
          some (fun i => Uflia.Term.map f (ts i)) := by
  induction inputs with
  | nil =>
      show ∀ es ts, decodeArguments? source [] es = some ts →
        ∃ outputs, es.mapM normalize = some outputs ∧
          decodeArguments? (decodeTermFuel? F (expressionsFuel outputs)) [] outputs =
            some (fun i => Uflia.Term.map f (ts i))
      intro es ts h
      cases es with
      | nil =>
          refine ⟨[], rfl, ?_⟩
          simp only [decodeArguments?, Option.some.injEq]
          funext i
          exact Fin.elim0 i
      | cons e es => simp [decodeArguments?] at h
  | cons input inputs ih =>
      show ∀ es ts, decodeArguments? source (input :: inputs) es = some ts →
        ∃ outputs, es.mapM normalize = some outputs ∧
          decodeArguments? (decodeTermFuel? F (expressionsFuel outputs)) (input :: inputs) outputs =
            some (fun i => Uflia.Term.map f (ts i))
      intro es ts h
      cases es with
      | nil => simp [decodeArguments?] at h
      | cons e es =>
          show ∃ outputs, (e :: es).mapM normalize = some outputs ∧
            decodeArguments? (decodeTermFuel? F (expressionsFuel outputs)) (input :: inputs) outputs =
              some (fun i => Uflia.Term.map f (ts i))
          have hshape : ∃ value, source e = some value ∧
              ∃ term, value.expect? input = some term ∧
              ∃ tail, decodeArguments? source inputs es = some tail ∧ Fin.cases term tail = ts := by
            simpa [decodeArguments?, Option.bind_eq_some_iff] using h
          obtain ⟨value, hv, term, ht, tail, htail, rfl⟩ := hshape
          obtain ⟨output, ho, hd⟩ : ∃ output, normalize e = some output ∧
              decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value) := hchildren e value hv
          obtain ⟨outputs, hos, hds⟩ : ∃ outputs, es.mapM normalize = some outputs ∧
              decodeArguments? (decodeTermFuel? F (expressionsFuel outputs)) inputs outputs =
                some (fun i => Uflia.Term.map f (tail i)) := ih es tail htail
          have hhead : decodeTermFuel? F (expressionsFuel (output :: outputs)) output =
              some (mapPacked f value) :=
            decodeTermFuel_mono (Nat.le_add_right _ _) output _ hd
          have htail' : decodeArguments? (decodeTermFuel? F (expressionsFuel (output :: outputs)))
              inputs outputs = some (fun i => Uflia.Term.map f (tail i)) := decodeArguments_refines
            (fun e t h => decodeTermFuel_mono (Nat.le_add_left
              (expressionsFuel outputs) (expressionFuel output)) e t h)
            inputs outputs (fun i => Uflia.Term.map f (tail i)) hds
          refine ⟨output :: outputs, by simp [ho, hos], ?_⟩
          simp only [decodeArguments?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
          refine ⟨mapPacked f value, hhead, Uflia.Term.map f term, ?_,
            (fun i => Uflia.Term.map f (tail i)), htail', ?_⟩
          · simp only [expect_mapPacked, ht, Option.map_some]
          · funext i
            exact Fin.cases rfl (fun _ => rfl) i

/-- Every successfully decoded atom normalizes with its mapped typed value,
including lexical substitution, literals and actual nullary UF declarations. -/
theorem normalizeAtom_success (f : NameMap E F) (fuel : Nat)
    (locals : Locals E) (syntaxLocals : SyntaxLocals)
    (hrelated : LocalsRelated f.abstract locals syntaxLocals)
    (name : String) (value : PackedTerm E)
    (h : decodeScopedFuel? E (fuel + 1) locals (.atom name) = some value) :
    ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  by_cases htrue : name = "true"
  · show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
    subst name
    have hv : (⟨.bool, Uflia.Term.boolean true⟩ : PackedTerm E) = value := Option.some.inj h
    cases hv
    refine ⟨.atom "true", rfl, ?_⟩
    change some (⟨.bool, Uflia.Term.boolean true⟩ : PackedTerm F) =
      some ⟨.bool, Uflia.Term.map f.abstract (Uflia.Term.boolean true)⟩
    congr 2
    exact (map_nullary f.abstract (.boolean true)).symm
  · show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
    by_cases hfalse : name = "false"
    · show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
        decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
      subst name
      have hv : (⟨.bool, Uflia.Term.boolean false⟩ : PackedTerm E) = value := Option.some.inj h
      cases hv
      refine ⟨.atom "false", rfl, ?_⟩
      change some (⟨.bool, Uflia.Term.boolean false⟩ : PackedTerm F) =
        some ⟨.bool, Uflia.Term.map f.abstract (Uflia.Term.boolean false)⟩
      congr 2
      exact (map_nullary f.abstract (.boolean false)).symm
    · show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
        decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
      rw [decodeAtom_eq fuel locals name htrue hfalse] at h
      cases hl : local? locals name with
      | some term =>
          show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
            decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
          simp only [hl] at h
          have hv : term = value := Option.some.inj h
          cases hv
          have hr : match (some value : Option (PackedTerm E)), syntaxLocal? syntaxLocals name with
              | none, none => True
              | some value, some output =>
                  decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
              | _, _ => False := by
            cases hsyntax : syntaxLocal? syntaxLocals name <;>
              simpa only [hl, hsyntax] using localsRelated_lookup f.abstract hrelated name
          cases hs : syntaxLocal? syntaxLocals name with
          | none => simp only [hs] at hr
          | some output =>
              refine ⟨output, ?_, ?_⟩
              · rw [normalizeAtom_eq f.rename fuel syntaxLocals name htrue hfalse, hs]
              · simpa only [hs] using hr
      | none =>
          show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
            decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
          have hs : syntaxLocal? syntaxLocals name = none := localsRelated_absent f.abstract hrelated name hl
          simp only [hl] at h
          cases hn : numeral? (.atom name) with
          | some n =>
              show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
                decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
              simp only [hn] at h
              have hv : (⟨.int, Uflia.Term.integer n⟩ : PackedTerm E) = value := Option.some.inj h
              cases hv
              refine ⟨.atom name, ?_, ?_⟩
              · rw [normalizeAtom_eq f.rename fuel syntaxLocals name htrue hfalse, hs, hn]
              · change decodeScopedFuel? F (0 + 1) [] (.atom name) = _
                rw [decodeAtom_eq 0 [] name htrue hfalse]
                simp only [local?, hn]
                change some (⟨.int, Uflia.Term.integer n⟩ : PackedTerm F) =
                  some ⟨.int, Uflia.Term.map f.abstract (Uflia.Term.integer n)⟩
                congr 2
                exact (map_nullary f.abstract (.integer n)).symm
          | none =>
              show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
                decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
              simp only [hn] at h
              cases hi : lookup? E name with
              | none => simp [applyUF?, hi] at h
              | some i =>
                  show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
                    decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
                  have ht : lookup? F (globalName E f.rename name) =
                      some (symbolIndex (f.abstract.operations (.declared i))) := lookup_globalName f name i hi
                  have hr : reserved.contains (globalName E f.rename name) = false := (lookup_lexical ht).2
                  have hnum : numeral? (.atom (globalName E f.rename name)) = none := lookup_not_numeral ht
                  have hm : applyUF? F
                      (fun e => (decodeScopedFuel? E fuel locals e).map (mapPacked f.abstract))
                      (globalName E f.rename name) [] = some (mapPacked f.abstract value) := applyUF_transport f
                    (mappedSource_success f.abstract (decodeScopedFuel? E fuel locals)) name [] value h
                  refine ⟨.atom (globalName E f.rename name), ?_, ?_⟩
                  · rw [normalizeAtom_eq f.rename fuel syntaxLocals name htrue hfalse, hs, hn]
                  · change decodeScopedFuel? F (0 + 1) [] (.atom (globalName E f.rename name)) = _
                    rw [decodeAtomUF 0 _ hr hnum]
                    exact (applyUF_empty_recur (decodeScopedFuel? F 0 [])
                      (fun e => (decodeScopedFuel? E fuel locals e).map (mapPacked f.abstract)) _).trans hm

/-- A genuine UF application normalizes its argument syntax and reconstructs
the actual target declaration at the expanded parent budget. -/
theorem normalizeUFApplication_success (f : NameMap E F) (fuel : Nat)
    (locals : Locals E) (syntaxLocals : SyntaxLocals)
    (hrelated : LocalsRelated f.abstract locals syntaxLocals)
    (hchildren : NormalizesAt f fuel locals syntaxLocals)
    (name : String) (args : List Expr) (hlocal : local? locals name = none) (hne : args ≠ [])
    (value : PackedTerm E)
    (h : applyUF? E (decodeScopedFuel? E fuel locals) name args = some value) :
    ∃ output,
      normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.list (.atom name :: args)) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  cases hi : lookup? E name with
  | none => simp [applyUF?, hi] at h
  | some i =>
      show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals
          (.list (.atom name :: args)) = some output ∧
        decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
      have hreserved : reserved.contains name = false := (lookup_lexical hi).2
      have hlet : name ≠ "let" := by
        intro heq
        subst name
        simp [reserved] at hreserved
      have hsyntax : syntaxLocal? syntaxLocals name = none := localsRelated_absent f.abstract hrelated name hlocal
      simp only [applyUF?, hi] at h
      change (decodeArguments? (decodeScopedFuel? E fuel locals) (E.declarations.get i).inputs args).bind _ =
        some value at h
      obtain ⟨ts, hs, hvalue⟩ := Option.bind_eq_some_iff.mp h
      have hv : (⟨(E.declarations.get i).output, .app (.uf (.declared i)) ts⟩ : PackedTerm E) = value :=
        Option.some.inj hvalue
      cases hv
      obtain ⟨outputs, hn, hd⟩ := normalizeArguments_transport f.abstract
        (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals)
        hchildren (E.declarations.get i).inputs args ts hs
      have houtne : outputs ≠ [] := by
        intro hempty
        have hlen : args.length = outputs.length := forall₂_length (List.mapM_eq_some_iff_forall₂.mp hn)
        rw [hempty, List.length_nil] at hlen
        exact hne (List.eq_nil_of_length_eq_zero hlen)
      have ht : lookup? F (globalName E f.rename name) =
          some (symbolIndex (f.abstract.operations (.declared i))) := lookup_globalName f name i hi
      have htargetReserved : reserved.contains (globalName E f.rename name) = false := (lookup_lexical ht).2
      have hargs : decodeArguments? (decodeTermFuel? F (1 + expressionsFuel outputs))
          (E.declarations.get i).inputs outputs = some (fun j => Uflia.Term.map f.abstract (ts j)) :=
        decodeArguments_refines
        (fun e t decoded => decodeTermFuel_mono
          (Nat.le_add_left (expressionsFuel outputs) 1) e t decoded)
        (E.declarations.get i).inputs outputs (fun j => Uflia.Term.map f.abstract (ts j)) hd
      refine ⟨.list (.atom (globalName E f.rename name) :: outputs), ?_, ?_⟩
      · rw [normalizeApplication_eq f.rename fuel syntaxLocals name args hlet hsyntax, hn]
        rfl
      · change decodeScopedFuel? F ((1 + expressionsFuel outputs) + 1) []
          (.list (.atom (globalName E f.rename name) :: outputs)) = _
        rw [decodeApplicationUF _ _ outputs htargetReserved houtne]
        rw [← applyProfile_lookup _ _ (f.abstract.operations (.declared i))
          (decodeScopedFuel? F (1 + expressionsFuel outputs) []) outputs
          (globalName E f.rename name) ht]
        unfold applyProfile?
        change (decodeArguments? (decodeTermFuel? F (1 + expressionsFuel outputs))
          (E.declarations.get i).inputs outputs).bind _ = _
        rw [hargs]
        rfl

/-- The full parallel-let branch follows from the old-scope induction hypothesis
for all right-hand sides and the extended-scope hypothesis for the body. The
eliminated binding layer consumes no extra target fuel. -/
theorem normalizeLet_success (f : NameMap E F) (fuel : Nat)
    (hchildren : ∀ locals syntaxLocals, LegalLocals locals →
      LocalsRelated f.abstract locals syntaxLocals → NormalizesAt f fuel locals syntaxLocals)
    (locals : Locals E) (syntaxLocals : SyntaxLocals) (hlegal : LegalLocals locals)
    (hrelated : LocalsRelated f.abstract locals syntaxLocals)
    (head : Expr) (tail : List Expr) (body : Expr) (values : Locals E)
    (hbindings : letBindings? (decodeScopedFuel? E fuel locals) (head :: tail) = some values)
    (value : PackedTerm E)
    (hbody : decodeScopedFuel? E fuel (values ++ locals) body = some value) :
    ∃ output,
      normalizeFuel? E f.rename (fuel + 1) syntaxLocals
        (.list [.atom "let", .list (head :: tail), body]) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  obtain ⟨bindings, hn, hr⟩ := normalizeLetBindings_transport f.abstract
    (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals)
    (hchildren locals syntaxLocals hlegal hrelated) (head :: tail) values hbindings
  obtain ⟨output, ho, hd⟩ := hchildren (values ++ locals) (bindings ++ syntaxLocals)
    (legalLocals_append (letBindings_legal _ _ _ hbindings) hlegal)
    (localsRelated_append f.abstract hr hrelated) body value hbody
  refine ⟨output, ?_, hd⟩
  change (syntaxBindings? (normalizeFuel? E f.rename fuel syntaxLocals) (head :: tail)).bind _ =
    some output
  rw [hn]
  exact ho

/-- A successful guarded UF branch supplies its nonempty-argument and absent
local-head premises; no decoder rejection reflection is used. -/
theorem normalizeUFApplication_guard_success (f : NameMap E F) (fuel : Nat)
    (locals : Locals E) (syntaxLocals : SyntaxLocals)
    (hrelated : LocalsRelated f.abstract locals syntaxLocals)
    (hchildren : NormalizesAt f fuel locals syntaxLocals)
    (name : String) (args : List Expr) (value : PackedTerm E)
    (h : (if args.isEmpty || reserved.contains name || (local? locals name).isSome then none
      else applyUF? E (decodeScopedFuel? E fuel locals) name args) = some value) :
    ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals
      (.list (.atom name :: args)) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  split at h
  · contradiction
  · rename_i guard
    have hne : args ≠ [] := by
      intro heq
      subst args
      simp at guard
    have hlocal : local? locals name = none := by
      cases hl : local? locals name with
      | none => rfl
      | some term => simp [hl] at guard
    exact normalizeUFApplication_success f fuel locals syntaxLocals hrelated hchildren name args hlocal hne value h

/-- The successful decoder let branch exposes exactly the checked bindings and
body hypotheses consumed by the scoped normalization induction. -/
theorem normalizeLet_decoded_success (f : NameMap E F) (fuel : Nat)
    (hchildren : ∀ locals syntaxLocals, LegalLocals locals →
      LocalsRelated f.abstract locals syntaxLocals → NormalizesAt f fuel locals syntaxLocals)
    (locals : Locals E) (syntaxLocals : SyntaxLocals) (hlegal : LegalLocals locals)
    (hrelated : LocalsRelated f.abstract locals syntaxLocals)
    (head : Expr) (tail : List Expr) (body : Expr) (value : PackedTerm E)
    (h : (letBindings? (decodeScopedFuel? E fuel locals) (head :: tail)).bind
      (fun values => decodeScopedFuel? E fuel (values ++ locals) body) = some value) :
    ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals
      (.list [.atom "let", .list (head :: tail), body]) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  obtain ⟨values, hbindings, hbody⟩ := Option.bind_eq_some_iff.mp h
  exact normalizeLet_success f fuel hchildren locals syntaxLocals hlegal hrelated
    head tail body values hbindings value hbody

/-- Full successful-source scoped decoder commutation for lexical let
normalization and coherent, possibly noninjective declaration name maps. -/
theorem normalizeScopedFuel_success (f : NameMap E F) (fuel : Nat) :
    ∀ locals syntaxLocals, LegalLocals locals → LocalsRelated f.abstract locals syntaxLocals →
      NormalizesAt f fuel locals syntaxLocals := by
  induction fuel with
  | zero =>
      intro locals syntaxLocals hlegal hrelated e value h
      cases h
  | succ fuel ih =>
      show ∀ locals syntaxLocals, LegalLocals locals → LocalsRelated f.abstract locals syntaxLocals →
        NormalizesAt f (fuel + 1) locals syntaxLocals
      intro locals syntaxLocals hlegal hrelated e value h
      cases e with
      | atom name => exact normalizeAtom_success f fuel locals syntaxLocals hrelated name value h
      | list es =>
          show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.list es) = some output ∧
            decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
          unfold decodeScopedFuel? at h
          split at h <;> simp_all only [Silmaril.Logic.Smt.SE.list.injEq, reduceCtorEq]
          all_goals subst es
          · exact normalizeLet_decoded_success f fuel ih locals syntaxLocals hlegal hrelated _ _ _ value h
          ·
            obtain ⟨a', hn, hd⟩ := normalizeUnary_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .not _ value h
            refine ⟨.list [.atom "not", a'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "not" (by decide) (by decide) [_] [a'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨a', hn, hd⟩ := normalizeUnary_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) (.scale (-1)) _ value h
            refine ⟨.list [.atom "-", a'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "-" (by decide) (by decide) [_] [a'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .and _ value h
            refine ⟨.list (.atom "and" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "and" (by decide) (by decide) _ outputs hn, ?_⟩
            change fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) .and outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .or _ value h
            refine ⟨.list (.atom "or" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "or" (by decide) (by decide) _ outputs hn, ?_⟩
            change fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) .or outputs = _
            exact hd
          ·
            obtain ⟨a', b', hn, hd⟩ := normalizeImplication_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) _ _ value h
            refine ⟨.list [.atom "=>", a', b'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "=>" (by decide) (by decide) [_, _] [a', b'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨a', b', hn, hd⟩ := normalizeXor_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) _ _ value h
            refine ⟨.list [.atom "xor", a', b'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "xor" (by decide) (by decide) [_, _] [a', b'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .add _ value h
            refine ⟨.list (.atom "+" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "+" (by decide) (by decide) _ outputs hn, ?_⟩
            change fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) .add outputs = _
            exact hd
          · show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals _ = some output ∧
              decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .sub _ value h
            refine ⟨.list (.atom "-" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "-" (by decide) (by decide) _ outputs hn, ?_⟩
            have hl : 2 ≤ List.length _ := fold_length (decodeScopedFuel? E fuel locals) .sub _ value h
            have hlen : List.length _ = outputs.length := forall₂_length (List.mapM_eq_some_iff_forall₂.mp hn)
            have hout : 2 ≤ outputs.length := by rw [← hlen]; exact hl
            change decodeScopedFuel? F ((1 + expressionsFuel outputs) + 1) []
              (.list (.atom "-" :: outputs)) = _
            rw [decodeSubtract_fold _ outputs hout]
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .le false _ value h
            refine ⟨.list (.atom "<=" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "<=" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .le false outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .lt false _ value h
            refine ⟨.list (.atom "<" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "<" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .lt false outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .le true _ value h
            refine ⟨.list (.atom ">=" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              ">=" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .le true outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .lt true _ value h
            refine ⟨.list (.atom ">" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              ">" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .lt true outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeEqualities_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) false _ value h
            refine ⟨.list (.atom "=" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "=" (by decide) (by decide) _ outputs hn, ?_⟩
            change equalities? (decodeTermFuel? F (1 + expressionsFuel outputs)) false outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeEqualities_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) true _ value h
            refine ⟨.list (.atom "distinct" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "distinct" (by decide) (by decide) _ outputs hn, ?_⟩
            change equalities? (decodeTermFuel? F (1 + expressionsFuel outputs)) true outputs = _
            exact hd
          ·
            obtain ⟨c', a', b', hn, hd⟩ := normalizeIte_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) _ _ _ value h
            refine ⟨.list [.atom "ite", c', a', b'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "ite" (by decide) (by decide) [_, _, _] [c', a', b'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeMultiply_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) _ value h
            refine ⟨.list (.atom "*" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "*" (by decide) (by decide) _ outputs hn, ?_⟩
            change multiply? (decodeTermFuel? F (1 + expressionsFuel outputs)) outputs = _
            exact hd
          · exact normalizeUFApplication_guard_success f fuel locals syntaxLocals hrelated (ih locals syntaxLocals hlegal hrelated) _ _ value h

/-- Successful default closed term decoding commutes with executable full-let
normalization and arbitrary coherent declaration symbol maps. -/
theorem normalizeTerm_success (f : NameMap E F) (e : Expr) (value : PackedTerm E)
    (h : decodeTerm? E e = some value) :
    ∃ output, normalize? E f.rename e = some output ∧
      decodeTerm? F output = some (mapPacked f.abstract value) := by
  have hlegal : LegalLocals ([] : Locals E) := by
    intro entry hmem
    contradiction
  exact normalizeScopedFuel_success f (expressionFuel e) [] [] hlegal .nil e value h

/-- Successful assertion decoding commutes with the actual source syntax
normalizer. The target is decoded with its own possibly expanded node budget. -/
theorem normalizeFormula_success (f : NameMap E F) (e : Expr) (formula : Formula E.signature)
    (h : decodeFormula? E e = some formula) :
    ∃ output, normalize? E f.rename e = some output ∧
      decodeFormula? F output = some (Uflia.Term.map f.abstract formula) := by
  change (decodeTerm? E e).bind (fun value => value.expect? .bool) = some formula at h
  obtain ⟨value, hv, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨output, hn, hd⟩ := normalizeTerm_success f e value hv
  refine ⟨output, hn, ?_⟩
  change (decodeTerm? F output).bind (fun value => value.expect? .bool) = _
  rw [hd]
  change (mapPacked f.abstract value).expect? .bool = _
  rw [expect_mapPacked, ht]
  rfl

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
