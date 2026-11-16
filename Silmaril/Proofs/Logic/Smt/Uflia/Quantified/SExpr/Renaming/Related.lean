module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Names

/-! Open-context port of the successful child-syntax correspondence helpers in
Uflia/SExprRenamingScoped at pinned base a29074a6e8f0. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open Silmaril.Logic.Smt.Uflia.SExpr
variable {E : Environment} {k : Nat} {Γ : Fin k → SortCode String}

/-- A syntax correspondence preserves successful recursive results while
allowing the argument expression itself to change. -/
def DecodeRelated (source target : Expr → Option (PackedTerm E Γ)) (a b : Expr) : Prop :=
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
theorem typedTerms_related {source target : Expr → Option (PackedTerm E Γ)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (sort : SortCode String) (values : List (Quantified.Term E.signature Γ sort))
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
theorem unary_related {source target : Expr → Option (PackedTerm E Γ)}
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e e' : Expr)
    (hE: DecodeRelated source target e e')
    (value : PackedTerm E Γ) (h : unary? source op e = some value) :
    unary? target op e' = some value := by
  cases he : source e with
  | none => simp [unary?, he] at h
  | some ve =>
      simpa only [unary?, he, hE ve he, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem binary_related {source target : Expr → Option (PackedTerm E Γ)}
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a a' : Expr) (b b' : Expr)
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E Γ) (h : binary? source op a b = some value) :
    binary? target op a' b' = some value := by
  cases ha : source a with
  | none => simp [binary?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [binary?, ha, hb] at h
      | some vb =>
          simpa only [binary?, ha, hb, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem implication_related {source target : Expr → Option (PackedTerm E Γ)}
    (a a' : Expr) (b b' : Expr)
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E Γ) (h : implication? source a b = some value) :
    implication? target a' b' = some value := by
  cases ha : source a with
  | none => simp [implication?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [implication?, ha, hb] at h
      | some vb =>
          simpa only [implication?, ha, hb, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem xor_related {source target : Expr → Option (PackedTerm E Γ)}
    (a a' : Expr) (b b' : Expr)
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E Γ) (h : xor? source a b = some value) :
    xor? target a' b' = some value := by
  cases ha : source a with
  | none => simp [xor?, ha] at h
  | some va =>
      cases hb : source b with
      | none => simp [xor?, ha, hb] at h
      | some vb =>
          simpa only [xor?, ha, hb, hA va ha, hB vb hb, Option.bind_some] using h

/-- Corresponding successful child syntax preserves typed elaboration. -/
theorem ite_related {source target : Expr → Option (PackedTerm E Γ)}
    (c c' : Expr) (a a' : Expr) (b b' : Expr)
    (hC: DecodeRelated source target c c')
    (hA: DecodeRelated source target a a')
    (hB: DecodeRelated source target b b')
    (value : PackedTerm E Γ) (h : ite? source c a b = some value) :
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
theorem fold_related {source target : Expr → Option (PackedTerm E Γ)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (value : PackedTerm E Γ) (h : fold? source op xs = some value) :
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
theorem compare_related {source target : Expr → Option (PackedTerm E Γ)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (value : PackedTerm E Γ) (h : compare? source op reverse xs = some value) :
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
theorem equalities_related {source target : Expr → Option (PackedTerm E Γ)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (distinct : Bool) (value : PackedTerm E Γ)
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
theorem multiply_related {source target : Expr → Option (PackedTerm E Γ)}
    {xs ys : List Expr} (hrelated : List.Forall₂ (DecodeRelated source target) xs ys)
    (value : PackedTerm E Γ) (h : multiply? source xs = some value) :
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

/-- Successful sort checking entails successful decoding of every raw child. -/
theorem typedTerms_source_exists (source : Expr → Option (PackedTerm E Γ))
    (sort : SortCode String) (es : List Expr)
    (ts : List (Quantified.Term E.signature Γ sort)) (h : typedTerms? source sort es = some ts) :
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

/-- Successful folding decodes every child before constructing its result. -/
theorem fold_source_exists (source : Expr → Option (PackedTerm E Γ))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (value : PackedTerm E Γ) (h : fold? source op es = some value) :
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
theorem compare_source_exists (source : Expr → Option (PackedTerm E Γ))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (es : List Expr) (value : PackedTerm E Γ) (h : compare? source op reverse es = some value) :
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
theorem equalities_source_exists (source : Expr → Option (PackedTerm E Γ))
    (distinct : Bool) (es : List Expr) (value : PackedTerm E Γ)
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
theorem multiply_source_exists (source : Expr → Option (PackedTerm E Γ))
    (es : List Expr) (value : PackedTerm E Γ) (h : multiply? source es = some value) :
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
theorem unary_source_exists (source : Expr → Option (PackedTerm E Γ))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e : Expr) (value : PackedTerm E Γ)
    (h : unary? source op e = some value) :
    ∃ values, [e].mapM source = some values := by
  cases he : source e with
  | none => simp [unary?, he] at h
  | some ve =>
      exact ⟨[ve], by simp [he]⟩

/-- A successful fixed-arity operator decodes every one of its children. -/
theorem binary_source_exists (source : Expr → Option (PackedTerm E Γ))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a : Expr) (b : Expr) (value : PackedTerm E Γ)
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
theorem implication_source_exists (source : Expr → Option (PackedTerm E Γ))
    (a : Expr) (b : Expr) (value : PackedTerm E Γ)
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
theorem xor_source_exists (source : Expr → Option (PackedTerm E Γ))
    (a : Expr) (b : Expr) (value : PackedTerm E Γ)
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
theorem ite_source_exists (source : Expr → Option (PackedTerm E Γ))
    (c : Expr) (a : Expr) (b : Expr) (value : PackedTerm E Γ)
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


end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
