module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Variables.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Normalization.Thms
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
open Uflia.SExpr (Environment Expr Symbol lookup?)
open Uflia.Quantified.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}
variable {f : environmentSignature E ⟶ environmentSignature F}

theorem adjacent_transport {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (r : α → α → γ) (q : β → β → δ)
    (hr : ∀ a b, g (r a b) = q (f a) (f b)) (xs : List α) :
    (adjacent r xs).map g = adjacent q (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b xs =>
          simp only [adjacent, List.map_cons, hr] at ih ⊢
          exact congrArg (List.cons (q (f a) (f b))) ih

/-- Mapping all pairs preserves the decoder's distinctness expansion. -/
theorem allPairs_transport {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (r : α → α → γ) (q : β → β → δ)
    (hr : ∀ a b, g (r a b) = q (f a) (f b)) (xs : List α) :
    (allPairs r xs).map g = allPairs q (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [allPairs, List.map_cons, List.map_append, List.map_map, ih]
      congr 1
      apply List.map_congr_left
      intro b hb
      exact hr a b

def iteProfile (s : SortCode String) : Fin 3 → SortCode String :=
  Fin.cases .bool (fun _ => s)

/-- Transport a term whose mapped sort has a chosen concrete presentation. -/
def termAt (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (v : Uflia.Quantified.Term E.signature Γ s) :
    Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) t := cast (congrArg (Uflia.Quantified.Term F.signature (f.sorts ∘ Γ)) h) (Hom.quantifiedTerm f v)

theorem termAt_heq (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (v : Uflia.Quantified.Term E.signature Γ s) :
    HEq (termAt f h v) (Hom.quantifiedTerm f v) := cast_heq _ _

private theorem packed_cast {s t : SortCode String} (h : s = t)
    (v : Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) s) :
    (⟨s,v⟩ : PackedTerm F (f.sorts ∘ Γ)) = ⟨t,cast (congrArg (Uflia.Quantified.Term F.signature (f.sorts ∘ Γ)) h) v⟩ := by
  cases h
  rfl

theorem mapPacked_at (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (v : Uflia.Quantified.Term E.signature Γ s) :
    mapPacked f ⟨s,v⟩ = ⟨t,termAt f h v⟩ := packed_cast h _

private theorem app_heq {n : Nat} {ss tt : Fin n → SortCode String}
    {s t : SortCode String} (hs : ss = tt) (ht : s = t)
    (op : Operation F.signature n ss s) (op' : Operation F.signature n tt t)
    (hop : HEq op op') (args : ∀ i, Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) (ss i))
    (args' : ∀ i, Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) (tt i))
    (ha : ∀ i, HEq (args i) (args' i)) :
    HEq (Uflia.Quantified.Term.app op args) (Uflia.Quantified.Term.app op' args') := by
  cases hs
  cases ht
  cases eq_of_heq hop
  exact heq_of_eq (congrArg (Uflia.Quantified.Term.app op) (funext (fun i => eq_of_heq (ha i))))

theorem termAt_app (f : environmentSignature E ⟶ environmentSignature F)
    {n : Nat} {ss tt : Fin n → SortCode String} {s t : SortCode String}
    (hs : ∀ i, f.sorts (ss i) = tt i) (ht : f.sorts s = t)
    (op : Operation E.signature n ss s) (op' : Operation F.signature n tt t)
    (hop : HEq (Hom.operation f op) op')
    (args : ∀ i, Uflia.Quantified.Term E.signature Γ (ss i)) :
    termAt f ht (.app op args) = .app op' (fun i => termAt f (hs i) (args i)) := by
  apply eq_of_heq
  apply (termAt_heq f ht _).trans
  rw [quantifiedTerm_app]
  exact app_heq (funext hs) ht _ _ hop _ _ (fun i => (termAt_heq f (hs i) _).symm)

theorem typedTerms_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (sort : SortCode String) (es : List Expr) (ts : List (Uflia.Quantified.Term E.signature Γ sort))
    (h : typedTerms? source sort es = some ts) :
    typedTerms? target (f.sorts sort) es = some (ts.map (Hom.quantifiedTerm f)) := by
  unfold Uflia.Quantified.SExpr.typedTerms? at h ⊢
  rw [List.mapM_eq_some_iff_forall₂] at h ⊢
  induction h with
  | nil => exact .nil
  | @cons e t es ts head tail ih =>
      apply List.Forall₂.cons ?_ ih
      obtain ⟨v,hv,ht⟩ := Option.bind_eq_some_iff.mp head
      change (target e).bind _ = some (Hom.quantifiedTerm f t)
      rw [hfg e v hv]
      exact expect_mapPacked_of_eq f v t ht

theorem typedTerms_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {s t : SortCode String} (hs : f.sorts s = t)
    (es : List Expr) (ts : List (Uflia.Quantified.Term E.signature Γ s))
    (h : typedTerms? source s es = some ts) :
    typedTerms? target t es = some (ts.map (termAt f hs)) := by
  cases hs
  exact typedTerms_transport f hfg s es ts h

theorem unary_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e : Expr) (t : PackedTerm E Γ) (h : unary? source op e = some t) :
    unary? target (Hom.operation f op) e = some (mapPacked f t) := by
  obtain ⟨v,hv,a,ha,rfl⟩ : ∃ v, source e = some v ∧ ∃ a,
      v.expect? input = some a ∧ (⟨output,.app op (fun _ => a)⟩ : PackedTerm E Γ) = t := by
    simpa [unary?, Option.bind_eq_some_iff] using h
  simp only [unary?, bind, pure, hfg e v hv, Option.bind_some,
    expect_mapPacked_of_eq f v a ha]
  change some (⟨_,_⟩ : PackedTerm F (f.sorts ∘ Γ)) = some (⟨_,_⟩ : PackedTerm F (f.sorts ∘ Γ))
  rw [quantifiedTerm_app]

theorem binary_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a b : Expr) (t : PackedTerm E Γ) (h : binary? source op a b = some t) :
    binary? target (Hom.operation f op) a b = some (mapPacked f t) := by
  obtain ⟨va,hva,ta,hta,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ ta, va.expect? input = some ta ∧
      ∃ vb, source b = some vb ∧ ∃ tb, vb.expect? input = some tb ∧
        (⟨output,.app op (Fin.cases ta (fun _ => tb))⟩ : PackedTerm E Γ) = t := by
    simpa [binary?, Option.bind_eq_some_iff] using h
  simp only [binary?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_mapPacked_of_eq f va ta hta, expect_mapPacked_of_eq f vb tb htb]
  change some (⟨_,_⟩ : PackedTerm F (f.sorts ∘ Γ)) = some (⟨_,_⟩ : PackedTerm F (f.sorts ∘ Γ))
  congr 2
  rw [quantifiedTerm_app]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem foldTerms_map (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (op : Operation E.signature 2 (fun _ => s) s)
    (a : Uflia.Quantified.Term E.signature Γ s) (ts : List (Uflia.Quantified.Term E.signature Γ s)) :
    Hom.quantifiedTerm f (foldTerms op a ts) =
      foldTerms (Hom.operation f op) (Hom.quantifiedTerm f a) (ts.map (Hom.quantifiedTerm f)) := by
  induction ts generalizing a with
  | nil => rfl
  | cons b ts ih =>
      simp only [foldTerms, List.foldl_cons, List.map_cons] at ih ⊢
      rw [ih]
      congr 1
      change Hom.quantifiedTerm f (.app op _) = .app (Hom.operation f op) _
      rw [quantifiedTerm_app]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem fold_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {s : SortCode String} (op : Operation E.signature 2 (fun _ => s) s)
    (es : List Expr) (t : PackedTerm E Γ) (h : fold? source op es = some t) :
    fold? target (Hom.operation f op) es = some (mapPacked f t) := by
  cases es with
  | nil => simp [fold?] at h
  | cons a es =>
      cases es with
      | nil => simp [fold?] at h
      | cons b rest =>
          obtain ⟨v,hv,a,ha,ts,hts,rfl⟩ :
              ∃ v, source a = some v ∧ ∃ a, v.expect? s = some a ∧
              ∃ ts, typedTerms? source s (b :: rest) = some ts ∧
                (⟨s,foldTerms op a ts⟩ : PackedTerm E Γ) = t := by
            simpa [fold?, Option.bind_eq_some_iff] using h
          simp only [fold?, bind, pure, hfg _ v hv, Option.bind_some, expect_mapPacked_of_eq f v a ha,
            typedTerms_transport f hfg s (b :: rest) ts hts]
          exact congrArg (fun x => some (⟨f.sorts s,x⟩ : PackedTerm F (f.sorts ∘ Γ)))
            (foldTerms_map f op a ts).symm


theorem unary_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 1 (fun _ => input) output)
    (op' : Operation F.signature 1 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op')
    (e : Expr) (t : PackedTerm E Γ) (h : unary? source op e = some t) :
    unary? target op' e = some (mapPacked f t) := by
  cases hs
  cases ht
  cases eq_of_heq hop
  exact unary_transport f hfg op e t h

theorem binary_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 2 (fun _ => input) output)
    (op' : Operation F.signature 2 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op')
    (a b : Expr) (t : PackedTerm E Γ) (h : binary? source op a b = some t) :
    binary? target op' a b = some (mapPacked f t) := by
  cases hs
  cases ht
  cases eq_of_heq hop
  exact binary_transport f hfg op a b t h

theorem fold_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {s t' : SortCode String} (hs : f.sorts s = t')
    (op : Operation E.signature 2 (fun _ => s) s)
    (op' : Operation F.signature 2 (fun _ => t') t')
    (hop : HEq (Hom.operation f op) op')
    (es : List Expr) (t : PackedTerm E Γ) (h : fold? source op es = some t) :
    fold? target op' es = some (mapPacked f t) := by
  cases hs
  cases eq_of_heq hop
  exact fold_transport f hfg op es t h

theorem expect_at (f : environmentSignature E ⟶ environmentSignature F)
    (v : PackedTerm E Γ) {s t : SortCode String} (hs : f.sorts s = t)
    (a : Uflia.Quantified.Term E.signature Γ s) (h : v.expect? s = some a) :
    (mapPacked f v).expect? t = some (termAt f hs a) := by
  cases hs
  exact expect_mapPacked_of_eq f v a h

abbrev boolTerm (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Quantified.Formula E.signature Γ) : Uflia.Quantified.Formula F.signature (f.sorts ∘ Γ) := termAt f f.bool p
abbrev intTerm (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Quantified.Term E.signature Γ .int) : Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) .int := termAt f f.int p

theorem boolTerm_all (f : environmentSignature E ⟶ environmentSignature F)
    (s : SortCode String)
    (body : Uflia.Quantified.Term E.signature (Fin.cases s Γ) .bool) :
    boolTerm f (.all s body) = .all (f.sorts s)
      (Hom.quantifiedBody f s (Hom.quantifiedTerm f body)) := by
  apply eq_of_heq
  exact (termAt_heq f f.bool _).trans (quantifiedTerm_all_heq f s body)

theorem boolTerm_ex (f : environmentSignature E ⟶ environmentSignature F)
    (s : SortCode String)
    (body : Uflia.Quantified.Term E.signature (Fin.cases s Γ) .bool) :
    boolTerm f (.ex s body) = .ex (f.sorts s)
      (Hom.quantifiedBody f s (Hom.quantifiedTerm f body)) := by
  apply eq_of_heq
  exact (termAt_heq f f.bool _).trans (quantifiedTerm_ex_heq f s body)

theorem mapPacked_bool (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Quantified.Formula E.signature Γ) : mapPacked f ⟨.bool,p⟩ = ⟨.bool,boolTerm f p⟩ :=
  mapPacked_at f f.bool p

theorem mapPacked_int (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Quantified.Term E.signature Γ .int) : mapPacked f ⟨.int,p⟩ = ⟨.int,intTerm f p⟩ :=
  mapPacked_at f f.int p

private theorem unary_at (f : environmentSignature E ⟶ environmentSignature F)
    {a b s t : SortCode String} (ha : f.sorts a = b) (hs : f.sorts s = t)
    (op : Operation E.signature 1 (fun _ => a) s)
    (op' : Operation F.signature 1 (fun _ => b) t)
    (hop : HEq (Hom.operation f op) op') (v : Uflia.Quantified.Term E.signature Γ a) :
    termAt f hs (.app op (fun _ => v)) = .app op' (fun _ => termAt f ha v) :=
  termAt_app f (fun _ => ha) hs op op' hop _

private theorem binary_at (f : environmentSignature E ⟶ environmentSignature F)
    {a b s t : SortCode String} (ha : f.sorts a = b) (hs : f.sorts s = t)
    (op : Operation E.signature 2 (fun _ => a) s)
    (op' : Operation F.signature 2 (fun _ => b) t)
    (hop : HEq (Hom.operation f op) op') (v w : Uflia.Quantified.Term E.signature Γ a) :
    termAt f hs (.app op (Fin.cases v (fun _ => w))) =
      .app op' (Fin.cases (termAt f ha v) (fun _ => termAt f ha w)) := by
  rw [termAt_app f (fun _ => ha) hs op op' hop]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem operation_not_heq (f : environmentSignature E ⟶ environmentSignature F)
     : HEq (Hom.operation f (.not)) (Operation.not (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_and_heq (f : environmentSignature E ⟶ environmentSignature F)
     : HEq (Hom.operation f (.and)) (Operation.and (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_or_heq (f : environmentSignature E ⟶ environmentSignature F)
     : HEq (Hom.operation f (.or)) (Operation.or (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_eq_heq (f : environmentSignature E ⟶ environmentSignature F)
    (s : SortCode String) : HEq (Hom.operation f (.eq s)) (Operation.eq (A := F.signature) (f.sorts s)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_integer_heq (f : environmentSignature E ⟶ environmentSignature F)
    (n : Int) : HEq (Hom.operation f (.integer n)) (Operation.integer (A := F.signature) n) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_boolean_heq (f : environmentSignature E ⟶ environmentSignature F)
    (b : Bool) : HEq (Hom.operation f (.boolean b)) (Operation.boolean (A := F.signature) b) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_add_heq (f : environmentSignature E ⟶ environmentSignature F)
     : HEq (Hom.operation f (.add)) (Operation.add (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_sub_heq (f : environmentSignature E ⟶ environmentSignature F)
     : HEq (Hom.operation f (.sub)) (Operation.sub (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_scale_heq (f : environmentSignature E ⟶ environmentSignature F)
    (n : Int) : HEq (Hom.operation f (.scale n)) (Operation.scale (A := F.signature) n) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem boolTerm_not (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Quantified.Formula E.signature Γ) :
    boolTerm f (.app .not (fun _ => p)) = .app .not (fun _ => boolTerm f p) :=
  unary_at f f.bool f.bool .not .not (operation_not_heq f) p

theorem boolTerm_or (f : environmentSignature E ⟶ environmentSignature F)
    (p q : Uflia.Quantified.Formula E.signature Γ) :
    boolTerm f (.app .or (Fin.cases p (fun _ => q))) =
      .app .or (Fin.cases (boolTerm f p) (fun _ => boolTerm f q)) :=
  binary_at f f.bool f.bool .or .or (operation_or_heq f) p q

theorem boolTerm_and (f : environmentSignature E ⟶ environmentSignature F)
    (p q : Uflia.Quantified.Formula E.signature Γ) :
    boolTerm f (.app .and (Fin.cases p (fun _ => q))) =
      .app .and (Fin.cases (boolTerm f p) (fun _ => boolTerm f q)) :=
  binary_at f f.bool f.bool .and .and (operation_and_heq f) p q

theorem boolTerm_eq (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (p q : Uflia.Quantified.Term E.signature Γ s) :
    boolTerm f (.app (.eq s) (Fin.cases p (fun _ => q))) =
      .app (.eq (f.sorts s)) (Fin.cases (Hom.quantifiedTerm f p) (fun _ => Hom.quantifiedTerm f q)) :=
  binary_at f rfl f.bool (.eq s) (.eq (f.sorts s)) (operation_eq_heq f s) p q

theorem boolTerm_boolean (f : environmentSignature E ⟶ environmentSignature F) (b : Bool) :
    boolTerm (Γ := Γ) f (Uflia.Quantified.Term.boolean b) = Uflia.Quantified.Term.boolean b := by
  rw [show Uflia.Quantified.Term.boolean (A := E.signature) (Γ := Γ) b =
    .app (.boolean b) (fun i => i.elim0) from rfl]
  apply Eq.trans (termAt_app f (fun i : Fin 0 => i.elim0) f.bool (.boolean b) (.boolean b)
    (operation_boolean_heq f b) (fun i => i.elim0))
  congr 1
  funext i
  exact i.elim0

theorem intTerm_integer (f : environmentSignature E ⟶ environmentSignature F) (n : Int) :
    intTerm (Γ := Γ) f (Uflia.Quantified.Term.integer n) = Uflia.Quantified.Term.integer n := by
  rw [show Uflia.Quantified.Term.integer (A := E.signature) (Γ := Γ) n =
    .app (.integer n) (fun i => i.elim0) from rfl]
  apply Eq.trans (termAt_app f (fun i : Fin 0 => i.elim0) f.int (.integer n) (.integer n)
    (operation_integer_heq f n) (fun i => i.elim0))
  congr 1
  funext i
  exact i.elim0

theorem implication_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E Γ) (h : implication? source a b = some t) :
    implication? target a b = some (mapPacked f t) := by
  obtain ⟨va,hva,ta,hta,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ ta, va.expect? .bool = some ta ∧
      ∃ vb, source b = some vb ∧ ∃ tb, vb.expect? .bool = some tb ∧
        (⟨.bool,.app .or (Fin.cases (.app .not (fun _ => ta)) (fun _ => tb))⟩ : PackedTerm E Γ) = t := by
    simpa [implication?, Option.bind_eq_some_iff] using h
  simp only [implication?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_at f va f.bool ta hta, expect_at f vb f.bool tb htb]
  rw [mapPacked_bool f, boolTerm_or f, boolTerm_not f]

theorem xor_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E Γ) (h : xor? source a b = some t) :
    xor? target a b = some (mapPacked f t) := by
  obtain ⟨va,hva,ta,hta,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ ta, va.expect? .bool = some ta ∧
      ∃ vb, source b = some vb ∧ ∃ tb, vb.expect? .bool = some tb ∧
        (⟨.bool,.app .not (fun _ => .app (.eq .bool) (Fin.cases ta (fun _ => tb)))⟩ : PackedTerm E Γ) = t := by
    simpa [xor?, Option.bind_eq_some_iff] using h
  simp only [xor?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_at f va f.bool ta hta, expect_at f vb f.bool tb htb]
  rw [mapPacked_bool f, boolTerm_not f, boolTerm_eq f]
  have eqmap :
      (Uflia.Quantified.Term.app (.eq (f.sorts .bool))
        (Fin.cases (Hom.quantifiedTerm f ta) (fun _ => Hom.quantifiedTerm f tb)) :
          Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) .bool) =
      .app (.eq .bool) (Fin.cases (boolTerm f ta) (fun _ => boolTerm f tb)) := by
    exact eq_of_heq (app_heq (funext (fun _ => f.bool)) rfl _ _
      (by
        generalize h : f.sorts .bool = b
        have hb : b = .bool := h.symm.trans f.bool
        cases hb
        rfl) _ _ (fun i => by
        refine Fin.cases ?_ (fun _ => ?_) i
        · exact (termAt_heq f f.bool ta).symm
        · exact (termAt_heq f f.bool tb).symm))
  rw [eqmap]

theorem operation_ite_heq (f : environmentSignature E ⟶ environmentSignature F)
    (s : SortCode String) :
    HEq (Hom.operation f (.ite s)) (Operation.ite (A := F.signature) (f.sorts s)) := by
  have profiles : f.sorts ∘ Fin.cases .bool (fun _ : Fin 2 => s) =
      Fin.cases .bool (fun _ : Fin 2 => f.sorts s) := by
    funext i
    exact Fin.cases f.bool (fun _ => rfl) i
  have shifted : Hom.operation f (.ite s) =
      profiles.symm ▸ (Operation.ite (A := F.signature) (f.sorts s)) := by
    cases s <;> rfl
  rw [shifted]
  exact eqRec_heq (φ := fun ss : Fin 3 → SortCode String =>
    Operation F.signature 3 ss (f.sorts s)) profiles.symm (.ite (f.sorts s))

theorem quantifiedTerm_ite (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (c : Uflia.Quantified.Formula E.signature Γ) (a b : Uflia.Quantified.Term E.signature Γ s) :
    Hom.quantifiedTerm f (.app (.ite s) (Fin.cases c (Fin.cases a (fun _ => b)))) =
      .app (.ite (f.sorts s))
        (Fin.cases (boolTerm f c) (Fin.cases (Hom.quantifiedTerm f a) (fun _ => Hom.quantifiedTerm f b))) := by
  have hs : ∀ i, f.sorts (iteProfile s i) =
      iteProfile (f.sorts s) i :=
    fun i => Fin.cases f.bool (fun _ => rfl) i
  have h := termAt_app f hs rfl (.ite s) (.ite (f.sorts s)) (operation_ite_heq f s)
    (show ∀ i, Uflia.Quantified.Term E.signature Γ (iteProfile s i) from
      Fin.cases c (Fin.cases a (fun _ => b)))
  change Hom.quantifiedTerm f _ = _ at h
  rw [h]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

theorem ite_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (c a b : Expr) (t : PackedTerm E Γ) (h : ite? source c a b = some t) :
    ite? target c a b = some (mapPacked f t) := by
  obtain ⟨vc,hvc,tc,htc,va,hva,vb,hvb,tb,htb,rfl⟩ :
      ∃ vc, source c = some vc ∧ ∃ tc, vc.expect? .bool = some tc ∧
      ∃ va, source a = some va ∧ ∃ vb, source b = some vb ∧
      ∃ tb, vb.expect? va.sort = some tb ∧
        (⟨va.sort,.app (.ite va.sort) (Fin.cases tc (Fin.cases va.term (fun _ => tb)))⟩ : PackedTerm E Γ) = t := by
    simpa [ite?, Option.bind_eq_some_iff] using h
  simp only [ite?, bind, pure, hfg c vc hvc, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_at f vc f.bool tc htc, mapPacked_sort,
    expect_mapPacked_of_eq f vb tb htb]
  exact congrArg (fun x => some (⟨f.sorts va.sort,x⟩ : PackedTerm F (f.sorts ∘ Γ)))
    (quantifiedTerm_ite f tc va.term tb).symm

theorem equality_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E Γ) (h : equality? source a b = some t) :
    equality? target a b = some (mapPacked f t) := by
  obtain ⟨va,hva,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ vb, source b = some vb ∧
      ∃ tb, vb.expect? va.sort = some tb ∧
        (⟨.bool,.app (.eq va.sort) (Fin.cases va.term (fun _ => tb))⟩ : PackedTerm E Γ) = t := by
    simpa [equality?, Option.bind_eq_some_iff] using h
  simp only [equality?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    mapPacked_sort, expect_mapPacked_of_eq f vb tb htb]
  change some (⟨.bool,.app (.eq (f.sorts va.sort))
    (Fin.cases (Hom.quantifiedTerm f va.term) (fun _ => Hom.quantifiedTerm f tb))⟩ : PackedTerm F (f.sorts ∘ Γ)) = _
  rw [mapPacked_bool f, boolTerm_eq f]

theorem foldTerms_at_map (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (hs : f.sorts s = t)
    (op : Operation E.signature 2 (fun _ => s) s)
    (op' : Operation F.signature 2 (fun _ => t) t)
    (hop : HEq (Hom.operation f op) op')
    (a : Uflia.Quantified.Term E.signature Γ s) (ts : List (Uflia.Quantified.Term E.signature Γ s)) :
    termAt f hs (foldTerms op a ts) =
      foldTerms op' (termAt f hs a) (ts.map (termAt f hs)) := by
  induction ts generalizing a with
  | nil => rfl
  | cons b ts ih =>
      simp only [foldTerms, List.foldl_cons, List.map_cons] at ih ⊢
      rw [ih]
      exact congrArg (fun x => List.foldl (pair op') x (ts.map (termAt f hs)))
        (binary_at f hs hs op op' hop a b)

theorem conjunction_map (f : environmentSignature E ⟶ environmentSignature F)
    (ts : List (Uflia.Quantified.Formula E.signature Γ)) :
    boolTerm f (conjunction ts) = conjunction (ts.map (boolTerm f)) := by
  cases ts with
  | nil => exact boolTerm_boolean f true
  | cons a ts => exact foldTerms_at_map f f.bool .and .and (operation_and_heq f) a ts

theorem compare_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (op : Operation E.signature 2 (fun _ => .int) .bool)
    (op' : Operation F.signature 2 (fun _ => .int) .bool)
    (hop : HEq (Hom.operation f op) op') (reverse : Bool)
    (es : List Expr) (t : PackedTerm E Γ) (h : compare? source op reverse es = some t) :
    compare? target op' reverse es = some (mapPacked f t) := by
  cases es with
  | nil => simp [compare?] at h
  | cons a es =>
      cases es with
      | nil => simp [compare?] at h
      | cons b rest =>
          change (typedTerms? source .int (a :: b :: rest)).bind _ = some t at h
          obtain ⟨ts,hts,h⟩ := Option.bind_eq_some_iff.mp h
          cases Option.some.inj h
          change (typedTerms? target .int (a :: b :: rest)).bind _ = _
          have hts' : typedTerms? target .int (a :: b :: rest) =
              some (ts.map (intTerm f)) := typedTerms_at_transport f hfg f.int _ ts hts
          rw [hts']
          change some (⟨.bool,_⟩ : PackedTerm F (f.sorts ∘ Γ)) = some (mapPacked f ⟨.bool,_⟩)
          rw [mapPacked_bool f, conjunction_map f]
          congr 2
          apply Eq.symm
          apply congrArg conjunction
          apply adjacent_transport (intTerm f) (boolTerm f)
          intro x y
          cases reverse <;> exact binary_at f f.int f.bool op op' hop _ _

theorem equalities_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (distinct : Bool) (es : List Expr) (t : PackedTerm E Γ)
    (h : equalities? source distinct es = some t) :
    equalities? target distinct es = some (mapPacked f t) := by
  cases es with
  | nil => simp [equalities?] at h
  | cons a es =>
      cases es with
      | nil => simp [equalities?] at h
      | cons b rest =>
          change (source a).bind _ = some t at h
          obtain ⟨va,hva,h⟩ := Option.bind_eq_some_iff.mp h
          change (typedTerms? source va.sort (b :: rest)).bind _ = some t at h
          obtain ⟨ts,hts,h⟩ := Option.bind_eq_some_iff.mp h
          cases Option.some.inj h
          change (target a).bind _ = _
          rw [hfg a va hva]
          change (typedTerms? target (f.sorts va.sort) (b :: rest)).bind _ = _
          rw [typedTerms_transport f hfg va.sort _ ts hts]
          change some (⟨.bool,_⟩ : PackedTerm F (f.sorts ∘ Γ)) = some (mapPacked f ⟨.bool,_⟩)
          rw [mapPacked_bool f, conjunction_map f]
          congr 2
          have heq (x y : Uflia.Quantified.Term E.signature Γ va.sort) := boolTerm_eq f x y
          have hnot (x y : Uflia.Quantified.Term E.signature Γ va.sort) :
              boolTerm f (.app .not (fun _ =>
                .app (.eq va.sort) (Fin.cases x (fun _ => y)))) =
              .app .not (fun _ => .app (.eq (f.sorts va.sort))
                (Fin.cases (Hom.quantifiedTerm f x) (fun _ => Hom.quantifiedTerm f y))) := by
            rw [boolTerm_not f, boolTerm_eq f]
          cases distinct with
          | false =>
              apply congrArg conjunction
              simpa only [Bool.false_eq_true, reduceIte, List.map_cons, mapPacked] using
                (adjacent_transport (Hom.quantifiedTerm f) (boolTerm f)
                  (fun x y => .app (.eq va.sort) (Fin.cases x (fun _ => y)))
                  (fun x y => .app (.eq (f.sorts va.sort)) (Fin.cases x (fun _ => y)))
                  heq (va.term :: ts)).symm
          | true =>
              apply congrArg conjunction
              simpa only [reduceIte, List.map_cons, mapPacked] using
                (allPairs_transport (Hom.quantifiedTerm f) (boolTerm f)
                  (fun x y => .app .not (fun _ => .app (.eq va.sort) (Fin.cases x (fun _ => y))))
                  (fun x y => .app .not (fun _ => .app (.eq (f.sorts va.sort)) (Fin.cases x (fun _ => y))))
                  hnot (va.term :: ts)).symm

theorem operation_le_heq (f : environmentSignature E ⟶ environmentSignature F) :
    HEq (Hom.operation f (.le)) (Operation.le (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

theorem operation_lt_heq (f : environmentSignature E ⟶ environmentSignature F) :
    HEq (Hom.operation f (.lt)) (Operation.lt (A := F.signature)) := by
  unfold Hom.operation
  exact cast_heq _ _

private theorem integerValue_heq {s t : SortCode String} (hs : s = t)
    (a : Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) s) (b : Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) t) (h : HEq a b) :
    integerValue? a = integerValue? b := by
  cases hs
  cases eq_of_heq h
  rfl

private theorem integerValue_at (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (a : Uflia.Quantified.Term E.signature Γ s) :
    integerValue? (Hom.quantifiedTerm f a) = integerValue? (termAt f h a) :=
  integerValue_heq h _ _ (termAt_heq f h a).symm

private theorem integerValue_uf {E : Environment} {n : Nat}
    {ss : Fin n → SortCode String} {s : SortCode String}
    (symbol : E.signature.operations n ss s) (args : ∀ i, Uflia.Quantified.Term E.signature Γ (ss i)) :
    integerValue? (E := E) (.app (.uf symbol) args) = none := by
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
      cases n with
      | zero => cases s <;> rfl
      | succ n => cases s <;> rfl

private theorem integerValue_ite {E : Environment} {s : SortCode String}
    (args : ∀ i, Uflia.Quantified.Term E.signature Γ (iteProfile s i)) :
    integerValue? (E := E) (.app (.ite s) args) = none := by
  cases s <;> rfl

/-- Literal recognition retains the constructor test, including nested scaling. -/
theorem integerValue_map (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (t : Uflia.Quantified.Term E.signature Γ s) :
    integerValue? (Hom.quantifiedTerm f t) = integerValue? t := by
  induction t with
  | var i =>
      rw [quantifiedTerm_var]
      rfl
  | app op args ih =>
      cases op with
      | uf symbol =>
          rw [quantifiedTerm_app]
          simp only [Hom.operation, integerValue_uf]
      | integer n =>
          have ha : args = (fun i => i.elim0) := funext (fun i => i.elim0)
          subst args
          rw [integerValue_at f f.int]
          change integerValue? (intTerm f (Uflia.Quantified.Term.integer n)) = some n
          rw [intTerm_integer]
          rfl
      | scale n =>
          rw [integerValue_at f f.int,
            termAt_app f (fun _ => f.int) f.int (.scale n) (.scale n) (operation_scale_heq f n)]
          change (integerValue? (intTerm f (args 0))).map (n * ·) =
            (integerValue? (args 0)).map (n * ·)
          rw [← integerValue_at f f.int, ih]
      | boolean b =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun i => i.elim0) f.bool (.boolean b) (.boolean b) (operation_boolean_heq f b)]
          rfl
      | add =>
          rw [integerValue_at f f.int,
            termAt_app f (fun _ => f.int) f.int .add .add (operation_add_heq f)]
          rfl
      | sub =>
          rw [integerValue_at f f.int,
            termAt_app f (fun _ => f.int) f.int .sub .sub (operation_sub_heq f)]
          rfl
      | le =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun _ => f.int) f.bool .le .le (operation_le_heq f)]
          rfl
      | lt =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun _ => f.int) f.bool .lt .lt (operation_lt_heq f)]
          rfl
      | eq s =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun _ => rfl) f.bool (.eq s) (.eq (f.sorts s)) (operation_eq_heq f s)]
          rfl
      | not =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun _ => f.bool) f.bool .not .not (operation_not_heq f)]
          rfl
      | and =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun _ => f.bool) f.bool .and .and (operation_and_heq f)]
          rfl
      | or =>
          rw [integerValue_at f f.bool,
            termAt_app f (fun _ => f.bool) f.bool .or .or (operation_or_heq f)]
          rfl
      | ite s =>
          have ha : args = Fin.cases (args 0) (Fin.cases (args 1) (fun _ => args 2)) := by
            funext i
            exact Fin.cases rfl (fun j => Fin.cases rfl
              (fun k => Fin.cases rfl (fun l => l.elim0) k) j) i
          rw [ha, quantifiedTerm_ite]
          simp only [integerValue_ite]

  | all s body ih =>
      rw [integerValue_at f f.bool]
      change integerValue? (boolTerm f (.all s body)) = none
      rw [boolTerm_all]
      rfl
  | ex s body ih =>
      rw [integerValue_at f f.bool]
      change integerValue? (boolTerm f (.ex s body)) = none
      rw [boolTerm_ex]
      rfl


theorem intTerm_scale (f : environmentSignature E ⟶ environmentSignature F)
    (c : Int) (p : Uflia.Quantified.Term E.signature Γ .int) :
    intTerm f (.app (.scale c) (fun _ => p)) = .app (.scale c) (fun _ => intTerm f p) :=
  unary_at f f.int f.int (.scale c) (.scale c) (operation_scale_heq f c) p

private theorem uf_cast_heq {n : Nat} {ss : Fin n → SortCode String}
    {s t : SortCode String} (h : s = t) (symbol : F.signature.operations n ss s) :
    HEq (Operation.uf symbol)
      (Operation.uf (cast (congrArg (F.signature.operations n ss) h) symbol)) := by
  cases h
  rfl

private theorem ite_sort_heq {s t : SortCode String} (h : s = t) :
    HEq (Operation.ite (A := F.signature) s) (Operation.ite (A := F.signature) t) := by
  cases h
  rfl

private theorem intTerm_uf (f : environmentSignature E ⟶ environmentSignature F)
    {n : Nat} {ss : Fin n → SortCode String}
    (symbol : E.signature.operations n ss .int)
    (args : ∀ i, Uflia.Quantified.Term E.signature Γ (ss i)) :
    intTerm f (.app (.uf symbol) args) =
      .app (.uf (cast (congrArg (F.signature.operations n (f.sorts ∘ ss)) f.int)
        (f.operations symbol))) (fun i => Hom.quantifiedTerm f (args i)) :=
  termAt_app f (fun _ => rfl) f.int (.uf symbol) _
    (uf_cast_heq f.int (f.operations symbol)) args

private theorem intTerm_ite (f : environmentSignature E ⟶ environmentSignature F)
    (args : ∀ i, Uflia.Quantified.Term E.signature Γ (iteProfile .int i)) :
    intTerm f (.app (.ite .int) args) =
      .app (.ite .int) (fun i => termAt f
        (show f.sorts (iteProfile .int i) =
          iteProfile .int i from
            Fin.cases f.bool (fun _ => f.int) i) (args i)) :=
  termAt_app f (fun i => Fin.cases f.bool (fun _ => f.int) i) f.int (.ite .int) (.ite .int)
    ((operation_ite_heq f .int).trans (ite_sort_heq f.int)) args

private theorem scaleLinear_uf {E : Environment} {n : Nat}
    {ss : Fin n → SortCode String} (symbol : E.signature.operations n ss .int)
    (args : ∀ i, Uflia.Quantified.Term E.signature Γ (ss i)) (c : Int) :
    scaleLinear (E := E) c (.app (.uf symbol) args) =
      .app (.scale c) (fun _ => .app (.uf symbol) args) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n => rfl

private def scaledTerm {E : Environment} {k : Nat} {Γ : Fin k → SortCode String}
    (c : Int) {s : SortCode String} (term : Uflia.Quantified.Term E.signature Γ s) :
    Uflia.Quantified.Term E.signature Γ s :=
  match s, term with
  | .int, term => .app (.scale c) (fun _ => term)
  | _, term => term

private abbrev scaledRef {E : Environment} {k : Nat} {Γ : Fin k → SortCode String}
    (c : Int) {s : SortCode String} (r : Uflia.Quantified.Ref Γ s) :
    Uflia.Quantified.Term E.signature Γ s := scaledTerm c r.term

private theorem scaleLinear_ref {E : Environment} {k : Nat} {Γ : Fin k → SortCode String}
    {s : SortCode String} (r : Uflia.Quantified.Ref Γ s) (c : Int) :
    scaleLinear (E := E) c r.term = scaledRef c r := by
  cases r with
  | index i =>
      simp only [Uflia.Quantified.Ref.term, scaleLinear, scaledRef, scaledTerm]
      generalize hv : (Uflia.Quantified.Term.var i :
        Uflia.Quantified.Term E.signature Γ (Γ i)) = term
      clear hv
      generalize Γ i = sort at term ⊢
      cases sort <;> rfl

private theorem cast_ref_term {E : Environment} {k : Nat} {Γ : Fin k → SortCode String}
    {s t : SortCode String} (h : s = t) (r : Uflia.Quantified.Ref Γ s) :
    cast (congrArg (Uflia.Quantified.Term E.signature Γ) h) r.term =
      (cast (congrArg (Uflia.Quantified.Ref Γ) h) r).term := by
  cases h
  rfl

private theorem scaleLinear_cast {E : Environment} {k : Nat} {Γ : Fin k → SortCode String}
    {s t : SortCode String} (h : s = t) (c : Int)
    (v : Uflia.Quantified.Term E.signature Γ s) :
    cast (congrArg (Uflia.Quantified.Term E.signature Γ) h) (scaleLinear c v) =
      scaleLinear c (cast (congrArg (Uflia.Quantified.Term E.signature Γ) h) v) := by
  cases h
  rfl

private theorem scaleLinear_ref_transport (f : environmentSignature E ⟶ environmentSignature F)
    (r : Uflia.Quantified.Ref Γ .int) (c : Int) :
    intTerm f (scaleLinear c r.term) = scaleLinear c (intTerm f r.term) := by
  rw [scaleLinear_ref]
  change intTerm f (.app (.scale c) (fun _ => r.term)) = _
  rw [intTerm_scale]
  unfold intTerm termAt
  rw [mapRef_term, cast_ref_term f.int]
  simpa only [scaledRef, scaledTerm] using
    (scaleLinear_ref (E := F)
      (cast (congrArg (Uflia.Quantified.Ref (f.sorts ∘ Γ)) f.int) (mapRef f r)) c).symm

private theorem scaleLinear_int_aux (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (t : Uflia.Quantified.Term E.signature Γ s) (coefficient : Int) :
    ∀ h : s = .int,
      intTerm f (cast (congrArg (Uflia.Quantified.Term E.signature Γ) h) (scaleLinear coefficient t)) =
        scaleLinear coefficient (intTerm f (cast (congrArg (Uflia.Quantified.Term E.signature Γ) h) t)) := by
  induction t generalizing coefficient with
  | var i =>
      intro hs
      rw [scaleLinear_cast]
      change intTerm f (scaleLinear coefficient
        (cast (congrArg (Uflia.Quantified.Term E.signature _) hs)
          (Uflia.Quantified.Ref.index i).term)) =
          scaleLinear coefficient (intTerm f (cast (congrArg (Uflia.Quantified.Term E.signature _) hs)
          (Uflia.Quantified.Ref.index i).term))
      simp only [cast_ref_term (E := E) hs (.index i)]
      exact scaleLinear_ref_transport f
        (cast (congrArg (Uflia.Quantified.Ref _) hs) (.index i)) coefficient
      exact hs
  | app op args ih =>
      intro hs
      cases hs
      cases op with
      | uf symbol =>
          simp only [cast_eq]
          rw [scaleLinear_uf, intTerm_scale, intTerm_uf, scaleLinear_uf]
      | integer n =>
          simp only [cast_eq]
          have ha : args = (fun i => i.elim0) := funext (fun i => i.elim0)
          subst args
          change intTerm f (Uflia.Quantified.Term.integer (coefficient * n)) =
            scaleLinear coefficient (intTerm f (Uflia.Quantified.Term.integer n))
          rw [intTerm_integer, intTerm_integer]
          rfl
      | add =>
          simp only [cast_eq]
          change intTerm f (.app .add (Fin.cases (scaleLinear coefficient (args 0))
            (fun _ => scaleLinear coefficient (args 1)))) = _
          change termAt f f.int (.app .add _) = scaleLinear coefficient (termAt f f.int (.app .add args))
          rw [binary_at f f.int f.int .add .add (operation_add_heq f),
            termAt_app f (fun _ => f.int) f.int .add .add (operation_add_heq f)]
          simp only [scaleLinear, pair]
          congr 1
          funext i
          exact Fin.cases (ih 0 coefficient rfl)
            (fun j => Fin.cases (ih 1 coefficient rfl) (fun k => k.elim0) j) i
      | sub =>
          simp only [cast_eq]
          change intTerm f (.app .sub (Fin.cases (scaleLinear coefficient (args 0))
            (fun _ => scaleLinear coefficient (args 1)))) = _
          change termAt f f.int (.app .sub _) = scaleLinear coefficient (termAt f f.int (.app .sub args))
          rw [binary_at f f.int f.int .sub .sub (operation_sub_heq f),
            termAt_app f (fun _ => f.int) f.int .sub .sub (operation_sub_heq f)]
          simp only [scaleLinear, pair]
          congr 1
          funext i
          exact Fin.cases (ih 0 coefficient rfl)
            (fun j => Fin.cases (ih 1 coefficient rfl) (fun k => k.elim0) j) i
      | scale k =>
          simp only [cast_eq]
          have ha : args = (fun _ => args 0) := by
            funext i
            exact Fin.cases rfl (fun j => j.elim0) i
          rw [ha]
          change intTerm f (scaleLinear (coefficient * k) (args 0)) =
            scaleLinear coefficient (intTerm f (.app (.scale k) (fun _ => args 0)))
          rw [intTerm_scale]
          exact ih 0 (coefficient * k) rfl
      | ite s =>
          simp only [cast_eq]
          rw [intTerm_ite]
          change intTerm f (.app (.scale coefficient) (fun _ => .app (.ite .int) args)) = _
          rw [intTerm_scale, intTerm_ite]
          rfl

  | all s body ih => intro hs; cases hs
  | ex s body ih => intro hs; cases hs

theorem scaleLinear_map (f : environmentSignature E ⟶ environmentSignature F)
    (coefficient : Int) (t : Uflia.Quantified.Term E.signature Γ .int) :
    intTerm f (scaleLinear coefficient t) = scaleLinear coefficient (intTerm f t) :=
  scaleLinear_int_aux f t coefficient rfl

theorem multiplyFactors_map (f : environmentSignature E ⟶ environmentSignature F)
    (ts : List (Uflia.Quantified.Term E.signature Γ .int)) (coefficient : Int)
    (factor : Option (Uflia.Quantified.Term E.signature Γ .int)) :
    multiplyFactors? (ts.map (intTerm f)) coefficient (factor.map (intTerm f)) =
      (multiplyFactors? ts coefficient factor).map (intTerm f) := by
  induction ts generalizing coefficient factor with
  | nil =>
      cases factor with
      | none =>
          simp only [List.map_nil, Option.map_none, multiplyFactors?, Option.map_some]
          exact congrArg some (intTerm_integer f coefficient).symm
      | some t =>
          simp only [List.map_nil, Option.map_some, multiplyFactors?]
          exact congrArg some (scaleLinear_map f coefficient t).symm
  | cons t ts ih =>
      have literal : integerValue? (intTerm f t) = integerValue? t :=
        (integerValue_at f f.int t).symm.trans (integerValue_map f t)
      simp only [List.map_cons, multiplyFactors?, literal]
      cases hv : integerValue? t with
      | some k => exact ih (coefficient * k) factor
      | none =>
          cases factor with
          | none => exact ih coefficient (some t)
          | some factor => rfl

theorem multiply_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (es : List Expr) (t : PackedTerm E Γ) (h : multiply? source es = some t) :
    multiply? target es = some (mapPacked f t) := by
  cases es with
  | nil => simp [multiply?] at h
  | cons a es =>
      cases es with
      | nil => simp [multiply?] at h
      | cons b rest =>
          obtain ⟨ts,hts,term,hterm,rfl⟩ :
              ∃ ts, typedTerms? source .int (a :: b :: rest) = some ts ∧
              ∃ term, multiplyFactors? ts 1 none = some term ∧
                (⟨.int,term⟩ : PackedTerm E Γ) = t := by
            simpa [multiply?, Option.bind_eq_some_iff] using h
          have hts' : typedTerms? target .int (a :: b :: rest) =
              some (ts.map (intTerm f)) := typedTerms_at_transport f hfg f.int _ ts hts
          change (typedTerms? target .int (a :: b :: rest)).bind _ = _
          rw [hts']
          change (multiplyFactors? (ts.map (intTerm f)) 1 none).bind _ = _
          have hm := multiplyFactors_map f ts 1 none
          simp only [Option.map_none,hterm,Option.map_some] at hm
          rw [hm]
          change some (⟨.int,intTerm f term⟩ : PackedTerm F (f.sorts ∘ Γ)) = some (mapPacked f ⟨.int,term⟩)
          rw [mapPacked_int f]

/-- Successful source children produce actual transformed expressions with the
mapped decoding relation, at the SAME caller-supplied target recursion budget. -/
theorem renameChildren_success (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F (f.sorts ∘ Γ)))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (es : List Expr) (decoded : ∃ values, es.mapM source = some values) :
    ∃ outputs, es.mapM rename = some outputs ∧
      List.Forall₂ (Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs := by
  obtain ⟨values, decoded⟩ := decoded
  induction es generalizing values with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons e es ih =>
    simp [List.mapM_cons, Option.bind_eq_some_iff] at decoded
    obtain ⟨value, head, values, tail, rfl⟩ := decoded
    obtain ⟨output, renamed, mapped⟩ := children e value head
    obtain ⟨outputs, renamedTail, relatedTail⟩ := ih values tail
    refine ⟨output :: outputs, by simp [renamed, renamedTail], .cons ?_ relatedTail⟩
    intro v hv
    simp only [head, Option.map_some, Option.some.injEq] at hv
    subst v
    exact mapped

theorem unary_syntax (f : environmentSignature E ⟶ environmentSignature F) {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    {input output} (op : Operation E.signature 1 (fun _ => input) output)
    (a a' : Expr) (related : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (value : PackedTerm E Γ) (decoded : unary? source op a = some value) :
    unary? target (Hom.operation f op) a' = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.unary_related (Hom.operation f op) a a' related
  exact unary_transport f (by intro e t h; simp [h]) op a value decoded

theorem implication_syntax (f : environmentSignature E ⟶ environmentSignature F) {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))} (a a' b b' : Expr)
    (ra : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (rb : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target b b')
    (value : PackedTerm E Γ) (decoded : implication? source a b = some value) :
    implication? target a' b' = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.implication_related a a' b b' ra rb
  exact implication_transport f (by intro e t h; simp [h]) a b value decoded

theorem xor_syntax (f : environmentSignature E ⟶ environmentSignature F) {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))} (a a' b b' : Expr)
    (ra : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (rb : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target b b')
    (value : PackedTerm E Γ) (decoded : xor? source a b = some value) :
    xor? target a' b' = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.xor_related a a' b b' ra rb
  exact xor_transport f (by intro e t h; simp [h]) a b value decoded

theorem ite_syntax (f : environmentSignature E ⟶ environmentSignature F) {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))} (c c' a a' b b' : Expr)
    (rc : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target c c')
    (ra : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (rb : Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target b b')
    (value : PackedTerm E Γ) (decoded : ite? source c a b = some value) :
    ite? target c' a' b' = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.ite_related c c' a a' b b' rc ra rb
  exact ite_transport f (by intro e t h; simp [h]) c a b value decoded

theorem fold_syntax (f : environmentSignature E ⟶ environmentSignature F) {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))} {sort}
    (op : Operation E.signature 2 (fun _ => sort) sort) {es outputs : List Expr}
    (related : List.Forall₂ (Uflia.Quantified.SExpr.Renaming.DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : fold? source op es = some value) :
    fold? target (Hom.operation f op) outputs = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.fold_related related (Hom.operation f op)
  exact fold_transport f (by intro e t h; simp [h]) op es value decoded

theorem compare_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (op : Operation E.signature 2 (fun _ => .int) .bool)
    (op' : Operation F.signature 2 (fun _ => .int) .bool)
    (hop : HEq (Hom.operation f op) op') (reverse : Bool) {es outputs : List Expr}
    (related : List.Forall₂ (Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : compare? source op reverse es = some value) :
    compare? target op' reverse outputs = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.compare_related related op' reverse
  exact compare_transport f (by intro e t h; simp [h]) op op' hop reverse es value decoded

theorem equalities_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))} (distinct : Bool) {es outputs : List Expr}
    (related : List.Forall₂ (Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : equalities? source distinct es = some value) :
    equalities? target distinct outputs = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.equalities_related related distinct
  exact equalities_transport f (by intro e t h; simp [h]) distinct es value decoded

theorem multiply_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))} {es outputs : List Expr}
    (related : List.Forall₂ (Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : multiply? source es = some value) :
    multiply? target outputs = some (mapPacked f value) := by
  apply Uflia.Quantified.SExpr.Renaming.multiply_related related
  exact multiply_transport f (by intro e t h; simp [h]) es value decoded

theorem unary_at_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 1 (fun _ => input) output)
    (op' : Operation F.signature 1 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op')
    (e output : Expr)
    (related : Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target e output) (t : PackedTerm E Γ) (h : unary? source op e = some t) :
    unary? target op' output = some (mapPacked f t) := by
  apply Uflia.Quantified.SExpr.Renaming.unary_related op' e output related
  exact unary_at_transport f (by intro e t h; simp [h]) hs ht op op' hop e t h

theorem binary_at_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 2 (fun _ => input) output)
    (op' : Operation F.signature 2 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op')
    (a a' b b' : Expr)
    (ra : Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target a a')
    (rb : Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target b b') (t : PackedTerm E Γ) (h : binary? source op a b = some t) :
    binary? target op' a' b' = some (mapPacked f t) := by
  apply Uflia.Quantified.SExpr.Renaming.binary_related op' a a' b b' ra rb
  exact binary_at_transport f (by intro e t h; simp [h]) hs ht op op' hop a b t h

theorem fold_at_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    {s t' : SortCode String} (hs : f.sorts s = t')
    (op : Operation E.signature 2 (fun _ => s) s)
    (op' : Operation F.signature 2 (fun _ => t') t')
    (hop : HEq (Hom.operation f op) op')
    (es outputs : List Expr)
    (related : List.Forall₂ (Uflia.Quantified.SExpr.Renaming.DecodeRelated
      (fun e => (source e).map (mapPacked f)) target) es outputs) (t : PackedTerm E Γ) (h : fold? source op es = some t) :
    fold? target op' outputs = some (mapPacked f t) := by
  apply Uflia.Quantified.SExpr.Renaming.fold_related related op'
  exact fold_at_transport f (by intro e t h; simp [h]) hs op op' hop es t h

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
