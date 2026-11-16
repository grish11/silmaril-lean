module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Core.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Normalization.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
open Uflia.SExpr
variable {E F : Environment}

def iteProfile (s : SortCode String) : Fin 3 → SortCode String :=
  Fin.cases .bool (fun _ => s)

/-- Transport a term whose mapped sort has a chosen concrete presentation. -/
def termAt (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (v : Uflia.Term E.signature s) :
    Uflia.Term F.signature t := cast (congrArg (Uflia.Term F.signature) h) (closedTerm f v)

theorem termAt_heq (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (v : Uflia.Term E.signature s) :
    HEq (termAt f h v) (closedTerm f v) := cast_heq _ _

private theorem packed_cast {s t : SortCode String} (h : s = t)
    (v : Uflia.Term F.signature s) :
    (⟨s,v⟩ : PackedTerm F) = ⟨t,cast (congrArg (Uflia.Term F.signature) h) v⟩ := by
  cases h
  rfl

theorem mapPacked_at (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (v : Uflia.Term E.signature s) :
    mapPacked f ⟨s,v⟩ = ⟨t,termAt f h v⟩ := packed_cast h _

private theorem app_heq {n : Nat} {ss tt : Fin n → SortCode String}
    {s t : SortCode String} (hs : ss = tt) (ht : s = t)
    (op : Operation F.signature n ss s) (op' : Operation F.signature n tt t)
    (hop : HEq op op') (args : ∀ i, Uflia.Term F.signature (ss i))
    (args' : ∀ i, Uflia.Term F.signature (tt i))
    (ha : ∀ i, HEq (args i) (args' i)) :
    HEq (ManySorted.Term.app op args) (ManySorted.Term.app op' args') := by
  cases hs
  cases ht
  cases eq_of_heq hop
  exact heq_of_eq (congrArg (ManySorted.Term.app op) (funext (fun i => eq_of_heq (ha i))))

theorem termAt_app (f : environmentSignature E ⟶ environmentSignature F)
    {n : Nat} {ss tt : Fin n → SortCode String} {s t : SortCode String}
    (hs : ∀ i, f.sorts (ss i) = tt i) (ht : f.sorts s = t)
    (op : Operation E.signature n ss s) (op' : Operation F.signature n tt t)
    (hop : HEq (Hom.operation f op) op')
    (args : ∀ i, Uflia.Term E.signature (ss i)) :
    termAt f ht (.app op args) = .app op' (fun i => termAt f (hs i) (args i)) := by
  apply eq_of_heq
  apply (termAt_heq f ht _).trans
  rw [closedTerm_app]
  exact app_heq (funext hs) ht _ _ hop _ _ (fun i => (termAt_heq f (hs i) _).symm)

theorem typedTerms_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (sort : SortCode String) (es : List Expr) (ts : List (Uflia.Term E.signature sort))
    (h : typedTerms? source sort es = some ts) :
    typedTerms? target (f.sorts sort) es = some (ts.map (closedTerm f)) := by
  unfold Uflia.SExpr.typedTerms? at h ⊢
  rw [List.mapM_eq_some_iff_forall₂] at h ⊢
  induction h with
  | nil => exact .nil
  | @cons e t es ts head tail ih =>
      apply List.Forall₂.cons ?_ ih
      obtain ⟨v,hv,ht⟩ := Option.bind_eq_some_iff.mp head
      change (target e).bind _ = some (closedTerm f t)
      rw [hfg e v hv]
      exact expect_mapPacked_of_eq f v t ht

theorem typedTerms_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {s t : SortCode String} (hs : f.sorts s = t)
    (es : List Expr) (ts : List (Uflia.Term E.signature s))
    (h : typedTerms? source s es = some ts) :
    typedTerms? target t es = some (ts.map (termAt f hs)) := by
  cases hs
  exact typedTerms_transport f hfg s es ts h

theorem unary_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output)
    (e : Expr) (t : PackedTerm E) (h : unary? source op e = some t) :
    unary? target (Hom.operation f op) e = some (mapPacked f t) := by
  obtain ⟨v,hv,a,ha,rfl⟩ : ∃ v, source e = some v ∧ ∃ a,
      v.expect? input = some a ∧ (⟨output,.app op (fun _ => a)⟩ : PackedTerm E) = t := by
    simpa [unary?, Option.bind_eq_some_iff] using h
  simp only [unary?, bind, pure, hfg e v hv, Option.bind_some,
    expect_mapPacked_of_eq f v a ha]
  change some (⟨_,_⟩ : PackedTerm F) = some (⟨_,_⟩ : PackedTerm F)
  rw [closedTerm_app]

theorem binary_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output)
    (a b : Expr) (t : PackedTerm E) (h : binary? source op a b = some t) :
    binary? target (Hom.operation f op) a b = some (mapPacked f t) := by
  obtain ⟨va,hva,ta,hta,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ ta, va.expect? input = some ta ∧
      ∃ vb, source b = some vb ∧ ∃ tb, vb.expect? input = some tb ∧
        (⟨output,.app op (Fin.cases ta (fun _ => tb))⟩ : PackedTerm E) = t := by
    simpa [binary?, Option.bind_eq_some_iff] using h
  simp only [binary?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_mapPacked_of_eq f va ta hta, expect_mapPacked_of_eq f vb tb htb]
  change some (⟨_,_⟩ : PackedTerm F) = some (⟨_,_⟩ : PackedTerm F)
  congr 2
  rw [closedTerm_app]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem foldTerms_map (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (op : Operation E.signature 2 (fun _ => s) s)
    (a : Uflia.Term E.signature s) (ts : List (Uflia.Term E.signature s)) :
    closedTerm f (foldTerms op a ts) =
      foldTerms (Hom.operation f op) (closedTerm f a) (ts.map (closedTerm f)) := by
  induction ts generalizing a with
  | nil => rfl
  | cons b ts ih =>
      simp only [foldTerms, List.foldl_cons, List.map_cons] at ih ⊢
      rw [ih]
      congr 1
      change closedTerm f (.app op _) = .app (Hom.operation f op) _
      rw [closedTerm_app]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem fold_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {s : SortCode String} (op : Operation E.signature 2 (fun _ => s) s)
    (es : List Expr) (t : PackedTerm E) (h : fold? source op es = some t) :
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
                (⟨s,foldTerms op a ts⟩ : PackedTerm E) = t := by
            simpa [fold?, Option.bind_eq_some_iff] using h
          simp only [fold?, bind, pure, hfg _ v hv, Option.bind_some, expect_mapPacked_of_eq f v a ha,
            typedTerms_transport f hfg s (b :: rest) ts hts]
          exact congrArg (fun x => some (⟨f.sorts s,x⟩ : PackedTerm F))
            (foldTerms_map f op a ts).symm


theorem unary_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 1 (fun _ => input) output)
    (op' : Operation F.signature 1 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op')
    (e : Expr) (t : PackedTerm E) (h : unary? source op e = some t) :
    unary? target op' e = some (mapPacked f t) := by
  cases hs
  cases ht
  cases eq_of_heq hop
  exact unary_transport f hfg op e t h

theorem binary_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 2 (fun _ => input) output)
    (op' : Operation F.signature 2 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op')
    (a b : Expr) (t : PackedTerm E) (h : binary? source op a b = some t) :
    binary? target op' a b = some (mapPacked f t) := by
  cases hs
  cases ht
  cases eq_of_heq hop
  exact binary_transport f hfg op a b t h

theorem fold_at_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {s t' : SortCode String} (hs : f.sorts s = t')
    (op : Operation E.signature 2 (fun _ => s) s)
    (op' : Operation F.signature 2 (fun _ => t') t')
    (hop : HEq (Hom.operation f op) op')
    (es : List Expr) (t : PackedTerm E) (h : fold? source op es = some t) :
    fold? target op' es = some (mapPacked f t) := by
  cases hs
  cases eq_of_heq hop
  exact fold_transport f hfg op es t h

theorem expect_at (f : environmentSignature E ⟶ environmentSignature F)
    (v : PackedTerm E) {s t : SortCode String} (hs : f.sorts s = t)
    (a : Uflia.Term E.signature s) (h : v.expect? s = some a) :
    (mapPacked f v).expect? t = some (termAt f hs a) := by
  cases hs
  exact expect_mapPacked_of_eq f v a h

abbrev boolTerm (f : environmentSignature E ⟶ environmentSignature F)
    (p : Formula E.signature) : Formula F.signature := termAt f f.bool p
abbrev intTerm (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Term E.signature .int) : Uflia.Term F.signature .int := termAt f f.int p

theorem mapPacked_bool (f : environmentSignature E ⟶ environmentSignature F)
    (p : Formula E.signature) : mapPacked f ⟨.bool,p⟩ = ⟨.bool,boolTerm f p⟩ :=
  mapPacked_at f f.bool p

theorem mapPacked_int (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Term E.signature .int) : mapPacked f ⟨.int,p⟩ = ⟨.int,intTerm f p⟩ :=
  mapPacked_at f f.int p

private theorem unary_at (f : environmentSignature E ⟶ environmentSignature F)
    {a b s t : SortCode String} (ha : f.sorts a = b) (hs : f.sorts s = t)
    (op : Operation E.signature 1 (fun _ => a) s)
    (op' : Operation F.signature 1 (fun _ => b) t)
    (hop : HEq (Hom.operation f op) op') (v : Uflia.Term E.signature a) :
    termAt f hs (.app op (fun _ => v)) = .app op' (fun _ => termAt f ha v) :=
  termAt_app f (fun _ => ha) hs op op' hop _

private theorem binary_at (f : environmentSignature E ⟶ environmentSignature F)
    {a b s t : SortCode String} (ha : f.sorts a = b) (hs : f.sorts s = t)
    (op : Operation E.signature 2 (fun _ => a) s)
    (op' : Operation F.signature 2 (fun _ => b) t)
    (hop : HEq (Hom.operation f op) op') (v w : Uflia.Term E.signature a) :
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
    (p : Formula E.signature) :
    boolTerm f (.app .not (fun _ => p)) = .app .not (fun _ => boolTerm f p) :=
  unary_at f f.bool f.bool .not .not (operation_not_heq f) p

theorem boolTerm_or (f : environmentSignature E ⟶ environmentSignature F)
    (p q : Formula E.signature) :
    boolTerm f (.app .or (Fin.cases p (fun _ => q))) =
      .app .or (Fin.cases (boolTerm f p) (fun _ => boolTerm f q)) :=
  binary_at f f.bool f.bool .or .or (operation_or_heq f) p q

theorem boolTerm_and (f : environmentSignature E ⟶ environmentSignature F)
    (p q : Formula E.signature) :
    boolTerm f (.app .and (Fin.cases p (fun _ => q))) =
      .app .and (Fin.cases (boolTerm f p) (fun _ => boolTerm f q)) :=
  binary_at f f.bool f.bool .and .and (operation_and_heq f) p q

theorem boolTerm_eq (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (p q : Uflia.Term E.signature s) :
    boolTerm f (.app (.eq s) (Fin.cases p (fun _ => q))) =
      .app (.eq (f.sorts s)) (Fin.cases (closedTerm f p) (fun _ => closedTerm f q)) :=
  binary_at f rfl f.bool (.eq s) (.eq (f.sorts s)) (operation_eq_heq f s) p q

theorem boolTerm_boolean (f : environmentSignature E ⟶ environmentSignature F) (b : Bool) :
    boolTerm f (Uflia.Term.boolean b) = Uflia.Term.boolean b := by
  rw [show Uflia.Term.boolean (A := E.signature) b =
    .app (.boolean b) (fun i => i.elim0) from rfl]
  apply Eq.trans (termAt_app f (fun i : Fin 0 => i.elim0) f.bool (.boolean b) (.boolean b)
    (operation_boolean_heq f b) (fun i => i.elim0))
  congr 1
  funext i
  exact i.elim0

theorem intTerm_integer (f : environmentSignature E ⟶ environmentSignature F) (n : Int) :
    intTerm f (Uflia.Term.integer n) = Uflia.Term.integer n := by
  rw [show Uflia.Term.integer (A := E.signature) n =
    .app (.integer n) (fun i => i.elim0) from rfl]
  apply Eq.trans (termAt_app f (fun i : Fin 0 => i.elim0) f.int (.integer n) (.integer n)
    (operation_integer_heq f n) (fun i => i.elim0))
  congr 1
  funext i
  exact i.elim0

theorem implication_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E) (h : implication? source a b = some t) :
    implication? target a b = some (mapPacked f t) := by
  obtain ⟨va,hva,ta,hta,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ ta, va.expect? .bool = some ta ∧
      ∃ vb, source b = some vb ∧ ∃ tb, vb.expect? .bool = some tb ∧
        (⟨.bool,.app .or (Fin.cases (.app .not (fun _ => ta)) (fun _ => tb))⟩ : PackedTerm E) = t := by
    simpa [implication?, Option.bind_eq_some_iff] using h
  simp only [implication?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_at f va f.bool ta hta, expect_at f vb f.bool tb htb]
  rw [mapPacked_bool f, boolTerm_or f, boolTerm_not f]

theorem xor_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E) (h : xor? source a b = some t) :
    xor? target a b = some (mapPacked f t) := by
  obtain ⟨va,hva,ta,hta,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ ta, va.expect? .bool = some ta ∧
      ∃ vb, source b = some vb ∧ ∃ tb, vb.expect? .bool = some tb ∧
        (⟨.bool,.app .not (fun _ => .app (.eq .bool) (Fin.cases ta (fun _ => tb)))⟩ : PackedTerm E) = t := by
    simpa [xor?, Option.bind_eq_some_iff] using h
  simp only [xor?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_at f va f.bool ta hta, expect_at f vb f.bool tb htb]
  rw [mapPacked_bool f, boolTerm_not f, boolTerm_eq f]
  have eqmap :
      (ManySorted.Term.app (.eq (f.sorts .bool))
        (Fin.cases (closedTerm f ta) (fun _ => closedTerm f tb)) :
          Uflia.Term F.signature .bool) =
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

theorem closedTerm_ite (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (c : Formula E.signature) (a b : Uflia.Term E.signature s) :
    closedTerm f (.app (.ite s) (Fin.cases c (Fin.cases a (fun _ => b)))) =
      .app (.ite (f.sorts s))
        (Fin.cases (boolTerm f c) (Fin.cases (closedTerm f a) (fun _ => closedTerm f b))) := by
  have hs : ∀ i, f.sorts (iteProfile s i) =
      iteProfile (f.sorts s) i :=
    fun i => Fin.cases f.bool (fun _ => rfl) i
  have h := termAt_app f hs rfl (.ite s) (.ite (f.sorts s)) (operation_ite_heq f s)
    (show ∀ i, Uflia.Term E.signature (iteProfile s i) from
      Fin.cases c (Fin.cases a (fun _ => b)))
  change closedTerm f _ = _ at h
  rw [h]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

theorem ite_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (c a b : Expr) (t : PackedTerm E) (h : ite? source c a b = some t) :
    ite? target c a b = some (mapPacked f t) := by
  obtain ⟨vc,hvc,tc,htc,va,hva,vb,hvb,tb,htb,rfl⟩ :
      ∃ vc, source c = some vc ∧ ∃ tc, vc.expect? .bool = some tc ∧
      ∃ va, source a = some va ∧ ∃ vb, source b = some vb ∧
      ∃ tb, vb.expect? va.sort = some tb ∧
        (⟨va.sort,.app (.ite va.sort) (Fin.cases tc (Fin.cases va.term (fun _ => tb)))⟩ : PackedTerm E) = t := by
    simpa [ite?, Option.bind_eq_some_iff] using h
  simp only [ite?, bind, pure, hfg c vc hvc, hfg a va hva, hfg b vb hvb, Option.bind_some,
    expect_at f vc f.bool tc htc, mapPacked_sort,
    expect_mapPacked_of_eq f vb tb htb]
  exact congrArg (fun x => some (⟨f.sorts va.sort,x⟩ : PackedTerm F))
    (closedTerm_ite f tc va.term tb).symm

theorem equality_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E) (h : equality? source a b = some t) :
    equality? target a b = some (mapPacked f t) := by
  obtain ⟨va,hva,vb,hvb,tb,htb,rfl⟩ :
      ∃ va, source a = some va ∧ ∃ vb, source b = some vb ∧
      ∃ tb, vb.expect? va.sort = some tb ∧
        (⟨.bool,.app (.eq va.sort) (Fin.cases va.term (fun _ => tb))⟩ : PackedTerm E) = t := by
    simpa [equality?, Option.bind_eq_some_iff] using h
  simp only [equality?, bind, pure, hfg a va hva, hfg b vb hvb, Option.bind_some,
    mapPacked_sort, expect_mapPacked_of_eq f vb tb htb]
  change some (⟨.bool,.app (.eq (f.sorts va.sort))
    (Fin.cases (closedTerm f va.term) (fun _ => closedTerm f tb))⟩ : PackedTerm F) = _
  rw [mapPacked_bool f, boolTerm_eq f]

theorem foldTerms_at_map (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (hs : f.sorts s = t)
    (op : Operation E.signature 2 (fun _ => s) s)
    (op' : Operation F.signature 2 (fun _ => t) t)
    (hop : HEq (Hom.operation f op) op')
    (a : Uflia.Term E.signature s) (ts : List (Uflia.Term E.signature s)) :
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
    (ts : List (Formula E.signature)) :
    boolTerm f (conjunction ts) = conjunction (ts.map (boolTerm f)) := by
  cases ts with
  | nil => exact boolTerm_boolean f true
  | cons a ts => exact foldTerms_at_map f f.bool .and .and (operation_and_heq f) a ts

theorem compare_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (op : Operation E.signature 2 (fun _ => .int) .bool)
    (op' : Operation F.signature 2 (fun _ => .int) .bool)
    (hop : HEq (Hom.operation f op) op') (reverse : Bool)
    (es : List Expr) (t : PackedTerm E) (h : compare? source op reverse es = some t) :
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
          change some (⟨.bool,_⟩ : PackedTerm F) = some (mapPacked f ⟨.bool,_⟩)
          rw [mapPacked_bool f, conjunction_map f]
          congr 2
          apply Eq.symm
          apply congrArg conjunction
          apply Uflia.SExpr.Renaming.adjacent_transport (intTerm f) (boolTerm f)
          intro x y
          cases reverse <;> exact binary_at f f.int f.bool op op' hop _ _

theorem equalities_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (distinct : Bool) (es : List Expr) (t : PackedTerm E)
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
          change some (⟨.bool,_⟩ : PackedTerm F) = some (mapPacked f ⟨.bool,_⟩)
          rw [mapPacked_bool f, conjunction_map f]
          congr 2
          have heq (x y : Uflia.Term E.signature va.sort) := boolTerm_eq f x y
          have hnot (x y : Uflia.Term E.signature va.sort) :
              boolTerm f (.app .not (fun _ =>
                .app (.eq va.sort) (Fin.cases x (fun _ => y)))) =
              .app .not (fun _ => .app (.eq (f.sorts va.sort))
                (Fin.cases (closedTerm f x) (fun _ => closedTerm f y))) := by
            rw [boolTerm_not f, boolTerm_eq f]
          cases distinct with
          | false =>
              apply congrArg conjunction
              simpa only [Bool.false_eq_true, reduceIte, List.map_cons, mapPacked] using
                (Uflia.SExpr.Renaming.adjacent_transport (closedTerm f) (boolTerm f)
                  (fun x y => .app (.eq va.sort) (Fin.cases x (fun _ => y)))
                  (fun x y => .app (.eq (f.sorts va.sort)) (Fin.cases x (fun _ => y)))
                  heq (va.term :: ts)).symm
          | true =>
              apply congrArg conjunction
              simpa only [reduceIte, List.map_cons, mapPacked] using
                (Uflia.SExpr.Renaming.allPairs_transport (closedTerm f) (boolTerm f)
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
    (a : Uflia.Term F.signature s) (b : Uflia.Term F.signature t) (h : HEq a b) :
    integerValue? a = integerValue? b := by
  cases hs
  cases eq_of_heq h
  rfl

private theorem integerValue_at (f : environmentSignature E ⟶ environmentSignature F)
    {s t : SortCode String} (h : f.sorts s = t) (a : Uflia.Term E.signature s) :
    integerValue? (closedTerm f a) = integerValue? (termAt f h a) :=
  integerValue_heq h _ _ (termAt_heq f h a).symm

private theorem integerValue_uf {E : Environment} {n : Nat}
    {ss : Fin n → SortCode String} {s : SortCode String}
    (symbol : E.signature.operations n ss s) (args : ∀ i, Uflia.Term E.signature (ss i)) :
    integerValue? (E := E) (.app (.uf symbol) args) = none := by
  cases n with
  | zero => cases s <;> rfl
  | succ n =>
      cases n with
      | zero => cases s <;> rfl
      | succ n => cases s <;> rfl

private theorem integerValue_ite {E : Environment} {s : SortCode String}
    (args : ∀ i, Uflia.Term E.signature (iteProfile s i)) :
    integerValue? (E := E) (.app (.ite s) args) = none := by
  cases s <;> rfl

/-- Literal recognition retains the constructor test, including nested scaling. -/
theorem integerValue_map (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (t : Uflia.Term E.signature s) :
    integerValue? (closedTerm f t) = integerValue? t := by
  induction t with
  | var i => exact i.elim0
  | app op args ih =>
      cases op with
      | uf symbol =>
          rw [closedTerm_app]
          simp only [Hom.operation, integerValue_uf]
      | integer n =>
          have ha : args = (fun i => i.elim0) := funext (fun i => i.elim0)
          subst args
          rw [integerValue_at f f.int]
          change integerValue? (intTerm f (Uflia.Term.integer n)) = some n
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
          rw [ha, closedTerm_ite]
          simp only [integerValue_ite]


theorem intTerm_scale (f : environmentSignature E ⟶ environmentSignature F)
    (c : Int) (p : Uflia.Term E.signature .int) :
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
    (args : ∀ i, Uflia.Term E.signature (ss i)) :
    intTerm f (.app (.uf symbol) args) =
      .app (.uf (cast (congrArg (F.signature.operations n (f.sorts ∘ ss)) f.int)
        (f.operations symbol))) (fun i => closedTerm f (args i)) :=
  termAt_app f (fun _ => rfl) f.int (.uf symbol) _
    (uf_cast_heq f.int (f.operations symbol)) args

private theorem intTerm_ite (f : environmentSignature E ⟶ environmentSignature F)
    (args : ∀ i, Uflia.Term E.signature (iteProfile .int i)) :
    intTerm f (.app (.ite .int) args) =
      .app (.ite .int) (fun i => termAt f
        (show f.sorts (iteProfile .int i) =
          iteProfile .int i from
            Fin.cases f.bool (fun _ => f.int) i) (args i)) :=
  termAt_app f (fun i => Fin.cases f.bool (fun _ => f.int) i) f.int (.ite .int) (.ite .int)
    ((operation_ite_heq f .int).trans (ite_sort_heq f.int)) args

private theorem scaleLinear_uf {E : Environment} {n : Nat}
    {ss : Fin n → SortCode String} (symbol : E.signature.operations n ss .int)
    (args : ∀ i, Uflia.Term E.signature (ss i)) (c : Int) :
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

private theorem scaleLinear_int_aux (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (t : Uflia.Term E.signature s) (coefficient : Int) :
    ∀ h : s = .int,
      intTerm f (cast (congrArg (Uflia.Term E.signature) h) (scaleLinear coefficient t)) =
        scaleLinear coefficient (intTerm f (cast (congrArg (Uflia.Term E.signature) h) t)) := by
  induction t generalizing coefficient with
  | var i => exact i.elim0
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
          change intTerm f (Uflia.Term.integer (coefficient * n)) =
            scaleLinear coefficient (intTerm f (Uflia.Term.integer n))
          rw [intTerm_integer, intTerm_integer]
          rfl
      | add =>
          simp only [cast_eq]
          change intTerm f (.app .add (Fin.cases (scaleLinear coefficient (args 0))
            (fun _ => scaleLinear coefficient (args 1)))) = _
          change termAt f f.int (.app .add _) = scaleLinear coefficient (termAt f f.int (.app .add args))
          rw [binary_at f f.int f.int .add .add (operation_add_heq f),
            termAt_app f (fun _ => f.int) f.int .add .add (operation_add_heq f)]
          change _ = (ManySorted.Term.app Operation.add (Fin.cases _ (fun _ => _)) : Uflia.Term F.signature .int)
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
          change _ = (ManySorted.Term.app Operation.sub (Fin.cases _ (fun _ => _)) : Uflia.Term F.signature .int)
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

theorem scaleLinear_map (f : environmentSignature E ⟶ environmentSignature F)
    (coefficient : Int) (t : Uflia.Term E.signature .int) :
    intTerm f (scaleLinear coefficient t) = scaleLinear coefficient (intTerm f t) :=
  scaleLinear_int_aux f t coefficient rfl

theorem multiplyFactors_map (f : environmentSignature E ⟶ environmentSignature F)
    (ts : List (Uflia.Term E.signature .int)) (coefficient : Int)
    (factor : Option (Uflia.Term E.signature .int)) :
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
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (es : List Expr) (t : PackedTerm E) (h : multiply? source es = some t) :
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
                (⟨.int,term⟩ : PackedTerm E) = t := by
            simpa [multiply?, Option.bind_eq_some_iff] using h
          have hts' : typedTerms? target .int (a :: b :: rest) =
              some (ts.map (intTerm f)) := typedTerms_at_transport f hfg f.int _ ts hts
          change (typedTerms? target .int (a :: b :: rest)).bind _ = _
          rw [hts']
          change (multiplyFactors? (ts.map (intTerm f)) 1 none).bind _ = _
          have hm := multiplyFactors_map f ts 1 none
          simp only [Option.map_none,hterm,Option.map_some] at hm
          rw [hm]
          change some (⟨.int,intTerm f term⟩ : PackedTerm F) = some (mapPacked f ⟨.int,term⟩)
          rw [mapPacked_int f]

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
