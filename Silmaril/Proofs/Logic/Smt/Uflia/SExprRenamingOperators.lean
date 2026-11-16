module

public import Silmaril.Proofs.Logic.Smt.Uflia.SExprRenaming

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
variable {E F : Environment}

/-- Folded operators preserve successful typed recursive results. -/
theorem fold_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort)
    (es : List Expr) (t : PackedTerm E) (h : fold? source op es = some t) :
    fold? target (Operation.map f op) es = some (mapPacked f t) := by
  cases es with
  | nil => simp [fold?] at h
  | cons a es =>
    show fold? target (Operation.map f op) (a :: es) = some (mapPacked f t)
    cases es with
    | nil => simp [fold?] at h
    | cons b rest =>
      show fold? target (Operation.map f op) (a :: b :: rest) = some (mapPacked f t)
      change (source a).bind _ = some t at h
      obtain ⟨va, hva, h⟩ := Option.bind_eq_some_iff.mp h
      change (va.expect? sort).bind _ = some t at h
      obtain ⟨ta, hta, h⟩ := Option.bind_eq_some_iff.mp h
      change (typedTerms? source sort (b :: rest)).bind _ = some t at h
      obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
      have ht : _ = t := Option.some.inj h
      subst t
      have hts' : typedTerms? target sort (b :: rest) =
          some (ts.map (Uflia.Term.map f)) :=
        typedTerms_transport f hfg sort (b :: rest) ts hts
      change (target a).bind _ = _
      rw [hfg a va hva]
      change ((mapPacked f va).expect? sort).bind _ = _
      rw [expect_mapPacked, hta]
      change (typedTerms? target sort (b :: rest)).bind _ = _
      rw [hts']
      exact congrArg (fun term => some (⟨sort, term⟩ : PackedTerm F))
        (foldTerms_map f op ta ts).symm

/-- Chained comparisons preserve their chosen orientation and adjacency order. -/
theorem compare_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool)
    (es : List Expr) (t : PackedTerm E) (h : compare? source op reverse es = some t) :
    compare? target (Operation.map f op) reverse es = some (mapPacked f t) := by
  cases es with
  | nil => simp [compare?] at h
  | cons a es =>
    show compare? target (Operation.map f op) reverse (a :: es) = some (mapPacked f t)
    cases es with
    | nil => simp [compare?] at h
    | cons b rest =>
      show compare? target (Operation.map f op) reverse (a :: b :: rest) = some (mapPacked f t)
      change (typedTerms? source .int (a :: b :: rest)).bind _ = some t at h
      obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
      have ht : _ = t := Option.some.inj h
      subst t
      have hts' : typedTerms? target .int (a :: b :: rest) =
          some (ts.map (Uflia.Term.map f)) :=
        typedTerms_transport f hfg .int (a :: b :: rest) ts hts
      change (typedTerms? target .int (a :: b :: rest)).bind _ = _
      rw [hts']
      change some (⟨.bool, _⟩ : PackedTerm F) = some (⟨.bool, _⟩ : PackedTerm F)
      congr 2
      rw [conjunction_map, adjacent_transport (Uflia.Term.map f) (Uflia.Term.map f)]
      intro x y
      cases reverse <;> exact map_binary f op _ _

/-- Pairwise distinctness and adjacent equality commute with typed transport. -/
theorem equalities_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (distinct : Bool) (es : List Expr) (t : PackedTerm E)
    (h : equalities? source distinct es = some t) :
    equalities? target distinct es = some (mapPacked f t) := by
  cases es with
  | nil => simp [equalities?] at h
  | cons a es =>
    show equalities? target distinct (a :: es) = some (mapPacked f t)
    cases es with
    | nil => simp [equalities?] at h
    | cons b rest =>
      show equalities? target distinct (a :: b :: rest) = some (mapPacked f t)
      change (source a).bind _ = some t at h
      obtain ⟨va, hva, h⟩ := Option.bind_eq_some_iff.mp h
      change (typedTerms? source va.sort (b :: rest)).bind _ = some t at h
      obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
      have ht : _ = t := Option.some.inj h
      subst t
      have hts' : typedTerms? target va.sort (b :: rest) =
          some (ts.map (Uflia.Term.map f)) :=
        typedTerms_transport f hfg va.sort (b :: rest) ts hts
      change (target a).bind _ = _
      rw [hfg a va hva]
      change (typedTerms? target va.sort (b :: rest)).bind _ = _
      rw [hts']
      change some (⟨.bool, _⟩ : PackedTerm F) = some (⟨.bool, _⟩ : PackedTerm F)
      congr 2
      rw [conjunction_map]
      have heq (x y : Uflia.Term E.signature va.sort) :
          Uflia.Term.map f (.app (.eq va.sort) (Fin.cases x (fun _ => y))) =
            .app (.eq va.sort) (Fin.cases (Uflia.Term.map f x) (fun _ => Uflia.Term.map f y)) :=
        map_binary f (.eq va.sort) x y
      cases distinct with
      | false =>
        show conjunction _ = conjunction _
        simp only [Bool.false_eq_true, ↓reduceIte, mapPacked]
        apply congrArg conjunction
        simpa only [List.map_cons] using
          (adjacent_transport
            (fun x : Uflia.Term E.signature va.sort => Uflia.Term.map f x)
            (fun x : Formula E.signature => Uflia.Term.map f x)
            (fun x y => .app (.eq va.sort) (Fin.cases x (fun _ => y)))
            (fun x y => .app (.eq va.sort) (Fin.cases x (fun _ => y)))
            heq (va.term :: ts)).symm
      | true =>
        show conjunction _ = conjunction _
        simp only [↓reduceIte, mapPacked]
        apply congrArg conjunction
        have hnot (x y : Uflia.Term E.signature va.sort) :
            Uflia.Term.map f (.app .not (fun _ =>
              .app (.eq va.sort) (Fin.cases x (fun _ => y)))) =
              .app .not (fun _ => .app (.eq va.sort)
                (Fin.cases (Uflia.Term.map f x) (fun _ => Uflia.Term.map f y))) := by
          simp only [Uflia.Term.map, ManySorted.Term.map, Signature.expandMap, Operation.map]
          congr 1
          funext i
          exact Fin.cases (heq x y) (fun j => Fin.elim0 j) i
        apply Eq.symm
        apply allPairs_transport (Uflia.Term.map f) (Uflia.Term.map f)
        exact hnot

/-- The normalized implication retains negation on its first argument. -/
theorem implication_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E) (h : implication? source a b = some t) :
    implication? target a b = some (mapPacked f t) := by
  change (source a).bind _ = some t at h
  obtain ⟨va, hva, h⟩ := Option.bind_eq_some_iff.mp h
  change (va.expect? .bool).bind _ = some t at h
  obtain ⟨ta, hta, h⟩ := Option.bind_eq_some_iff.mp h
  change (source b).bind _ = some t at h
  obtain ⟨vb, hvb, h⟩ := Option.bind_eq_some_iff.mp h
  change (vb.expect? .bool).bind _ = some t at h
  obtain ⟨tb, htb, h⟩ := Option.bind_eq_some_iff.mp h
  have ht : _ = t := Option.some.inj h
  subst t
  change (target a).bind _ = _
  rw [hfg a va hva]
  change (((mapPacked f va).expect? .bool)).bind _ = _
  rw [expect_mapPacked, hta]
  change (target b).bind _ = _
  rw [hfg b vb hvb]
  change (((mapPacked f vb).expect? .bool)).bind _ = _
  rw [expect_mapPacked, htb]
  change some (⟨_, _⟩ : PackedTerm F) = some (⟨_, _⟩ : PackedTerm F)
  congr 2
  simp only [Uflia.Term.map, ManySorted.Term.map, Signature.expandMap, Operation.map]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

/-- Exclusive-or retains its equality-then-negation elaboration. -/
theorem xor_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (a b : Expr) (t : PackedTerm E) (h : xor? source a b = some t) :
    xor? target a b = some (mapPacked f t) := by
  change (source a).bind _ = some t at h
  obtain ⟨va, hva, h⟩ := Option.bind_eq_some_iff.mp h
  change (va.expect? .bool).bind _ = some t at h
  obtain ⟨ta, hta, h⟩ := Option.bind_eq_some_iff.mp h
  change (source b).bind _ = some t at h
  obtain ⟨vb, hvb, h⟩ := Option.bind_eq_some_iff.mp h
  change (vb.expect? .bool).bind _ = some t at h
  obtain ⟨tb, htb, h⟩ := Option.bind_eq_some_iff.mp h
  have ht : _ = t := Option.some.inj h
  subst t
  change (target a).bind _ = _
  rw [hfg a va hva]
  change (((mapPacked f va).expect? .bool)).bind _ = _
  rw [expect_mapPacked, hta]
  change (target b).bind _ = _
  rw [hfg b vb hvb]
  change (((mapPacked f vb).expect? .bool)).bind _ = _
  rw [expect_mapPacked, htb]
  change some (⟨_, _⟩ : PackedTerm F) = some (⟨_, _⟩ : PackedTerm F)
  congr 2
  simp only [Uflia.Term.map, ManySorted.Term.map, Signature.expandMap, Operation.map]
  congr 1
  funext i
  congr 1
  funext j
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j

/-- Conditional elaboration preserves the condition and both dependent branches. -/
theorem ite_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (c a b : Expr) (t : PackedTerm E) (h : ite? source c a b = some t) :
    ite? target c a b = some (mapPacked f t) := by
  change (source c).bind _ = some t at h
  obtain ⟨vc, hvc, h⟩ := Option.bind_eq_some_iff.mp h
  change (vc.expect? .bool).bind _ = some t at h
  obtain ⟨tc, htc, h⟩ := Option.bind_eq_some_iff.mp h
  change (source a).bind _ = some t at h
  obtain ⟨va, hva, h⟩ := Option.bind_eq_some_iff.mp h
  change (source b).bind _ = some t at h
  obtain ⟨vb, hvb, h⟩ := Option.bind_eq_some_iff.mp h
  change (vb.expect? va.sort).bind _ = some t at h
  obtain ⟨tb, htb, h⟩ := Option.bind_eq_some_iff.mp h
  have ht : _ = t := Option.some.inj h
  subst t
  change (target c).bind _ = _
  rw [hfg c vc hvc]
  change (((mapPacked f vc).expect? .bool)).bind _ = _
  rw [expect_mapPacked, htc]
  change (target a).bind _ = _
  rw [hfg a va hva]
  change (target b).bind _ = _
  rw [hfg b vb hvb]
  change (((mapPacked f vb).expect? va.sort)).bind _ = _
  rw [expect_mapPacked, htb]
  change some (⟨_, _⟩ : PackedTerm F) = some (⟨_, _⟩ : PackedTerm F)
  congr 2
  simp only [Uflia.Term.map, ManySorted.Term.map, Signature.expandMap, Operation.map]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl
    (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i

/-- Multiplication transports the actual coefficient normalization and restriction
of at most one nonliteral factor, rather than only its semantic value. -/
theorem multiply_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (es : List Expr) (t : PackedTerm E) (h : multiply? source es = some t) :
    multiply? target es = some (mapPacked f t) := by
  cases es with
  | nil => simp [multiply?] at h
  | cons a es =>
    show multiply? target (a :: es) = some (mapPacked f t)
    cases es with
    | nil => simp [multiply?] at h
    | cons b rest =>
      show multiply? target (a :: b :: rest) = some (mapPacked f t)
      change (typedTerms? source .int (a :: b :: rest)).bind _ = some t at h
      obtain ⟨ts, hts, h⟩ := Option.bind_eq_some_iff.mp h
      change (multiplyFactors? ts 1 none).bind _ = some t at h
      obtain ⟨term, hterm, h⟩ := Option.bind_eq_some_iff.mp h
      have ht : _ = t := Option.some.inj h
      subst t
      have hts' : typedTerms? target .int (a :: b :: rest) =
          some (ts.map (Uflia.Term.map f)) :=
        typedTerms_transport f hfg .int (a :: b :: rest) ts hts
      change (typedTerms? target .int (a :: b :: rest)).bind _ = _
      rw [hts']
      change (multiplyFactors? (ts.map (Uflia.Term.map f)) 1 none).bind _ = _
      have hm : multiplyFactors? (ts.map (Uflia.Term.map f)) 1 none =
          (multiplyFactors? ts 1 none).map (Uflia.Term.map f) :=
        multiplyFactors_map f ts 1 none
      simp only [hterm, Option.map_some] at hm
      rw [hm]
      rfl

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
