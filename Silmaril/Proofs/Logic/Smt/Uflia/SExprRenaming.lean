module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Thms
public import Batteries.Data.List.Lemmas
public import Mathlib.Data.List.OfFn

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
variable {E F : Environment}

/-- Successful-result refinement is enough for fuel growth; rejected inputs
need not remain rejected when more fuel becomes available. -/
def Refines {α β : Type} (f g : α → Option β) : Prop :=
  ∀ a b, f a = some b → g a = some b

/-- Sequence successful recursive results without assuming rejection equality. -/
theorem mapM_refines {α β : Type} {f g : α → Option β}
    (hfg : Refines f g) (as : List α) (bs : List β)
    (h : as.mapM f = some bs) : as.mapM g = some bs := by
  rw [List.mapM_eq_some_iff_forall₂] at h ⊢
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab htail ih => exact .cons (hfg a b hab) ih

/-- Sort-checked list decoding preserves every successful result under a
successful recursive refinement. This is the list case of decoder fuel growth. -/
theorem typedTerms_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (sort : SortCode String) (es : List Expr)
    (ts : List (Uflia.Term E.signature sort))
    (h : typedTerms? f sort es = some ts) : typedTerms? g sort es = some ts := by
  apply mapM_refines (as := es) (bs := ts) ?_ h
  intro e t ht
  change (f e).bind (fun value => value.expect? sort) = some t at ht
  change (g e).bind (fun value => value.expect? sort) = some t
  cases hv : f e with
  | none => simp [hv] at ht
  | some value => simpa only [hfg e value hv, hv, Option.bind_some] using ht

/-- Arity- and sort-checked UF arguments also preserve successful recursive
results. Dependent argument functions are retained, not compared by evaluation. -/
theorem decodeArguments_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (inputs : List (SortCode String)) :
    ∀ (es : List Expr) (ts : (i : Fin inputs.length) →
      Uflia.Term E.signature (inputs.get i)),
      decodeArguments? f inputs es = some ts →
      decodeArguments? g inputs es = some ts := by
  induction inputs with
  | nil =>
      intro es ts h
      cases es with
      | nil => simpa only [decodeArguments?] using h
      | cons e es => simp [decodeArguments?] at h
  | cons input inputs ih =>
      intro es ts h
      cases es with
      | nil => simp [decodeArguments?] at h
      | cons e es =>
          simp [decodeArguments?, Option.bind_eq_some_iff] at h ⊢
          obtain ⟨value, hv, term, ht, tail, htail, rfl⟩ := h
          exact ⟨value, hfg e value hv, term, ht, tail, ih es tail htail, rfl⟩

/-- Successful UF application only depends on successful argument decoding. -/
theorem applyUF_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (name : String) (es : List Expr) (t : PackedTerm E)
    (h : applyUF? E f name es = some t) : applyUF? E g name es = some t := by
  cases hi : lookup? E name with
  | none => simp [applyUF?, hi] at h
  | some i =>
      simp only [applyUF?, hi] at h ⊢
      change (decodeArguments? f (E.declarations.get i).inputs es).bind _ = some t at h
      change (decodeArguments? g (E.declarations.get i).inputs es).bind _ = some t
      cases hs : decodeArguments? f (E.declarations.get i).inputs es with
      | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
      | some ts =>
          simpa only [hs,
            decodeArguments_refines hfg _ es ts hs, Option.bind_some] using h

/-- Unary elaboration preserves a successful recursive refinement. -/
theorem unary_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output) (e : Expr)
    (t : PackedTerm E) (h : unary? f op e = some t) : unary? g op e = some t := by
  cases he : f e with
  | none => simp [unary?, he] at h
  | some ve =>
      simpa only [unary?, he, hfg e ve he, Option.bind_some] using h

/-- Binary elaboration preserves a successful recursive refinement. -/
theorem binary_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr)
    (t : PackedTerm E) (h : binary? f op a b = some t) : binary? g op a b = some t := by
  cases ha : f a with
  | none => simp [binary?, ha] at h
  | some va =>
      cases hb : f b with
      | none => simp [binary?, ha, hb] at h
      | some vb =>
          simpa only [binary?, ha, hb, hfg a va ha, hfg b vb hb, Option.bind_some] using h

/-- Conditional elaboration keeps the branch-dependent sort checks. -/
theorem ite_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (c a b : Expr) (t : PackedTerm E)
    (h : ite? f c a b = some t) : ite? g c a b = some t := by
  cases hc : f c with
  | none => simp [ite?, hc] at h
  | some vc =>
      cases ha : f a with
      | none => simp [ite?, hc, ha] at h
      | some va =>
          cases hb : f b with
          | none => simp [ite?, hc, ha, hb] at h
          | some vb =>
              simpa only [ite?, hc, ha, hb, hfg c vc hc, hfg a va ha, hfg b vb hb, Option.bind_some] using h

/-- Equality elaboration keeps the first operand's inferred sort. -/
theorem equality_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (a b : Expr) (t : PackedTerm E)
    (h : equality? f a b = some t) : equality? g a b = some t := by
  cases ha : f a with
  | none => simp [equality?, ha] at h
  | some va =>
      cases hb : f b with
      | none => simp [equality?, ha, hb] at h
      | some vb =>
          simpa only [equality?, ha, hb, hfg a va ha, hfg b vb hb, Option.bind_some] using h

/-- Boolean elaboration preserves every successful recursive result. -/
theorem implication_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (a b : Expr) (t : PackedTerm E)
    (h : implication? f a b = some t) : implication? g a b = some t := by
  cases ha : f a with
  | none => simp [implication?, ha] at h
  | some va =>
      cases hb : f b with
      | none => simp [implication?, ha, hb] at h
      | some vb =>
          simpa only [implication?, ha, hb, hfg a va ha, hfg b vb hb, Option.bind_some] using h

/-- Boolean elaboration preserves every successful recursive result. -/
theorem xor_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (a b : Expr) (t : PackedTerm E)
    (h : xor? f a b = some t) : xor? g a b = some t := by
  cases ha : f a with
  | none => simp [xor?, ha] at h
  | some va =>
      cases hb : f b with
      | none => simp [xor?, ha, hb] at h
      | some vb =>
          simpa only [xor?, ha, hb, hfg a va ha, hfg b vb hb, Option.bind_some] using h

/-- Typed folds depend only on successful operands. -/
theorem fold_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort) (es : List Expr)
    (t : PackedTerm E) (h : fold? f op es = some t) : fold? g op es = some t := by
  cases es with
  | nil => simp [fold?] at h
  | cons a rest =>
    show fold? g op (a :: rest) = some t
    cases rest with
    | nil => simp [fold?] at h
    | cons b rest =>
      show fold? g op (a :: b :: rest) = some t
      have hsource : ∃ value, f a = some value ∧ ∃ term,
          value.expect? sort = some term ∧ ∃ terms,
          typedTerms? f sort (b :: rest) = some terms ∧
          (⟨sort, foldTerms op term terms⟩ : PackedTerm E) = t := by
        simpa [fold?, Option.bind_eq_some_iff] using h
      obtain ⟨value, hv, term, ht, terms, hterms, hresult⟩ := hsource
      have hvalue : g a = some value := hfg a value hv
      have htail : typedTerms? g sort (b :: rest) = some terms :=
        typedTerms_refines hfg sort _ terms hterms
      simpa [fold?, hvalue, ht, htail] using congrArg some hresult

/-- Adjacent comparisons preserve successful typed list decoding. -/
theorem compare_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (op : Operation E.signature 2 (fun _ => .int) .bool)
    (reverse : Bool) (es : List Expr) (t : PackedTerm E)
    (h : compare? f op reverse es = some t) : compare? g op reverse es = some t := by
  cases es with
  | nil => simp [compare?] at h
  | cons a rest =>
      cases rest with
      | nil => simp [compare?] at h
      | cons b rest =>
          simp only [compare?] at h ⊢
          change (typedTerms? f .int (a :: b :: rest)).bind _ = some t at h
          change (typedTerms? g .int (a :: b :: rest)).bind _ = some t
          cases hs : typedTerms? f .int (a :: b :: rest) with
          | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
          | some ts =>
              simpa only [hs, typedTerms_refines hfg .int _ ts hs,
                Option.bind_some] using h

/-- Both all-pairs and adjacent equality decoding retain inferred sorts. -/
theorem equalities_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (distinct : Bool) (es : List Expr) (t : PackedTerm E)
    (h : equalities? f distinct es = some t) : equalities? g distinct es = some t := by
  cases es with
  | nil => simp [equalities?] at h
  | cons a rest =>
      cases rest with
      | nil => simp [equalities?] at h
      | cons b rest =>
          cases ha : f a with
          | none => simp [equalities?, ha] at h
          | some va =>
              simp only [equalities?, ha, hfg a va ha] at h ⊢
              change (typedTerms? f va.sort (b :: rest)).bind _ = some t at h
              change (typedTerms? g va.sort (b :: rest)).bind _ = some t
              cases hs : typedTerms? f va.sort (b :: rest) with
              | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
              | some ts =>
                  simpa only [hs, typedTerms_refines hfg va.sort _ ts hs,
                    Option.bind_some] using h

/-- Linear multiplication's coefficient check keeps exactly the decoded terms. -/
theorem multiply_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (es : List Expr) (t : PackedTerm E)
    (h : multiply? f es = some t) : multiply? g es = some t := by
  cases es with
  | nil => simp [multiply?] at h
  | cons a rest =>
      cases rest with
      | nil => simp [multiply?] at h
      | cons b rest =>
          simp only [multiply?] at h ⊢
          change (typedTerms? f .int (a :: b :: rest)).bind _ = some t at h
          change (typedTerms? g .int (a :: b :: rest)).bind _ = some t
          cases hs : typedTerms? f .int (a :: b :: rest) with
          | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
          | some ts =>
              simpa only [hs, typedTerms_refines hfg .int _ ts hs,
                Option.bind_some] using h

/-- Expose the binding sequence explicitly so successful results can be named. -/
private theorem letBindings_pair (recur : Expr → Option (PackedTerm E))
    (name : String) (rhs : Expr) (es : List Expr) :
    letBindings? recur (.list [.atom name, rhs] :: es) =
      if !simpleSymbol name || reserved.contains name then none else
      (recur rhs).bind (fun value => (letBindings? recur es).bind (fun values =>
        if values.any (fun pair => pair.1 == name) then none
        else some ((name, value) :: values))) := rfl

private theorem letBindings_pair_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (name : String) (rhs : Expr) (es : List Expr)
    (htail : ∀ values, letBindings? f es = some values → letBindings? g es = some values)
    (values : Locals E) (h : letBindings? f (.list [.atom name, rhs] :: es) = some values) :
    letBindings? g (.list [.atom name, rhs] :: es) = some values := by
  simp only [letBindings_pair] at h ⊢
  split at h
  · contradiction
  · rename_i valid
    rw [ite_eq_right valid]
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨value, hv, rest, hr, hresult⟩ := h
    exact ⟨value, hfg rhs value hv, rest, htail rest hr, hresult⟩

/-- Parallel let bindings retain their values and duplicate-name checks. -/
theorem letBindings_refines {f g : Expr → Option (PackedTerm E)}
    (hfg : Refines f g) (es : List Expr) (values : Locals E)
    (h : letBindings? f es = some values) : letBindings? g es = some values := by
  induction es generalizing values with
  | nil => exact h
  | cons e es ih =>
    show letBindings? g (e :: es) = some values
    unfold letBindings? at h
    split at h
    · contradiction
    · rename_i ignored name rhs tail hshape
      obtain ⟨he, htail⟩ : e = .list [.atom name, rhs] ∧ es = tail := List.cons.inj hshape
      subst e
      subst tail
      exact letBindings_pair_refines hfg name rhs es ih values h
    · contradiction

/-- The scoped decoder step preserves successful refinements in every scope. -/
theorem decodeScopedFuel_step {n m : Nat}
    (hfg : ∀ locals, Refines (decodeScopedFuel? E n locals) (decodeScopedFuel? E m locals))
    (locals : Locals E) (e : Expr) (t : PackedTerm E)
    (h : decodeScopedFuel? E (n + 1) locals e = some t) :
    decodeScopedFuel? E (m + 1) locals e = some t := by
  have hscope : Refines (decodeScopedFuel? E n locals) (decodeScopedFuel? E m locals) := hfg locals
  have hbindings : ∀ es values, letBindings? (decodeScopedFuel? E n locals) es = some values →
      letBindings? (decodeScopedFuel? E m locals) es = some values := letBindings_refines hscope
  have happly : ∀ name es value, applyUF? E (decodeScopedFuel? E n locals) name es = some value →
      applyUF? E (decodeScopedFuel? E m locals) name es = some value := applyUF_refines hscope
  unfold decodeScopedFuel? at h ⊢
  split at h
  all_goals try first
    | exact h
    | exact unary_refines (hfg locals) _ _ _ h
    | exact fold_refines (hfg locals) _ _ _ h
    | exact implication_refines (hfg locals) _ _ _ h
    | exact xor_refines (hfg locals) _ _ _ h
    | exact compare_refines (hfg locals) _ _ _ _ h
    | exact equalities_refines (hfg locals) _ _ _ h
    | exact ite_refines (hfg locals) _ _ _ _ h
    | exact multiply_refines (hfg locals) _ _ h

  · split at h
    · exact h
    · split at h
      · exact h
      · exact happly _ _ _ h
  · show (letBindings? (decodeScopedFuel? E m locals) _).bind _ = some t
    rename_i head tail body
    change (letBindings? (decodeScopedFuel? E n locals) (head :: tail)).bind _ = some t at h
    change (letBindings? (decodeScopedFuel? E m locals) (head :: tail)).bind _ = some t
    obtain ⟨values, hv, hb⟩ : ∃ values,
        letBindings? (decodeScopedFuel? E n locals) (head :: tail) = some values ∧
        decodeScopedFuel? E n (values ++ locals) body = some t := Option.bind_eq_some_iff.mp h
    have hvalues : letBindings? (decodeScopedFuel? E m locals) (head :: tail) = some values :=
      hbindings _ values hv
    have hbody : decodeScopedFuel? E m (values ++ locals) body = some t :=
      hfg (values ++ locals) body t hb
    exact Option.bind_eq_some_iff.mpr ⟨values, hvalues, hbody⟩
  · split at h
    · contradiction
    · rename_i guard
      simpa only [ite_eq_right guard] using happly _ _ _ h

/-- Increasing the scoped decoder's fuel preserves every successful result,
including all parallel-let right-hand sides and the extended body scope. -/
theorem decodeScopedFuel_mono {n m : Nat} (hnm : n ≤ m)
    (locals : Locals E) (e : Expr) (t : PackedTerm E)
    (h : decodeScopedFuel? E n locals e = some t) :
    decodeScopedFuel? E m locals e = some t := by
  induction n generalizing m locals e t with
  | zero => simp [decodeScopedFuel?] at h
  | succ n ih =>
      cases m with
      | zero => exact False.elim (Nat.not_succ_le_zero n hnm)
      | succ m =>
          apply decodeScopedFuel_step (n := n) (m := m) ?_ locals e t h
          intro scope expression result decoded
          exact ih (Nat.le_of_succ_le_succ hnm) scope expression result decoded

/-- The closed entry point inherits successful fuel monotonicity. -/
theorem decodeTermFuel_mono {n m : Nat} (hnm : n ≤ m)
    (e : Expr) (t : PackedTerm E) (h : decodeTermFuel? E n e = some t) :
    decodeTermFuel? E m e = some t :=
  decodeScopedFuel_mono hnm [] e t h

/-- Each normalized child can be decoded at the combined output-node budget.
This permits arbitrary lexical expansion: only the actual output sizes enter. -/
theorem normalizeMapM_transport {α β : Type}
    (source : Expr → Option α) (normalize : Expr → Option Expr)
    (decode : Nat → Expr → Option β) (mapValue : α → β)
    (hmono : ∀ n m, n ≤ m → Refines (decode n) (decode m))
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decode (expressionFuel output) output = some (mapValue value))
    (es : List Expr) (values : List α) (h : es.mapM source = some values) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      outputs.mapM (decode (expressionsFuel outputs)) = some (values.map mapValue) := by
  rw [List.mapM_eq_some_iff_forall₂] at h
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons e value es values he htail ih =>
      obtain ⟨output, ho, hd⟩ := hchildren e value he
      obtain ⟨outputs, hos, hds⟩ := ih
      have hhead : decode (expressionsFuel (output :: outputs)) output =
          some (mapValue value) :=
        hmono _ _ (Nat.le_add_right _ _) output (mapValue value) hd
      have htail' : outputs.mapM (decode (expressionsFuel (output :: outputs))) =
          some (values.map mapValue) :=
        mapM_refines (hmono _ _ (Nat.le_add_left _ _)) outputs _ hds
      exact ⟨output :: outputs, by simp [ho, hos], by simp [hhead, htail']⟩

/-- Normalize a successfully sort-checked argument list and decode it at its
actual expanded list budget, preserving every mapped typed value. -/
theorem normalizeTypedTerms_transport (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (sort : SortCode String) (es : List Expr)
    (ts : List (Uflia.Term E.signature sort)) (h : typedTerms? source sort es = some ts) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      typedTerms? (decodeTermFuel? F (expressionsFuel outputs)) sort outputs =
        some (ts.map (Uflia.Term.map f)) := by
  apply normalizeMapM_transport
    (fun e => (source e).bind (fun value => value.expect? sort)) normalize
    (fun fuel e => (decodeTermFuel? F fuel e).bind (fun value => value.expect? sort))
    (Uflia.Term.map f) ?_ ?_ es ts h
  · intro n m hnm e term decoded
    cases hv : decodeTermFuel? F n e with
    | none => simp only [hv, Option.bind_none, reduceCtorEq] at decoded
    | some value =>
        simpa only [decodeTermFuel_mono hnm e value hv, hv, Option.bind_some] using decoded
  · intro e term decoded
    cases hv : source e with
    | none => simp only [hv, Option.bind_none, reduceCtorEq] at decoded
    | some value =>
        simp only [hv, Option.bind_some] at decoded
        obtain ⟨output, ho, hd⟩ := hchildren e value hv
        refine ⟨output, ho, ?_⟩
        simp only [hd, Option.bind_some, expect_mapPacked, decoded, Option.map_some]

/-- Local values are represented by closed target expressions decoded at their
own node budgets. Names and ordering retain lexical shadowing. -/
def LocalsRelated (f : E.signature ⟶ F.signature) (locals : Locals E)
    (syntaxLocals : SyntaxLocals) : Prop :=
  List.Forall₂ (fun value expression => value.1 = expression.1 ∧
    decodeTermFuel? F (expressionFuel expression.2) expression.2 =
      some (mapPacked f value.2)) locals syntaxLocals

/-- The local relation is stable under the decoder's left-biased scope extension. -/
theorem localsRelated_append (f : E.signature ⟶ F.signature)
    {xs ys : Locals E} {ss ts : SyntaxLocals}
    (hxs : LocalsRelated f xs ss) (hys : LocalsRelated f ys ts) :
    LocalsRelated f (xs ++ ys) (ss ++ ts) := by
  induction hxs with
  | nil => exact hys
  | cons head tail ih => exact .cons head ih

/-- Name-only duplicate checks agree in related typed and syntactic scopes. -/
theorem localsRelated_anyName (f : E.signature ⟶ F.signature)
    {locals : Locals E} {syntaxLocals : SyntaxLocals} (h : LocalsRelated f locals syntaxLocals)
    (name : String) :
    locals.any (fun pair => pair.1 == name) = syntaxLocals.any (fun pair => pair.1 == name) := by
  induction h with
  | nil => rfl
  | @cons a b xs ys hab htail ih =>
      simp only [List.any_cons, hab.1, ih]

/-- Lexical lookup agrees on absence and on the own-budget interpretation of
present values, including shadowed duplicate names in outer scopes. -/
theorem localsRelated_lookup (f : E.signature ⟶ F.signature)
    {locals : Locals E} {syntaxLocals : SyntaxLocals} (h : LocalsRelated f locals syntaxLocals)
    (name : String) :
    match local? locals name, syntaxLocal? syntaxLocals name with
    | none, none => True
    | some value, some output =>
        decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value)
    | _, _ => False := by
  induction h with
  | nil => trivial
  | @cons a b xs ys hab htail ih =>
      rcases a with ⟨a, value⟩
      rcases b with ⟨b, output⟩
      obtain ⟨names, decoded⟩ := hab
      dsimp only at names decoded
      subst b
      by_cases hn : a = name
      · simp only [local?, syntaxLocal?, hn, ite_true]
        exact decoded
      · simpa only [local?, syntaxLocal?, hn, ite_false] using ih

private theorem syntaxBindings_pair (recur : Expr → Option Expr)
    (name : String) (rhs : Expr) (es : List Expr) :
    syntaxBindings? recur (.list [.atom name, rhs] :: es) =
      if !simpleSymbol name || reserved.contains name then none else
      (recur rhs).bind (fun value => (syntaxBindings? recur es).bind (fun values =>
        if values.any (fun pair => pair.1 == name) then none
        else some ((name, value) :: values))) := rfl

private theorem normalizeLetBindings_pair (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (name : String) (rhs : Expr) (es : List Expr)
    (htail : ∀ values, letBindings? source es = some values → ∃ outputs,
      syntaxBindings? normalize es = some outputs ∧ LocalsRelated f values outputs)
    (values : Locals E) (h : letBindings? source (.list [.atom name, rhs] :: es) = some values) :
    ∃ outputs, syntaxBindings? normalize (.list [.atom name, rhs] :: es) = some outputs ∧
      LocalsRelated f values outputs := by
  simp only [letBindings_pair] at h
  split at h
  · contradiction
  · show ∃ outputs, syntaxBindings? normalize (.list [.atom name, rhs] :: es) = some outputs ∧
      LocalsRelated f values outputs
    rename_i valid
    have hsource : ∃ value, source rhs = some value ∧ ∃ rest,
        letBindings? source es = some rest ∧
        (if rest.any (fun pair => pair.1 == name) then none
         else some ((name, value) :: rest)) = some values := by
      simpa only [Option.bind_eq_some_iff] using h
    obtain ⟨value, hv, rest, hr, hresult⟩ := hsource
    obtain ⟨output, ho, hd⟩ : ∃ output, normalize rhs = some output ∧
        decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value) :=
      hchildren rhs value hv
    obtain ⟨outputs, hos, hrelated⟩ : ∃ outputs,
        syntaxBindings? normalize es = some outputs ∧ LocalsRelated f rest outputs := htail rest hr
    have hdup : rest.any (fun pair => pair.1 == name) =
        outputs.any (fun pair => pair.1 == name) := localsRelated_anyName f hrelated name
    have hread : syntaxBindings? normalize (.list [.atom name, rhs] :: es) =
        some ((name, output) :: outputs) := by
      simp only [syntaxBindings_pair, ite_eq_right valid, ho, hos, Option.bind_some]
      split at hresult
      · contradiction
      · rename_i unique
        rw [← hdup, ite_eq_right unique]
    have hvalues : (name, value) :: rest = values := by
      split at hresult
      · contradiction
      · exact Option.some.inj hresult
    have hrel : LocalsRelated f ((name, value) :: rest) ((name, output) :: outputs) :=
      .cons ⟨rfl, hd⟩ hrelated
    exact ⟨(name, output) :: outputs, hread, hvalues ▸ hrel⟩

/-- Parallel binding normalization uses the same outer recursive relation for
every right-hand side and retains the checked source names and ordering. -/
theorem normalizeLetBindings_transport (f : E.signature ⟶ F.signature)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (hchildren : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (es : List Expr) (values : Locals E) (h : letBindings? source es = some values) :
    ∃ outputs, syntaxBindings? normalize es = some outputs ∧ LocalsRelated f values outputs := by
  induction es generalizing values with
  | nil =>
    have hv : ([] : Locals E) = values := Option.some.inj h
    subst values
    exact ⟨[], rfl, .nil⟩
  | cons e es ih =>
    show ∃ outputs, syntaxBindings? normalize (e :: es) = some outputs ∧ LocalsRelated f values outputs
    unfold letBindings? at h
    split at h
    · contradiction
    · rename_i ignored name rhs tail hshape
      obtain ⟨he, htail⟩ : e = .list [.atom name, rhs] ∧ es = tail := List.cons.inj hshape
      subst e
      subst tail
      exact normalizeLetBindings_pair f source normalize hchildren name rhs es ih values h
    · contradiction

/-- Sequence a successful heterogeneous recursive transport. -/
theorem mapM_transport {α β γ : Type} {f : α → Option β} {g : α → Option γ}
    (k : β → γ) (hfg : ∀ a b, f a = some b → g a = some (k b))
    (as : List α) (bs : List β) (h : as.mapM f = some bs) :
    as.mapM g = some (bs.map k) := by
  rw [List.mapM_eq_some_iff_forall₂] at h ⊢
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab htail ih => exact .cons (hfg a b hab) ih

/-- Sort-checked recursive lists commute with actual typed symbol transport. -/
theorem typedTerms_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (sort : SortCode String) (es : List Expr)
    (ts : List (Uflia.Term E.signature sort)) (h : typedTerms? source sort es = some ts) :
    typedTerms? target sort es = some (ts.map (Uflia.Term.map f)) := by
  apply mapM_transport (Uflia.Term.map f) (as := es) (bs := ts) ?_ h
  intro e t ht
  change (source e).bind (fun value => value.expect? sort) = some t at ht
  change (target e).bind (fun value => value.expect? sort) = some (Uflia.Term.map f t)
  cases hv : source e with
  | none => simp only [hv, Option.bind_none, reduceCtorEq] at ht
  | some value =>
      simp only [hv, Option.bind_some] at ht
      simp only [hfg e value hv, Option.bind_some, expect_mapPacked, ht, Option.map_some]

/-- UF argument transport retains each dependent input position. -/
theorem decodeArguments_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (inputs : List (SortCode String)) :
    ∀ (es : List Expr) (ts : (i : Fin inputs.length) →
      Uflia.Term E.signature (inputs.get i)),
      decodeArguments? source inputs es = some ts →
      decodeArguments? target inputs es = some (fun i => Uflia.Term.map f (ts i)) := by
  induction inputs with
  | nil =>
    intro es ts h
    cases es with
    | nil =>
      simp only [decodeArguments?, Option.some.injEq]
      funext i
      exact Fin.elim0 i
    | cons e es => simp [decodeArguments?] at h
  | cons input inputs ih =>
    show ∀ es ts, decodeArguments? source (input :: inputs) es = some ts →
      decodeArguments? target (input :: inputs) es = some (fun i => Uflia.Term.map f (ts i))
    intro es ts h
    cases es with
    | nil => simp [decodeArguments?] at h
    | cons e es =>
      show decodeArguments? target (input :: inputs) (e :: es) =
        some (fun i => Uflia.Term.map f (ts i))
      have hsource : ∃ value, source e = some value ∧ ∃ term,
          value.expect? input = some term ∧ ∃ tail,
          decodeArguments? source inputs es = some tail ∧ Fin.cases term tail = ts := by
        simpa [decodeArguments?, Option.bind_eq_some_iff] using h
      obtain ⟨value, hv, term, ht, tail, htail, hr⟩ := hsource
      have hvalue : target e = some (mapPacked f value) := hfg e value hv
      have hterm : (mapPacked f value).expect? input = some (Uflia.Term.map f term) := by
        rw [expect_mapPacked, ht]
        rfl
      have hrest : decodeArguments? target inputs es = some (fun i => Uflia.Term.map f (tail i)) :=
        ih es tail htail
      have harguments : Fin.cases (Uflia.Term.map f term) (fun i => Uflia.Term.map f (tail i)) =
          (fun i => Uflia.Term.map f (ts i)) := by
        rw [← hr]
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simp only [decodeArguments?, hvalue]
      change ((mapPacked f value).expect? input).bind _ = _
      rw [hterm]
      change (decodeArguments? target inputs es).bind _ = _
      rw [hrest]
      exact congrArg some harguments

/-- Recover the whole input profile from a typed declaration symbol. -/
theorem symbol_inputs {n : Nat} {inputs : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n inputs output) :
    (E.declarations.get (symbolIndex symbol)).inputs = List.ofFn inputs := by
  cases symbol
  exact (List.ofFn_get _).symm

/-- Evaluate a UF at its explicit profile before relating it to name lookup. -/
def applyProfile? (inputs : List (SortCode String)) (output : SortCode String)
    (symbol : Symbol E inputs.length inputs.get output)
    (recur : Expr → Option (PackedTerm E)) (es : List Expr) : Option (PackedTerm E) := do
  let terms ← decodeArguments? recur inputs es
  pure ⟨output, .app (.uf symbol) terms⟩

/-- An explicit typed symbol is exactly its actual declaration application;
whole profile recovery justifies reconstruction, not index equality alone. -/
theorem applyProfile_lookup (inputs : List (SortCode String)) (output : SortCode String)
    (symbol : Symbol E inputs.length inputs.get output)
    (recur : Expr → Option (PackedTerm E)) (es : List Expr) (name : String)
    (hlookup : lookup? E name = some (symbolIndex symbol)) :
    applyProfile? inputs output symbol recur es = applyUF? E recur name es := by
  have hin := symbol_inputs symbol
  rw [List.ofFn_get] at hin
  have hout := symbol_output symbol
  have hs := symbol_reconstruct symbol
  generalize hj : symbolIndex symbol = j at *
  cases hin
  cases hout
  have heq : Symbol.declared j = symbol := eq_of_heq hs
  subst symbol
  simp only [applyProfile?, applyUF?, hlookup]
  rfl

/-- Successful UF decoding commutes with an actual declaration name map.
The target argument profile is recovered from the typed symbol image. -/
theorem applyUF_transport (f : NameMap E F)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f.abstract t))
    (name : String) (es : List Expr) (t : PackedTerm E)
    (h : applyUF? E source name es = some t) :
    applyUF? F target (globalName E f.rename name) es = some (mapPacked f.abstract t) := by
  cases hi : lookup? E name with
  | none => simp [applyUF?, hi] at h
  | some i =>
    show applyUF? F target (globalName E f.rename name) es = some (mapPacked f.abstract t)
    have htarget : lookup? F (f.rename name) =
        some (symbolIndex (f.abstract.operations (.declared i))) := f.lookup name i hi
    have hglobal : globalName E f.rename name = f.rename name := by
      simp only [globalName, hi]
    have hsource : ∃ ts, decodeArguments? source (E.declarations.get i).inputs es = some ts ∧
        (⟨(E.declarations.get i).output, .app (.uf (.declared i)) ts⟩ : PackedTerm E) = t := by
      simpa [applyUF?, hi, Option.bind_eq_some_iff] using h
    obtain ⟨ts, hs, ht⟩ := hsource
    have harguments : decodeArguments? target (E.declarations.get i).inputs es =
        some (fun j => Uflia.Term.map f.abstract (ts j)) :=
      decodeArguments_transport f.abstract hfg _ es ts hs
    have hprofile : applyProfile? (E.declarations.get i).inputs (E.declarations.get i).output
        (f.abstract.operations (.declared i)) target es =
        some (mapPacked f.abstract (⟨(E.declarations.get i).output,
          .app (.uf (.declared i)) ts⟩ : PackedTerm E)) := by
      unfold applyProfile?
      rw [harguments]
      rfl
    have hlookup : applyProfile? (E.declarations.get i).inputs (E.declarations.get i).output
        (f.abstract.operations (.declared i)) target es = applyUF? F target (f.rename name) es :=
      applyProfile_lookup _ _ (f.abstract.operations (.declared i)) target es (f.rename name) htarget
    calc
      applyUF? F target (globalName E f.rename name) es =
          applyProfile? (E.declarations.get i).inputs (E.declarations.get i).output
            (f.abstract.operations (.declared i)) target es := by rw [hglobal, hlookup]
      _ = some (mapPacked f.abstract t) := by rw [hprofile, ht]

/-- Unary typed elaboration commutes with symbol transport. -/
theorem unary_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output) (e : Expr) (t : PackedTerm E)
    (h : unary? source op e = some t) :
    unary? target (Operation.map f op) e = some (mapPacked f t) := by
  cases hv : source e with
  | none => simp [unary?, hv] at h
  | some value =>
      cases ht : value.expect? input with
      | none => simp [unary?, hv, ht] at h
      | some term =>
          have hr : (⟨output, .app op (fun _ => term)⟩ : PackedTerm E) = t := by
            exact Option.some.inj (by simpa [unary?, hv, ht] using h)
          subst t
          simp only [unary?, hfg e value hv]
          change ((mapPacked f value).expect? input).bind _ = _
          rw [expect_mapPacked, ht]
          rfl

/-- Binary typed elaboration preserves ordered arguments under symbol maps. -/
theorem binary_transport (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E)} {target : Expr → Option (PackedTerm F)}
    (hfg : ∀ e t, source e = some t → target e = some (mapPacked f t))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr) (t : PackedTerm E)
    (h : binary? source op a b = some t) :
    binary? target (Operation.map f op) a b = some (mapPacked f t) := by
  have hsource : ∃ va, source a = some va ∧ ∃ ta,
      va.expect? input = some ta ∧ ∃ vb, source b = some vb ∧ ∃ tb,
      vb.expect? input = some tb ∧
      (⟨output, .app op (Fin.cases ta (fun _ => tb))⟩ : PackedTerm E) = t := by
    simpa [binary?, Option.bind_eq_some_iff] using h
  obtain ⟨va, ha, ta, hta, vb, hb, tb, htb, hr⟩ := hsource
  have hma : (mapPacked f va).expect? input = some (Uflia.Term.map f ta) := by
    rw [expect_mapPacked, hta]
    rfl
  have hmb : (mapPacked f vb).expect? input = some (Uflia.Term.map f tb) := by
    rw [expect_mapPacked, htb]
    rfl
  have hresult : mapPacked f (⟨output, .app op (Fin.cases ta (fun _ => tb))⟩ : PackedTerm E) =
      mapPacked f t := congrArg (mapPacked f) hr
  have hterm : Uflia.Term.map f (.app op (Fin.cases ta (fun _ => tb))) =
      .app (Operation.map f op) (Fin.cases (Uflia.Term.map f ta) (fun _ => Uflia.Term.map f tb)) :=
    map_binary f op ta tb
  simp only [binary?, hfg a va ha, hfg b vb hb]
  change ((mapPacked f va).expect? input).bind _ = _
  rw [hma]
  change ((mapPacked f vb).expect? input).bind _ = _
  rw [hmb]
  simpa only [Option.bind_some, Option.pure_def, mapPacked, hterm] using congrArg some hresult

/-- The homogeneous pair constructor transports without assuming the result
sort determines a declaration's profile. -/
theorem pair_map (f : E.signature ⟶ F.signature) {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (a b : Uflia.Term E.signature sort) :
    Uflia.Term.map f (pair op a b) =
      pair (Operation.map f op) (Uflia.Term.map f a) (Uflia.Term.map f b) :=
  map_binary f op a b

/-- Folding typed nodes commutes with symbol transport in list order. -/
theorem foldTerms_map (f : E.signature ⟶ F.signature) {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (a : Uflia.Term E.signature sort) (ts : List (Uflia.Term E.signature sort)) :
    Uflia.Term.map f (foldTerms op a ts) =
      foldTerms (Operation.map f op) (Uflia.Term.map f a) (ts.map (Uflia.Term.map f)) := by
  induction ts generalizing a with
  | nil => rfl
  | cons b ts ih =>
      simpa only [foldTerms, List.foldl_cons, List.map_cons, pair_map]
        using ih (pair op a b)

/-- Conjunction preserves the order of its transported formulas. -/
theorem conjunction_map (f : E.signature ⟶ F.signature)
    (ts : List (Formula E.signature)) :
    Uflia.Term.map f (conjunction ts) =
      conjunction (ts.map (Uflia.Term.map f)) := by
  cases ts with
  | nil => exact map_nullary f (.boolean true)
  | cons a ts => exact foldTerms_map f .and a ts

/-- Mapping adjacent relations retains source list order. -/
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

/-- Coefficient distribution is independent of the names of UF symbols. -/
theorem scaleLinear_map (f : E.signature ⟶ F.signature)
    {sort : SortCode String} (coefficient : Int) (t : Uflia.Term E.signature sort) :
    Uflia.Term.map f (scaleLinear coefficient t) =
      scaleLinear coefficient (Uflia.Term.map f t) := by
  induction t generalizing coefficient with
  | var i => exact Fin.elim0 i
  | app op args ih =>
      show Uflia.Term.map f (scaleLinear coefficient (.app op args)) =
        scaleLinear coefficient (Uflia.Term.map f (.app op args))
      cases op <;> try rfl
      case uf n inputs output symbol =>
        cases output <;>
          simp only [scaleLinear, Uflia.Term.map, ManySorted.Term.map,
            Signature.expandMap, Operation.map]
      case integer n =>
        show Uflia.Term.map f (scaleLinear coefficient (.app (.integer n) args)) =
          scaleLinear coefficient (Uflia.Term.map f (.app (.integer n) args))
        have h : args = (fun i => Fin.elim0 i) := funext (fun i => Fin.elim0 i)
        rw [h]
        change Uflia.Term.map f (Uflia.Term.integer (coefficient * n)) =
          scaleLinear coefficient (Uflia.Term.map f (Uflia.Term.integer n))
        have hm : Uflia.Term.map f (Uflia.Term.integer (A := E.signature) n) =
            Uflia.Term.integer (A := F.signature) n :=
          map_nullary (E := E) (F := F) f (.integer n)
        rw [hm]
        exact map_nullary (E := E) (F := F) f (.integer (coefficient * n))
      case add =>
        show Uflia.Term.map f (scaleLinear coefficient (.app .add args)) =
          scaleLinear coefficient (Uflia.Term.map f (.app .add args))
        simp only [scaleLinear, pair, Uflia.Term.map, ManySorted.Term.map,
          Signature.expandMap, Operation.map]
        congr 1
        funext i
        exact Fin.cases (ih 0 coefficient)
          (fun j => Fin.cases (ih 1 coefficient) (fun k => Fin.elim0 k) j) i
      case sub =>
        show Uflia.Term.map f (scaleLinear coefficient (.app .sub args)) =
          scaleLinear coefficient (Uflia.Term.map f (.app .sub args))
        simp only [scaleLinear, pair, Uflia.Term.map, ManySorted.Term.map,
          Signature.expandMap, Operation.map]
        congr 1
        funext i
        exact Fin.cases (ih 0 coefficient)
          (fun j => Fin.cases (ih 1 coefficient) (fun k => Fin.elim0 k) j) i
      case scale k => exact ih 0 (coefficient * k)
      case ite s => cases s <;> rfl

/-- Coefficient recognition and the single symbolic-factor restriction commute
with an arbitrary profile-preserving signature map, including identifications. -/
theorem multiplyFactors_map (f : E.signature ⟶ F.signature)
    (ts : List (Uflia.Term E.signature .int)) (coefficient : Int)
    (factor : Option (Uflia.Term E.signature .int)) :
    multiplyFactors? (ts.map (Uflia.Term.map f)) coefficient (factor.map (Uflia.Term.map f)) =
      (multiplyFactors? ts coefficient factor).map (Uflia.Term.map f) := by
  induction ts generalizing coefficient factor with
  | nil =>
      cases factor with
      | none =>
          simp only [List.map_nil, Option.map_none, multiplyFactors?, Option.map_some]
          exact congrArg some (map_nullary f (.integer coefficient)).symm
      | some t =>
          simp only [List.map_nil, Option.map_some, multiplyFactors?]
          exact congrArg some (scaleLinear_map f coefficient t).symm
  | cons t ts ih =>
      simp only [List.map_cons, multiplyFactors?, integerValue_map]
      cases hv : integerValue? t with
      | some k => exact ih (coefficient * k) factor
      | none =>
          cases factor with
          | none => exact ih coefficient (some t)
          | some factor => rfl

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
