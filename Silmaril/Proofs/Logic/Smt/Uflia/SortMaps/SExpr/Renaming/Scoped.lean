module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Lexical.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Operators.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Applications.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic Uflia.SExpr
open Uflia.SExpr.Renaming
variable {E F : Environment}

private def mappedSource (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (e : Expr) : Option (PackedTerm F) :=
  (source e).map (mapPacked f)

private theorem mappedSource_success (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) :
    ∀ e value, source e = some value → mappedSource f source e = some (mapPacked f value) := by
  intro e value h
  simp only [mappedSource, h, Option.map_some]

private theorem mappedChildren (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value)) :
    ∀ e mapped, mappedSource f source e = some mapped → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output =
        some (Uflia.SExpr.Renaming.mapPacked (𝟙 F.signature) mapped) := by
  intro e mapped hm
  cases hv : source e with
  | none => simp [mappedSource, hv] at hm
  | some value =>
    have heq : mapPacked f value = mapped := by simpa [mappedSource, hv] using hm
    subst mapped
    obtain ⟨output, hn, hd⟩ := children e value hv
    exact ⟨output, hn, by simpa using hd⟩

@[simp] private theorem fixed_operation_id {n inputs output}
    (op : Operation F.signature n inputs output) : Operation.map (𝟙 F.signature) op = op := by
  cases op <;> rfl


private theorem normalizeEqualities_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (distinct : Bool) (es : List Expr) (value : PackedTerm E)
    (h : equalities? source distinct es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      equalities? (decodeTermFuel? F (1 + expressionsFuel outputs)) distinct outputs =
        some (mapPacked f value) := by
  have mapped := equalities_transport f (mappedSource_success f source) distinct es value h
  obtain ⟨outputs, hn, hd⟩ := Uflia.SExpr.Renaming.normalizeEqualities_result
    (𝟙 F.signature) (mappedSource f source) normalize (mappedChildren f source normalize children)
    distinct es (mapPacked f value) mapped
  exact ⟨outputs, hn, by simpa using hd⟩


private theorem normalizeMultiply_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (es : List Expr) (value : PackedTerm E)
    (h : multiply? source es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      multiply? (decodeTermFuel? F (1 + expressionsFuel outputs)) outputs =
        some (mapPacked f value) := by
  have mapped := multiply_transport f (mappedSource_success f source) es value h
  obtain ⟨outputs, hn, hd⟩ := Uflia.SExpr.Renaming.normalizeMultiply_result
    (𝟙 F.signature) (mappedSource f source) normalize (mappedChildren f source normalize children)
    es (mapPacked f value) mapped
  exact ⟨outputs, hn, by simpa using hd⟩


private theorem normalizeImplication_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : implication? source a b = some value) :
    ∃ a' b', [a, b].mapM normalize = some [a', b'] ∧
      implication? (decodeTermFuel? F (1 + expressionsFuel [a', b'])) a' b' =
        some (mapPacked f value) := by
  have mapped := implication_transport f (mappedSource_success f source) a b value h
  obtain ⟨a', b', hn, hd⟩ := Uflia.SExpr.Renaming.normalizeImplication_result
    (𝟙 F.signature) (mappedSource f source) normalize (mappedChildren f source normalize children)
    a b (mapPacked f value) mapped
  exact ⟨a', b', hn, by simpa using hd⟩


private theorem normalizeXor_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : xor? source a b = some value) :
    ∃ a' b', [a, b].mapM normalize = some [a', b'] ∧
      xor? (decodeTermFuel? F (1 + expressionsFuel [a', b'])) a' b' =
        some (mapPacked f value) := by
  have mapped := xor_transport f (mappedSource_success f source) a b value h
  obtain ⟨a', b', hn, hd⟩ := Uflia.SExpr.Renaming.normalizeXor_result
    (𝟙 F.signature) (mappedSource f source) normalize (mappedChildren f source normalize children)
    a b (mapPacked f value) mapped
  exact ⟨a', b', hn, by simpa using hd⟩


private theorem normalizeIte_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (c : Expr) (a : Expr) (b : Expr) (value : PackedTerm E)
    (h : ite? source c a b = some value) :
    ∃ c' a' b', [c, a, b].mapM normalize = some [c', a', b'] ∧
      ite? (decodeTermFuel? F (1 + expressionsFuel [c', a', b'])) c' a' b' =
        some (mapPacked f value) := by
  have mapped := ite_transport f (mappedSource_success f source) c a b value h
  obtain ⟨c', a', b', hn, hd⟩ := Uflia.SExpr.Renaming.normalizeIte_result
    (𝟙 F.signature) (mappedSource f source) normalize (mappedChildren f source normalize children)
    c a b (mapPacked f value) mapped
  exact ⟨c', a', b', hn, by simpa using hd⟩

private theorem normalizeUnary_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    {input input' output output' : SortCode String}
    (hs : f.sorts input = input') (ht : f.sorts output = output')
    (op : Operation E.signature 1 (fun _ => input) output)
    (op' : Operation F.signature 1 (fun _ => input') output')
    (hop : HEq (Hom.operation f op) op') (e : Expr) (value : PackedTerm E)
    (h : unary? source op e = some value) :
    ∃ e', [e].mapM normalize = some [e'] ∧
      unary? (decodeTermFuel? F (1 + expressionsFuel [e'])) op' e' = some (mapPacked f value) := by
  have mapped := unary_at_transport f (mappedSource_success f source) hs ht op op' hop e value h
  obtain ⟨output, hn, hd⟩ := Uflia.SExpr.Renaming.normalizeUnary_result (𝟙 F.signature)
    (mappedSource f source) normalize (mappedChildren f source normalize children)
    op' e (mapPacked f value) mapped
  exact ⟨output, hn, by simpa using hd⟩

private theorem normalizeFold_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    {sort sort' : SortCode String} (hs : f.sorts sort = sort')
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (op' : Operation F.signature 2 (fun _ => sort') sort')
    (hop : HEq (Hom.operation f op) op') (es : List Expr) (value : PackedTerm E)
    (h : fold? source op es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) op' outputs = some (mapPacked f value) := by
  have mapped := fold_at_transport f (mappedSource_success f source) hs op op' hop es value h
  obtain ⟨outputs, hn, hd⟩ := Uflia.SExpr.Renaming.normalizeFold_result (𝟙 F.signature)
    (mappedSource f source) normalize (mappedChildren f source normalize children)
    op' es (mapPacked f value) mapped
  exact ⟨outputs, hn, by simpa using hd⟩

private theorem normalizeCompare_result (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (op : Operation E.signature 2 (fun _ => .int) .bool)
    (op' : Operation F.signature 2 (fun _ => .int) .bool)
    (hop : HEq (Hom.operation f op) op') (reverse : Bool) (es : List Expr) (value : PackedTerm E)
    (h : compare? source op reverse es = some value) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) op' reverse outputs =
        some (mapPacked f value) := by
  have mapped := compare_transport f (mappedSource_success f source) op op' hop reverse es value h
  obtain ⟨outputs, hn, hd⟩ := Uflia.SExpr.Renaming.normalizeCompare_result (𝟙 F.signature)
    (mappedSource f source) normalize (mappedChildren f source normalize children)
    op' reverse es (mapPacked f value) mapped
  exact ⟨outputs, hn, by simpa using hd⟩

@[simp] private theorem fixed_mapPacked_option (o : Option (PackedTerm F)) :
    o.map (Uflia.SExpr.Renaming.mapPacked (𝟙 F.signature)) = o := by
  cases o <;> simp

private theorem normalizedChildren (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (es : List Expr) (values : List (PackedTerm E)) (h : es.mapM source = some values) :
    ∃ outputs, es.mapM normalize = some outputs ∧
      List.Forall₂ (DecodeRelated (mappedSource f source)
        (decodeTermFuel? F (1 + expressionsFuel outputs))) es outputs := by
  have mapped := Uflia.SExpr.Renaming.mapM_transport (mapPacked f)
    (mappedSource_success f source) es values h
  obtain ⟨outputs, hn, hr⟩ := Uflia.SExpr.Renaming.normalizeChildren_success (𝟙 F.signature)
    (mappedSource f source) normalize (mappedChildren f source normalize children) es ⟨_, mapped⟩
  exact ⟨outputs, hn, by simpa only [fixed_mapPacked_option] using hr⟩

private theorem applyUF_related {source target : Expr → Option (PackedTerm F)}
    {es outputs : List Expr} (related : List.Forall₂ (DecodeRelated source target) es outputs)
    (name : String) (value : PackedTerm F) (h : applyUF? F source name es = some value) :
    applyUF? F target name outputs = some value := by
  change (lookup? F name).bind _ = some value at h ⊢
  obtain ⟨index, lookup, rest⟩ := Option.bind_eq_some_iff.mp h
  rw [lookup]
  change (decodeArguments? source (F.declarations.get index).inputs es).bind _ = some value at rest
  obtain ⟨terms, decoded, same⟩ := Option.bind_eq_some_iff.mp rest
  change (decodeArguments? target (F.declarations.get index).inputs outputs).bind _ = some value
  rw [arguments_related related _ terms decoded]
  exact same

/-- Induction uses each actual expanded target expression's own node budget. -/
def NormalizesAt (f : NameMap E F) (fuel : Nat) (locals : Locals E)
    (syntaxLocals : SyntaxLocals) : Prop :=
  ∀ e value, decodeScopedFuel? E fuel locals e = some value → ∃ output,
    normalizeFuel? E f.rename fuel syntaxLocals e = some output ∧
    decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)

/-- The existing lexical normalizer keeps reserved operation names unchanged. -/
theorem normalizeBuiltinApplication_success (f : NameMap E F) (fuel : Nat)
    {locals : Locals E} {syntaxLocals : SyntaxLocals} (legal : LegalLocals locals)
    (related : LocalsRelated f.abstract locals syntaxLocals)
    (name : String) (reservedName : reserved.contains name = true) (notLet : name ≠ "let")
    (es outputs : List Expr)
    (normalized : es.mapM (normalizeFuel? E f.rename fuel syntaxLocals) = some outputs) :
    normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.list (.atom name :: es)) =
      some (.list (.atom name :: outputs)) := by
  have absent := localsRelated_absent f.abstract related name
    (legalLocals_reserved_absent legal name reservedName)
  rw [normalizeApplication_eq f.rename fuel syntaxLocals name es notLet absent]
  rw [globalName_reserved f.rename name reservedName, normalized]
  rfl

/-- Parallel RHSs use the old scope; only the body sees the mapped bindings. -/
theorem normalizeLet_success (f : NameMap E F) (fuel : Nat)
    (children : ∀ locals syntaxLocals, LegalLocals locals →
      LocalsRelated f.abstract locals syntaxLocals → NormalizesAt f fuel locals syntaxLocals)
    (locals : Locals E) (syntaxLocals : SyntaxLocals) (legal : LegalLocals locals)
    (related : LocalsRelated f.abstract locals syntaxLocals)
    (head : Expr) (tail : List Expr) (body : Expr) (values : Locals E)
    (bindings : letBindings? (decodeScopedFuel? E fuel locals) (head :: tail) = some values)
    (value : PackedTerm E)
    (decoded : decodeScopedFuel? E fuel (values ++ locals) body = some value) :
    ∃ output,
      normalizeFuel? E f.rename (fuel + 1) syntaxLocals
        (.list [.atom "let", .list (head :: tail), body]) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  obtain ⟨syntaxBindings, hn, hr⟩ := normalizeLetBindings_transport f.abstract
    (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals)
    (children locals syntaxLocals legal related) (head :: tail) values bindings
  obtain ⟨output, ho, hd⟩ := children (values ++ locals) (syntaxBindings ++ syntaxLocals)
    (legalLocals_append (letBindings_legal _ _ _ bindings) legal)
    (localsRelated_append f.abstract hr related) body value decoded
  refine ⟨output, ?_, hd⟩
  change (syntaxBindings? (normalizeFuel? E f.rename fuel syntaxLocals) (head :: tail)).bind _ = _
  rw [hn]
  exact ho

/-- Atom transport distinguishes lexical substitution from global lookup. -/
theorem normalizeAtom_success (f : NameMap E F) (fuel : Nat)
    (locals : Locals E) (syntaxLocals : SyntaxLocals)
    (related : LocalsRelated f.abstract locals syntaxLocals)
    (name : String) (value : PackedTerm E)
    (decoded : decodeScopedFuel? E (fuel + 1) locals (.atom name) = some value) :
    ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.atom name) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  by_cases ht : name = "true"
  · subst name
    have same : (⟨.bool, Uflia.Term.boolean true⟩ : PackedTerm E) = value := Option.some.inj decoded
    subst value
    refine ⟨.atom "true", rfl, ?_⟩
    rw [mapPacked_bool f.abstract, boolTerm_boolean]
    rfl
  by_cases hf : name = "false"
  · subst name
    have same : (⟨.bool, Uflia.Term.boolean false⟩ : PackedTerm E) = value := Option.some.inj decoded
    subst value
    refine ⟨.atom "false", rfl, ?_⟩
    rw [mapPacked_bool f.abstract, boolTerm_boolean]
    rfl
  rw [decodeAtom_eq fuel locals name ht hf] at decoded
  cases hl : local? locals name with
  | some term =>
    have same : term = value := Option.some.inj (by simpa only [hl] using decoded)
    subst term
    have hr := localsRelated_lookup f.abstract related name
    cases hs : syntaxLocal? syntaxLocals name with
    | none => simp [hl, hs] at hr
    | some output =>
      refine ⟨output, ?_, ?_⟩
      · rw [normalizeAtom_eq f.rename fuel syntaxLocals name ht hf, hs]
      · simpa only [hl, hs] using hr
  | none =>
    have hs := localsRelated_absent f.abstract related name hl
    simp only [hl] at decoded
    cases hn : numeral? (.atom name) with
    | some n =>
      have same : (⟨.int, Uflia.Term.integer n⟩ : PackedTerm E) = value :=
        Option.some.inj (by simpa only [hn] using decoded)
      subst value
      refine ⟨.atom name, ?_, ?_⟩
      · rw [normalizeAtom_eq f.rename fuel syntaxLocals name ht hf, hs, hn]
      · change decodeScopedFuel? F (0 + 1) [] (.atom name) = _
        rw [decodeAtom_eq 0 [] name ht hf]
        simp only [local?, hn]
        rw [mapPacked_int f.abstract, intTerm_integer]
    | none =>
      simp only [hn] at decoded
      cases hi : lookup? E name with
      | none => simp [applyUF?, hi] at decoded
      | some i =>
        have targetLookup := lookup_globalName f name i hi
        have targetReserved := (lookup_lexical targetLookup).2
        have targetNumeral := lookup_not_numeral targetLookup
        have mapped : applyUF? F
            (fun e => (decodeScopedFuel? E fuel locals e).map (mapPacked f.abstract))
            (globalName E f.rename name) [] = some (mapPacked f.abstract value) :=
          applyUF_transport f (fun _ _ h => by rw [h]; rfl) name [] value decoded
        refine ⟨.atom (globalName E f.rename name), ?_, ?_⟩
        · rw [normalizeAtom_eq f.rename fuel syntaxLocals name ht hf, hs, hn]
        · change decodeScopedFuel? F (0 + 1) [] (.atom (globalName E f.rename name)) = _
          rw [decodeAtomUF 0 _ targetReserved targetNumeral]
          exact (applyUF_empty_recur (decodeScopedFuel? F 0 [])
            (fun e => (decodeScopedFuel? E fuel locals e).map (mapPacked f.abstract)) _).trans mapped

/-- UF children may expand through lets; target decoding uses their actual sizes. -/
theorem normalizeUFApplication_success (f : NameMap E F) (fuel : Nat)
    (locals : Locals E) (syntaxLocals : SyntaxLocals)
    (related : LocalsRelated f.abstract locals syntaxLocals)
    (children : NormalizesAt f fuel locals syntaxLocals)
    (name : String) (args : List Expr) (absent : local? locals name = none) (nonempty : args ≠ [])
    (value : PackedTerm E)
    (h : applyUF? E (decodeScopedFuel? E fuel locals) name args = some value) :
    ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals (.list (.atom name :: args)) = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value) := by
  obtain ⟨values, hvalues⟩ := uf_source_exists _ name args value h
  obtain ⟨outputs, hn, hr⟩ := normalizedChildren f.abstract (decodeScopedFuel? E fuel locals)
    (normalizeFuel? E f.rename fuel syntaxLocals) children args values hvalues
  have mapped := applyUF_transport f
    (mappedSource_success f.abstract (decodeScopedFuel? E fuel locals)) name args value h
  have decoded := applyUF_related hr (globalName E f.rename name) (mapPacked f.abstract value) mapped
  have sourceLookup : ∃ i, lookup? E name = some i := by
    cases hi : lookup? E name with
    | none => simp [applyUF?, hi] at h
    | some i => exact ⟨i, rfl⟩
  obtain ⟨i, hi⟩ := sourceLookup
  have sourceReserved := (lookup_lexical hi).2
  have notLet : name ≠ "let" := by
    intro heq
    subst name
    simp [reserved] at sourceReserved
  have targetLookup := lookup_globalName f name i hi
  have targetReserved := (lookup_lexical targetLookup).2
  have targetNonempty : outputs ≠ [] := by
    intro hempty
    have sameLength := forall₂_length (List.mapM_eq_some_iff_forall₂.mp hn)
    rw [hempty, List.length_nil] at sameLength
    exact nonempty (List.eq_nil_of_length_eq_zero sameLength)
  refine ⟨.list (.atom (globalName E f.rename name) :: outputs), ?_, ?_⟩
  · rw [normalizeApplication_eq f.rename fuel syntaxLocals name args notLet
      (localsRelated_absent f.abstract related name absent), hn]
    rfl
  · change decodeScopedFuel? F ((1 + expressionsFuel outputs) + 1) []
      (.list (.atom (globalName E f.rename name) :: outputs)) = _
    rw [decodeApplicationUF _ _ outputs targetReserved targetNonempty]
    exact decoded

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
            obtain ⟨a', hn, hd⟩ := normalizeUnary_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) f.abstract.bool f.abstract.bool .not .not (operation_not_heq f.abstract) _ value h
            refine ⟨.list [.atom "not", a'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "not" (by decide) (by decide) [_] [a'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨a', hn, hd⟩ := normalizeUnary_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) f.abstract.int f.abstract.int (.scale (-1)) (.scale (-1)) (operation_scale_heq f.abstract (-1)) _ value h
            refine ⟨.list [.atom "-", a'], normalizeBuiltinApplication_success f fuel hlegal hrelated
              "-" (by decide) (by decide) [_] [a'] hn, ?_⟩
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) f.abstract.bool .and .and (operation_and_heq f.abstract) _ value h
            refine ⟨.list (.atom "and" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "and" (by decide) (by decide) _ outputs hn, ?_⟩
            change fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) .and outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) f.abstract.bool .or .or (operation_or_heq f.abstract) _ value h
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
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) f.abstract.int .add .add (operation_add_heq f.abstract) _ value h
            refine ⟨.list (.atom "+" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "+" (by decide) (by decide) _ outputs hn, ?_⟩
            change fold? (decodeTermFuel? F (1 + expressionsFuel outputs)) .add outputs = _
            exact hd
          · show ∃ output, normalizeFuel? E f.rename (fuel + 1) syntaxLocals _ = some output ∧
              decodeTermFuel? F (expressionFuel output) output = some (mapPacked f.abstract value)
            obtain ⟨outputs, hn, hd⟩ := normalizeFold_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) f.abstract.int .sub .sub (operation_sub_heq f.abstract) _ value h
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
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .le .le (operation_le_heq f.abstract) false _ value h
            refine ⟨.list (.atom "<=" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "<=" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .le false outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .lt .lt (operation_lt_heq f.abstract) false _ value h
            refine ⟨.list (.atom "<" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              "<" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .lt false outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .le .le (operation_le_heq f.abstract) true _ value h
            refine ⟨.list (.atom ">=" :: outputs), normalizeBuiltinApplication_success f fuel hlegal hrelated
              ">=" (by decide) (by decide) _ outputs hn, ?_⟩
            change compare? (decodeTermFuel? F (1 + expressionsFuel outputs)) .le true outputs = _
            exact hd
          ·
            obtain ⟨outputs, hn, hd⟩ := normalizeCompare_result f.abstract (decodeScopedFuel? E fuel locals) (normalizeFuel? E f.rename fuel syntaxLocals) (ih locals syntaxLocals hlegal hrelated) .lt .lt (operation_lt_heq f.abstract) true _ value h
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


/-- Every successfully decoded term has an actual capture-safe normalized
source in the target, with its mapped computed sort and typed term. -/
theorem normalizeTerm_success (f : NameMap E F) (e : Expr) (value : PackedTerm E)
    (h : decodeTerm? E e = some value) :
    ∃ output, normalize? E f.rename e = some output ∧
      decodeTerm? F output = some (mapPacked f.abstract value) := by
  have legal : LegalLocals ([] : Locals E) := by
    intro entry member
    contradiction
  exact normalizeScopedFuel_success f (expressionFuel e) [] [] legal .nil e value h

/-- Actual Boolean decoding commutes; this is proved, not a morphism field. -/
theorem normalizeFormula_success (f : NameMap E F) (e : Expr) (formula : Uflia.Formula E.signature)
    (h : decodeFormula? E e = some formula) :
    ∃ output, normalize? E f.rename e = some output ∧
      decodeFormula? F output = some (Hom.formula f.abstract formula) := by
  change (decodeTerm? E e).bind (fun value => value.expect? .bool) = some formula at h
  obtain ⟨value, hv, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨output, hn, hd⟩ := normalizeTerm_success f e value hv
  refine ⟨output, hn, ?_⟩
  change (decodeTerm? F output).bind (fun value => value.expect? .bool) = _
  rw [hd]
  have mapped := expect_at f.abstract value f.abstract.bool formula ht
  have same : termAt f.abstract f.abstract.bool formula = Hom.formula f.abstract formula :=
    eq_of_heq ((termAt_heq f.abstract f.abstract.bool formula).trans
      (closedTerm_formula_heq f.abstract formula))
  simpa only [Option.bind_some, same] using mapped


end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
