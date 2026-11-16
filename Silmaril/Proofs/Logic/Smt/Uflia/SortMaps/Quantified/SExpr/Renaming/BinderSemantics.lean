module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.BinderSemantics.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Uflia.SExpr Uflia.Quantified.SExpr
variable {E F : Environment}

theorem castPacked_heq {k : Nat} {Γ Δ : Fin k → SortCode String}
    (h : Γ = Δ) (value : PackedTerm E Γ) : HEq (castPacked h value) value := by
  cases h
  rfl

theorem packed_heq {k : Nat} {Γ Δ : Fin k → SortCode String} {s t : SortCode String}
    (hΓ : Γ = Δ) (hs : s = t)
    (p : Uflia.Quantified.Term E.signature Γ s)
    (q : Uflia.Quantified.Term E.signature Δ t) (hp : HEq p q) :
    HEq (⟨s, p⟩ : PackedTerm E Γ) (⟨t, q⟩ : PackedTerm E Δ) := by
  cases hΓ
  cases hs
  cases eq_of_heq hp
  rfl

private theorem var_heq {k : Nat} {Γ Δ : Fin k → SortCode String}
    (h : Γ = Δ) (i : Fin k) :
    HEq (.var i : Uflia.Quantified.Term E.signature Γ (Γ i))
      (.var i : Uflia.Quantified.Term E.signature Δ (Δ i)) := by
  cases h
  rfl

theorem castPacked_weaken (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (value : PackedTerm E Γ)
    (sort : SortCode String) :
    castPacked (Hom.sorts_cons f sort Γ)
      (mapPacked f ⟨value.sort, value.term.weaken sort⟩) =
      ⟨f.sorts value.sort, (Hom.quantifiedTerm f value.term).weaken (f.sorts sort)⟩ := by
  apply eq_of_heq
  exact (castPacked_heq _ _).trans (packed_heq (Hom.sorts_cons f sort Γ) rfl _ _
    (quantifiedTerm_weaken_heq f value.term sort))

/-- After the explicit context cast, the target binder is index zero and all
previous target values are weakened under its actual mapped sort. -/
theorem targetLocals_pushBinder {k : Nat} {Γ : Fin k → SortCode String}
    (f : environmentSignature E ⟶ environmentSignature F) (locals : List (Local E Γ))
    (next : Nat) (name : String) (sort : SortCode String) :
    castLocals (Hom.sorts_cons f sort Γ) (targetLocals f (pushBinder locals next name sort)) =
      (freshName next, ⟨f.sorts sort, .var 0⟩) :: (targetLocals f locals).map
        (fun entry => (entry.1, ⟨entry.2.sort, entry.2.term.weaken (f.sorts sort)⟩)) := by
  simp only [castLocals, targetLocals, pushBinder, List.map_cons, List.map_map,
    Function.comp_def, weakenLocal]
  congr 1
  · congr 1
    apply eq_of_heq
    exact (castPacked_heq _ _).trans (packed_heq (Hom.sorts_cons f sort Γ) rfl _ _
      (var_heq (Hom.sorts_cons f sort Γ) 0))
  · apply List.map_congr_left
    intro entry _
    congr 1
    exact castPacked_weaken f entry.value sort

/-- Quantification respects equality transport of the entire lexical context. -/
theorem quantify_cast (universal : Bool)
    (target : ∀ {k : Nat} {Γ : Fin k → SortCode String},
      Uflia.Quantified.SExpr.Locals F Γ → Expr → Option (PackedTerm F Γ))
    {k : Nat} {Γ Δ : Fin k → SortCode String} (h : Γ = Δ)
    (locals : Uflia.Quantified.SExpr.Locals F Γ)
    (bindings : List (String × SortCode String)) (body : Expr) :
    quantify? F universal target (castLocals h locals) bindings body =
      (quantify? F universal target locals bindings body).map (castPacked h) := by
  cases h
  have packedId : castPacked (E := F) (rfl : Γ = Γ) = id := by
    funext value
    cases value
    rfl
  have localsId : castLocals (rfl : Γ = Γ) locals = locals := by
    calc
      castLocals (rfl : Γ = Γ) locals = locals.map id := by
        apply List.map_congr_left
        intro entry _
        rw [packedId]
        cases entry
        rfl
      _ = locals := List.map_id locals
  rw [localsId, packedId]
  exact (congrFun Option.map_id _).symm

theorem expect_heq {k : Nat} {Γ Δ : Fin k → SortCode String} {s t : SortCode String}
    (hΓ : Γ = Δ) (hs : s = t) (v : PackedTerm F Γ) (w : PackedTerm F Δ)
    (hv : HEq v w) (p : Uflia.Quantified.Term F.signature Γ s)
    (q : Uflia.Quantified.Term F.signature Δ t) (hp : HEq p q)
    (checked : v.expect? s = some p) : w.expect? t = some q := by
  cases hΓ
  cases hs
  cases eq_of_heq hv
  cases eq_of_heq hp
  exact checked

/-- General binder-list transport in every open source context. -/
theorem quantify_success (f : NameMap E F) (universal : Bool)
    (source : ∀ {k : Nat} {Γ : Fin k → SortCode String},
      Uflia.Quantified.SExpr.Locals E Γ → Expr → Option (PackedTerm E Γ))
    (target : ∀ {k : Nat} {Γ : Fin k → SortCode String},
      Uflia.Quantified.SExpr.Locals F Γ → Expr → Option (PackedTerm F Γ))
    (rename : Scope → Nat → Expr → Option Expr)
    (bodySuccess : ∀ {k : Nat} {Γ : Fin k → SortCode String}
      (locals : List (Local E Γ)) (next : Nat), ValidScope F next locals → firstFresh F ≤ next →
      ∀ body value, source (sourceLocals locals) body = some value → ∃ output,
        rename (localScope locals) next body = some output ∧
          target (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    {k : Nat} {Γ : Fin k → SortCode String} (locals : List (Local E Γ))
    (next : Nat) (valid : ValidScope F next locals) (bound : firstFresh F ≤ next)
    (bindings : List (String × SortCode String)) (body : Expr) (value : PackedTerm E Γ)
    (decoded : quantify? E universal source (sourceLocals locals) bindings body = some value) :
    ∃ output, rename ((binderScope next bindings).reverse ++ localScope locals)
        (next + bindings.length) body = some output ∧
      quantify? F universal target (targetLocals f.abstract locals)
        (freshBinderTypes f.abstract next bindings) output = some (mapPacked f.abstract value) := by
  induction bindings generalizing k Γ locals next value with
  | nil =>
    simpa only [binderScope, freshBinderTypes, List.reverse_nil, List.nil_append, List.length_nil,
      Nat.add_zero, quantify?] using bodySuccess locals next valid bound body value decoded
  | cons binding bindings ih =>
    rcases binding with ⟨name, sort⟩
    change (quantify? E universal source
      ((name, ⟨sort, .var 0⟩) :: (sourceLocals locals).map
        (fun entry => (entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩))) bindings body).bind _ = some value at decoded
    rw [← sourceLocals_pushBinder locals next name sort] at decoded
    obtain ⟨inner, decodedInner, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    change (inner.expect? .bool).bind _ = some value at decoded
    obtain ⟨term, typed, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    have same : (⟨.bool, if universal then .all sort term else .ex sort term⟩ : PackedTerm E Γ) = value :=
      Option.some.inj decoded
    subst value
    obtain ⟨output, renamed, mapped⟩ := ih (pushBinder locals next name sort) (next + 1)
      (pushBinder_valid locals next valid bound name sort) (by omega) inner decodedInner
    refine ⟨output, ?_, ?_⟩
    · simpa [binderScope, pushBinder, localScope, weakenLocal, Function.comp_def,
        List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using renamed
    · have mapped' := congrArg (Option.map (castPacked (Hom.sorts_cons f.abstract sort Γ))) mapped
      rw [← quantify_cast universal target, targetLocals_pushBinder] at mapped'
      have checked := expect_heq (Hom.sorts_cons f.abstract sort Γ) f.abstract.bool
        (mapPacked f.abstract inner)
        (castPacked (Hom.sorts_cons f.abstract sort Γ) (mapPacked f.abstract inner))
        (castPacked_heq _ _).symm (Hom.quantifiedTerm f.abstract term)
        (Hom.quantifiedBody f.abstract sort (Hom.quantifiedTerm f.abstract term))
        (quantifiedBody_heq f.abstract sort _).symm
        (expect_mapPacked_of_eq f.abstract inner term typed)
      simp only [freshBinderTypes, quantify?, mapped', Option.map_some, bind, pure,
        Option.bind_some, checked]
      apply congrArg some
      apply eq_of_heq
      cases universal with
      | false => exact (packed_heq rfl f.abstract.bool _ _
          (quantifiedTerm_ex_heq f.abstract sort term)).symm
      | true => exact (packed_heq rfl f.abstract.bool _ _
          (quantifiedTerm_all_heq f.abstract sort term)).symm

/-- Assemble a complete quantifier constructor from admitted original binders
and one recursive body transport. No injectivity of global names is used. -/
theorem renameQuantifier_success (f : NameMap E F) (fuel : Nat)
    (bodySuccess : ∀ {k : Nat} {Γ : Fin k → SortCode String}
      (locals : List (Local E Γ)) (next : Nat), ValidScope F next locals → firstFresh F ≤ next →
      ∀ body value, decodeScopedFuel? E fuel (sourceLocals locals) body = some value → ∃ output,
        renameScopedFuel? f fuel (localScope locals) next body = some output ∧
          decodeScopedFuel? F fuel (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    {k : Nat} {Γ : Fin k → SortCode String} (locals : List (Local E Γ))
    (next : Nat) (valid : ValidScope F next locals) (bound : firstFresh F ≤ next)
    (universal : Bool) (head : Expr) (rest : List Expr)
    (parsed : List (String × SortCode String))
    (parsedBinders : binders? E (head :: rest) = some parsed)
    (body : Expr) (value : PackedTerm E Γ)
    (decoded : quantify? E universal (fun locals body => decodeScopedFuel? E fuel locals body)
      (sourceLocals locals) parsed body = some value) :
    ∃ output,
      renameScopedFuel? f (fuel + 1) (localScope locals) next
        (.list [.atom (if universal then "forall" else "exists"), .list (head :: rest), body]) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output =
        some (mapPacked f.abstract value) := by
  obtain ⟨bindings, renamedBinders, targetBinders, lengths, parsedLengths⟩ :=
    renameBinders_success f (head :: rest) parsed parsedBinders next
  obtain ⟨output, renamedBody, mappedBody⟩ := quantify_success f universal
    (fun locals body => decodeScopedFuel? E fuel locals body)
    (fun locals body => decodeScopedFuel? F fuel locals body)
    (renameScopedFuel? f fuel) bodySuccess locals next valid bound parsed body value decoded
  have bodyRename : renameScopedFuel? f fuel
      ((binderScope next parsed).reverse ++ localScope locals) (next + (head :: rest).length) body = some output := by
    simpa only [parsedLengths] using renamedBody
  cases bindings with
  | nil => simp at lengths
  | cons targetHead targetRest =>
    cases universal with
    | false =>
      refine ⟨.list [.atom "exists", .list (targetHead :: targetRest), output], ?_, ?_⟩
      · change (renameBinders? f next (head :: rest)).bind _ = _
        rw [renamedBinders]
        change (renameScopedFuel? f fuel _ _ body).bind _ = _
        rw [bodyRename]
        rfl
      · change (binders? F (targetHead :: targetRest)).bind _ = _
        rw [targetBinders]
        exact mappedBody
    | true =>
      refine ⟨.list [.atom "forall", .list (targetHead :: targetRest), output], ?_, ?_⟩
      · change (renameBinders? f next (head :: rest)).bind _ = _
        rw [renamedBinders]
        change (renameScopedFuel? f fuel _ _ body).bind _ = _
        rw [bodyRename]
        rfl
      · change (binders? F (targetHead :: targetRest)).bind _ = _
        rw [targetBinders]
        exact mappedBody

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
