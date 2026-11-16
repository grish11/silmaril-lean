module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
open Uflia.SExpr
variable {E F : Environment}

/-- Lookup coherence uses actual target indices, not just equal printed names. -/
theorem lookup_globalName (f : NameMap E F) (name : String)
    (i : Fin E.declarations.length) (h : lookup? E name = some i) :
    lookup? F (Uflia.SExpr.Renaming.globalName E f.rename name) = some
      (Uflia.SExpr.Renaming.symbolIndex (f.abstract.operations (.declared i))) := by
  simpa [Uflia.SExpr.Renaming.globalName, h] using f.lookup name i h

/-- The selected target declaration has exactly the mapped result sort. -/
theorem target_output (f : NameMap E F) (i : Fin E.declarations.length) :
    (F.declarations.get
      (Uflia.SExpr.Renaming.symbolIndex (f.abstract.operations (.declared i)))).output =
        f.abstract.sorts (E.declarations.get i).output :=
  Uflia.SExpr.Renaming.symbol_output _

/-- Transport retains arity even when distinct source sorts are identified. -/
theorem target_arity (f : NameMap E F) (i : Fin E.declarations.length) :
    (F.declarations.get
      (Uflia.SExpr.Renaming.symbolIndex (f.abstract.operations (.declared i)))).inputs.length =
        (E.declarations.get i).inputs.length :=
  Uflia.SExpr.Renaming.symbol_arity _

theorem closedTerm_heq (f : environmentSignature E ⟶ environmentSignature F)
    {s : SortCode String} (t : Uflia.Term E.signature s) :
    HEq (closedTerm f t) (Hom.term f t) := by
  unfold closedTerm
  exact cast_heq _ _

@[simp] theorem mapPacked_sort (f : environmentSignature E ⟶ environmentSignature F)
    (t : PackedTerm E) : (mapPacked f t).sort = f.sorts t.sort := rfl

/-- Only successful checks transport. Their converse would require sort
injectivity, which is deliberately not part of a varying-sort signature map. -/
theorem expect_mapPacked_of_eq (f : environmentSignature E ⟶ environmentSignature F)
    (t : PackedTerm E) {s : SortCode String} (v : Uflia.Term E.signature s)
    (h : t.expect? s = some v) :
    (mapPacked f t).expect? (f.sorts s) = some (closedTerm f v) := by
  rcases t with ⟨sort, term⟩
  unfold PackedTerm.expect? at h
  split at h
  next hs =>
    change sort = s at hs
    subst sort
    change some term = some v at h
    cases Option.some.inj h
    unfold mapPacked PackedTerm.expect?
    exact dite_eq_left rfl
  next hs => simp at h

/-- The Boolean result cast agrees with the existing abstract formula map. -/
theorem closedTerm_formula_heq (f : environmentSignature E ⟶ environmentSignature F)
    (p : Uflia.Formula E.signature) :
    HEq (closedTerm f p) (Hom.formula f p) :=
  (closedTerm_heq f p).trans (Hom.formula_heq f p).symm

/-- Every closed application retains its mapped operation and ordered arguments;
heterogeneous equality exposes only the empty-context cast. -/
theorem closedTerm_app_heq (f : environmentSignature E ⟶ environmentSignature F)
    {n : Nat} {inputs : Fin n → SortCode String} {output : SortCode String}
    (op : Operation E.signature n inputs output)
    (args : ∀ i, Uflia.Term E.signature (inputs i)) :
    HEq (closedTerm f (.app op args))
      (ManySorted.Term.app (Hom.operation f op) (fun i => Hom.term f (args i))) :=
  closedTerm_heq f (.app op args)

private theorem cast_app {Γ Δ : Fin 0 → SortCode String} (h : Γ = Δ)
    {n : Nat} {inputs : Fin n → SortCode String} {output : SortCode String}
    (op : Operation F.signature n inputs output)
    (args : ∀ i, ManySorted.Term F.signature.expanded Γ (inputs i)) :
    cast (congrArg (fun ctx => ManySorted.Term F.signature.expanded ctx output) h)
      (.app op args) =
    .app op (fun i => cast
      (congrArg (fun ctx => ManySorted.Term F.signature.expanded ctx (inputs i)) h) (args i)) := by
  cases h
  rfl

/-- Empty-context transport commutes with every application, preserving order. -/
theorem closedTerm_app (f : environmentSignature E ⟶ environmentSignature F)
    {n : Nat} {inputs : Fin n → SortCode String} {output : SortCode String}
    (op : Operation E.signature n inputs output)
    (args : ∀ i, Uflia.Term E.signature (inputs i)) :
    closedTerm f (.app op args) =
      .app (Hom.operation f op) (fun i => closedTerm f (args i)) :=
  cast_app (Hom.sorts_empty f) (Hom.operation f op) (fun i => Hom.term f (args i))

/-- Recover the complete dependent input family of an actual declaration. -/
theorem symbol_inputs {n : Nat} {inputs : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n inputs output) :
    HEq (E.declarations.get (Uflia.SExpr.Renaming.symbolIndex symbol)).inputs.get inputs := by
  cases symbol
  rfl

/-- Each target input has the mapped source sort, with its actual arity. -/
theorem target_inputs (f : NameMap E F) (i : Fin E.declarations.length) :
    HEq (F.declarations.get
      (Uflia.SExpr.Renaming.symbolIndex (f.abstract.operations (.declared i)))).inputs.get
      (f.abstract.sorts ∘ (E.declarations.get i).inputs.get) :=
  symbol_inputs _

private theorem eval_heq (M : Model F.signature)
    {Γ Δ : Fin 0 → SortCode String} {s : SortCode String}
    (hΓ : Γ = Δ) (p : ManySorted.Term F.signature.expanded Γ s)
    (q : ManySorted.Term F.signature.expanded Δ s) (hp : HEq p q)
    (v : ∀ i, M.carriers.value (Γ i)) (w : ∀ i, M.carriers.value (Δ i)) :
    M.algebra.eval v p = M.algebra.eval w q := by
  cases hΓ
  cases eq_of_heq hp
  have same : v = w := funext (fun i => i.elim0)
  rw [same]

/-- Evaluation uses the actual sort-map model reduct, including U→Bool/Int. -/
theorem eval_closedTerm (f : environmentSignature E ⟶ environmentSignature F)
    (M : Model F.signature) {s : SortCode String} (t : Uflia.Term E.signature s) :
    M.eval (closedTerm f t) = Hom.value f M s ((Hom.reduct f M).eval t) := by
  have ev := Hom.eval_term f M t (fun i => i.elim0)
  apply Eq.trans ?_ ev.symm
  exact eval_heq M (Hom.sorts_empty f).symm
    (closedTerm f t) (Hom.term f t) (closedTerm_heq f t) _ _

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
