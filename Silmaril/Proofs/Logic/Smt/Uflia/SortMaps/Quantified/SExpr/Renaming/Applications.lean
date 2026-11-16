module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Core.Thms
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic Uflia.Quantified.SExpr
open Uflia.SExpr (Environment Expr Symbol lookup?)
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}
variable {f : environmentSignature E ⟶ environmentSignature F}

/-- Every argument is retained in its original position, with its mapped sort. -/
def mapArguments (f : environmentSignature E ⟶ environmentSignature F)
    (inputs : List (SortCode String))
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i)) :
    ∀ i, Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) ((inputs.map (fun s : SortCode String => (f.sorts s : SortCode String))).get i) :=
  fun i => cast (congrArg (Uflia.Quantified.Term F.signature (f.sorts ∘ Γ)) (by simp))
    (Hom.quantifiedTerm f (terms ⟨i.val, by simpa using i.isLt⟩))

private theorem fin_val_eq {n m : Nat} {i : Fin n} {j : Fin m} (hn : n = m) (h : HEq i j) :
    i.val = j.val := by
  cases hn
  cases eq_of_heq h
  rfl

theorem mapArguments_heq (f : environmentSignature E ⟶ environmentSignature F)
    (inputs : List (SortCode String))
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i)) :
    HEq (mapArguments f inputs terms) (fun i => Hom.quantifiedTerm f (terms i)) := by
  apply Function.hfunext (by simp)
  intro i j hij
  have hi : (⟨i.val, by simpa using i.isLt⟩ : Fin inputs.length) = j :=
    Fin.ext (fin_val_eq (i := i) (j := j) (by simp) hij)
  unfold mapArguments
  exact (cast_heq _ _).trans (by rw [hi])

/-- Consing arguments preserves their actual order, without an arity cap. -/
theorem mapArguments_cons (f : environmentSignature E ⟶ environmentSignature F)
    (input : SortCode String) (inputs : List (SortCode String))
    (term : Uflia.Quantified.Term E.signature Γ input)
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i)) :
    mapArguments f (input :: inputs) (Fin.cases term terms) =
      Fin.cases (Hom.quantifiedTerm f term) (mapArguments f inputs terms) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

/-- Successful source argument checks transport even when user sorts collapse. -/
theorem arguments_transport (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    (children : ∀ e t, source e = some t → target e = some (mapPacked f t))
    (inputs : List (SortCode String)) (es : List Expr)
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i))
    (decoded : decodeArguments? source inputs es = some terms) :
    decodeArguments? target (inputs.map (fun s : SortCode String => (f.sorts s : SortCode String))) es = some (mapArguments f inputs terms) := by
  dsimp only [environmentSignature] at f
  induction inputs generalizing es with
  | nil =>
    cases es with
    | nil =>
      change some (fun i : Fin 0 => i.elim0) = some _
      congr 1
      funext i
      exact i.elim0
    | cons e es => cases decoded
  | cons input inputs ih =>
    cases es with
    | nil => cases decoded
    | cons e es =>
      change (source e).bind _ = some terms at decoded
      obtain ⟨value, head, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      change (value.expect? input).bind _ = some terms at decoded
      obtain ⟨term, typed, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      change (decodeArguments? source inputs es).bind _ = some terms at decoded
      obtain ⟨tail, rest, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      cases Option.some.inj decoded
      have mappedTail := ih es tail rest
      change (target e).bind _ = _
      rw [children e value head]
      change ((mapPacked f value).expect? (f.sorts input)).bind _ = _
      rw [expect_mapPacked_of_eq f value term typed]
      change (decodeArguments? target _ es).bind _ = _
      rw [mappedTail]
      rw [mapArguments_cons]
      rfl

/-- Successful UF argument decoding has visited every source child. -/
theorem arguments_source_exists (source : Expr → Option (PackedTerm E Γ))
    (inputs : List (SortCode String)) (es : List Expr)
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i))
    (decoded : decodeArguments? source inputs es = some terms) :
    ∃ values, es.mapM source = some values := by
  induction inputs generalizing es with
  | nil =>
    cases es with
    | nil => exact ⟨[], rfl⟩
    | cons e es => simp [decodeArguments?] at decoded
  | cons input inputs ih =>
    cases es with
    | nil => simp [decodeArguments?] at decoded
    | cons e es =>
      change (source e).bind _ = some terms at decoded
      obtain ⟨value, head, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      change (value.expect? input).bind _ = some terms at decoded
      obtain ⟨term, typed, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      change (decodeArguments? source inputs es).bind _ = some terms at decoded
      obtain ⟨tail, decodedTail, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨values, decodedValues⟩ := ih es tail decodedTail
      exact ⟨value :: values, by simp [head, decodedValues]⟩

/-- Successful UF application decodes every argument, with no arity truncation. -/
theorem uf_source_exists (source : Expr → Option (PackedTerm E Γ))
    (name : String) (es : List Expr) (value : PackedTerm E Γ)
    (decoded : applyUF? E source name es = some value) :
    ∃ values, es.mapM source = some values := by
  change (lookup? E name).bind _ = some value at decoded
  obtain ⟨index, lookup, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  change (decodeArguments? source (E.declarations.get index).inputs es).bind _ = some value at decoded
  obtain ⟨terms, arguments, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  exact arguments_source_exists source _ es terms arguments

theorem arguments_related {source target : Expr → Option (PackedTerm E Γ)}
    {es outputs : List Expr} (related : List.Forall₂ ((fun a b => ∀ value, source a = some value → target b = some value)) es outputs)
    (inputs : List (SortCode String))
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i))
    (decoded : decodeArguments? source inputs es = some terms) :
    decodeArguments? target inputs outputs = some terms := by
  induction inputs generalizing es outputs with
  | nil =>
    cases related with
    | nil => exact decoded
    | cons head tail => simp [decodeArguments?] at decoded
  | cons input inputs ih =>
    cases related with
    | nil => simp [decodeArguments?] at decoded
    | @cons e output es outputs head tail =>
      cases he : source e with
      | none => simp [decodeArguments?, he] at decoded
      | some value =>
        simp only [decodeArguments?, he] at decoded
        change (value.expect? input).bind _ = some terms at decoded
        obtain ⟨term, typed, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        change (decodeArguments? source inputs es).bind _ = some terms at decoded
        obtain ⟨rest, decodedRest, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        have mappedRest := ih tail rest decodedRest
        simpa [decodeArguments?, head value he, typed, mappedRest] using decoded

theorem mapped_inputs_heq (f : environmentSignature E ⟶ environmentSignature F)
    (inputs : List (SortCode String)) :
    HEq (inputs.map (fun s : SortCode String => (f.sorts s : SortCode String))).get (f.sorts ∘ inputs.get) := by
  apply Function.hfunext (by simp)
  intro i j hij
  apply heq_of_eq
  simp only [Function.comp_apply, List.get_eq_getElem, List.getElem_map]
  congr 2
  exact fin_val_eq (by simp) hij

theorem symbol_type_eq {n m : Nat} {ss : Fin n → SortCode String}
    {tt : Fin m → SortCode String} {output : SortCode String}
    (hn : n = m) (hs : HEq ss tt) :
    Symbol F n ss output = Symbol F m tt output := by
  cases hn
  cases hs
  rfl

/-- Reprofile the actual mapped symbol, retaining its index and all input sorts. -/
def mapSymbol (f : environmentSignature E ⟶ environmentSignature F)
    {inputs : List (SortCode String)} {output : SortCode String}
    (symbol : Symbol E inputs.length inputs.get output) :
    Symbol F (inputs.map (fun s : SortCode String => (f.sorts s : SortCode String))).length (inputs.map (fun s : SortCode String => (f.sorts s : SortCode String))).get (f.sorts output) :=
  cast (symbol_type_eq (by simp) (mapped_inputs_heq f inputs).symm)
    (f.operations symbol)

theorem mapSymbol_heq (f : environmentSignature E ⟶ environmentSignature F)
    {inputs : List (SortCode String)} {output : SortCode String}
    (symbol : Symbol E inputs.length inputs.get output) :
    HEq (mapSymbol f symbol) (f.operations symbol) := cast_heq _ _

private theorem symbolIndex_heq {n m : Nat} {ss : Fin n → SortCode String}
    {tt : Fin m → SortCode String} {s t : SortCode String}
    {a : Symbol F n ss s} {b : Symbol F m tt t} (hn : n = m) (hs : HEq ss tt) (ht : s = t) (h : HEq a b) :
    Uflia.SExpr.Renaming.symbolIndex a = Uflia.SExpr.Renaming.symbolIndex b := by
  cases hn
  cases eq_of_heq hs
  cases ht
  cases eq_of_heq h
  rfl

private theorem uf_heq {n m : Nat} {ss : Fin n → SortCode String}
    {tt : Fin m → SortCode String} {s t : SortCode String}
    {a : Symbol F n ss s} {b : Symbol F m tt t} (hn : n = m) (hs : HEq ss tt) (ht : s = t) (h : HEq a b) :
    HEq (Operation.uf (A := F.signature) a) (Operation.uf (A := F.signature) b) := by
  cases hn
  cases eq_of_heq hs
  cases ht
  cases eq_of_heq h
  rfl

private theorem app_heq {n m : Nat} {ss : Fin n → SortCode String}
    {tt : Fin m → SortCode String} {s t : SortCode String}
    {a : Operation F.signature n ss s} {b : Operation F.signature m tt t}
    {argsA : ∀ i, Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) (ss i)}
    {argsB : ∀ i, Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) (tt i)} (hn : n = m) (hs : HEq ss tt) (ht : s = t) (hop : HEq a b) (hargs : HEq argsA argsB) :
    HEq (Uflia.Quantified.Term.app a argsA) (Uflia.Quantified.Term.app b argsB) := by
  cases hn
  cases eq_of_heq hs
  cases ht
  cases eq_of_heq hop
  cases eq_of_heq hargs
  rfl

private theorem symbol_inputs_list {n : Nat} {ss : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n ss output) :
    (E.declarations.get (Uflia.SExpr.Renaming.symbolIndex symbol)).inputs = List.ofFn ss := by
  cases symbol
  exact (List.ofFn_get _).symm

/-- Evaluate an actual symbol at its complete declaration profile. -/
def applyProfile? (inputs : List (SortCode String)) (output : SortCode String)
    (symbol : Symbol E inputs.length inputs.get output)
    (recur : Expr → Option (PackedTerm E Γ)) (es : List Expr) : Option (PackedTerm E Γ) := do
  let terms ← decodeArguments? recur inputs es
  pure ⟨output, .app (.uf symbol) terms⟩

theorem applyProfile_lookup (inputs : List (SortCode String)) (output : SortCode String)
    (symbol : Symbol E inputs.length inputs.get output)
    (recur : Expr → Option (PackedTerm E Γ)) (es : List Expr) (name : String)
    (lookup : lookup? E name = some (Uflia.SExpr.Renaming.symbolIndex symbol)) :
    applyProfile? inputs output symbol recur es = applyUF? E recur name es := by
  have hin := symbol_inputs_list symbol
  rw [List.ofFn_get] at hin
  have hout := Uflia.SExpr.Renaming.symbol_output symbol
  have hs := Uflia.SExpr.Renaming.symbol_reconstruct symbol
  generalize hj : Uflia.SExpr.Renaming.symbolIndex symbol = j at *
  cases hin
  cases hout
  have heq : Symbol.declared j = symbol := eq_of_heq hs
  subst symbol
  simp only [applyProfile?, applyUF?, lookup]
  rfl

/-- Genuine target lookup and its complete mapped profile justify UF transport. -/
theorem applyUF_transport (f : NameMap E F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F (f.abstract.sorts ∘ Γ))}
    (children : ∀ e t, source e = some t → target e = some (mapPacked f.abstract t))
    (name : String) (es : List Expr) (t : PackedTerm E Γ)
    (decoded : applyUF? E source name es = some t) :
    applyUF? F target (Uflia.SExpr.Renaming.globalName E f.rename name) es =
      some (mapPacked f.abstract t) := by
  cases lookup : lookup? E name with
  | none => simp [applyUF?, lookup] at decoded
  | some i =>
    obtain ⟨terms, arguments, same⟩ :
        ∃ terms, decodeArguments? source (E.declarations.get i).inputs es = some terms ∧
        (⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩ : PackedTerm E Γ) = t := by
      simpa [applyUF?, lookup, Option.bind_eq_some_iff] using decoded
    have mapped := arguments_transport f.abstract children _ es terms arguments
    have index := symbolIndex_heq (by simp) (mapped_inputs_heq _ _) rfl (mapSymbol_heq f.abstract (.declared i))
    have targetLookup := SortMaps.SExpr.Renaming.lookup_globalName f.toNameMap name i lookup
    rw [← index] at targetLookup
    rw [← applyProfile_lookup _ _ (mapSymbol f.abstract (.declared i)) target es _ targetLookup]
    simp only [applyProfile?, mapped]
    change some _ = some _
    rw [← same]
    congr 1
    change (⟨f.abstract.sorts (E.declarations.get i).output, _⟩ : PackedTerm F (f.abstract.sorts ∘ Γ)) = _
    unfold mapPacked
    rw [quantifiedTerm_app]
    apply congrArg (fun term => (⟨f.abstract.sorts (E.declarations.get i).output, term⟩ : PackedTerm F (f.abstract.sorts ∘ Γ)))
    apply eq_of_heq
    exact app_heq (by simp) (mapped_inputs_heq _ _) rfl (uf_heq (by simp) (mapped_inputs_heq _ _) rfl (mapSymbol_heq f.abstract (.declared i)))
      (mapArguments_heq f.abstract _ terms)

/-- Changing syntax retains every ordered argument and its transported sort. -/
theorem arguments_syntax (f : environmentSignature E ⟶ environmentSignature F)
    {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.sorts ∘ Γ))}
    {es outputs : List Expr}
    (related : List.Forall₂ (fun e output => ∀ value,
      (source e).map (mapPacked f) = some value → target output = some value) es outputs)
    (inputs : List (SortCode String))
    (terms : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs.get i))
    (decoded : decodeArguments? source inputs es = some terms) :
    decodeArguments? target (inputs.map (fun s => f.sorts s)) outputs =
      some (mapArguments f inputs terms) := by
  apply arguments_related related
  exact arguments_transport f (by intro e t h; simp [h]) inputs es terms decoded

/-- Actual global lookup, full mapped profiles and transformed child syntax. -/
theorem uf_syntax (f : NameMap E F)
    {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F (f.abstract.sorts ∘ Γ))}
    {es outputs : List Expr}
    (related : List.Forall₂ (fun e output => ∀ value,
      (source e).map (mapPacked f.abstract) = some value → target output = some value) es outputs)
    (name : String) (value : PackedTerm E Γ)
    (decoded : applyUF? E source name es = some value) :
    applyUF? F target (f.rename name) outputs = some (mapPacked f.abstract value) := by
  cases lookup : lookup? E name with
  | none => simp [applyUF?, lookup] at decoded
  | some i =>
    obtain ⟨terms, arguments, same⟩ :
        ∃ terms, decodeArguments? source (E.declarations.get i).inputs es = some terms ∧
          (⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩ : PackedTerm E Γ) = value := by
      simpa [applyUF?, lookup, Option.bind_eq_some_iff] using decoded
    have mapped := arguments_syntax f.abstract related _ terms arguments
    have index := symbolIndex_heq (by simp) (mapped_inputs_heq _ _) rfl
      (mapSymbol_heq f.abstract (.declared i))
    have targetLookup := f.lookup name i lookup
    rw [← index] at targetLookup
    rw [← applyProfile_lookup _ _ (mapSymbol f.abstract (.declared i)) target outputs _ targetLookup]
    simp only [applyProfile?, mapped]
    change some _ = some _
    rw [← same]
    congr 1
    change (⟨f.abstract.sorts (E.declarations.get i).output, _⟩ :
      PackedTerm F (f.abstract.sorts ∘ Γ)) = _
    unfold mapPacked
    rw [quantifiedTerm_app]
    apply congrArg (fun term => (⟨f.abstract.sorts (E.declarations.get i).output, term⟩ :
      PackedTerm F (f.abstract.sorts ∘ Γ)))
    apply eq_of_heq
    exact app_heq (by simp) (mapped_inputs_heq _ _) rfl
      (uf_heq (by simp) (mapped_inputs_heq _ _) rfl (mapSymbol_heq f.abstract (.declared i)))
      (mapArguments_heq f.abstract _ terms)

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
