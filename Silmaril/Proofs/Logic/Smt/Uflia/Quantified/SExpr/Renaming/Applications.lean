module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Operators
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}

/-- Successful UF argument decoding has visited every source child. -/
theorem arguments_source_exists (source : Expr → Option (PackedTerm E Γ))
    (inputs : List (SortCode String)) (es : List Expr)
    (terms : ∀ i, Term E.signature Γ (inputs.get i))
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

/-- Corresponding argument expressions preserve their complete typed profile. -/
theorem arguments_related {source target : Expr → Option (PackedTerm E Γ)}
    {es outputs : List Expr} (related : List.Forall₂ (DecodeRelated source target) es outputs)
    (inputs : List (SortCode String))
    (terms : ∀ i, Term E.signature Γ (inputs.get i))
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

theorem arguments_syntax (f : E.signature ⟶ F.signature)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F Γ)}
    {es outputs : List Expr}
    (related : List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs)
    (inputs : List (SortCode String)) (terms : ∀ i, Term E.signature Γ (inputs.get i))
    (decoded : decodeArguments? source inputs es = some terms) :
    decodeArguments? target inputs outputs = some (fun i => (terms i).map f) := by
  apply arguments_related related
  rw [arguments_map, decoded]
  rfl

private theorem symbol_inputs {n : Nat} {inputs : Fin n → SortCode String}
    {output : SortCode String} (symbol : Symbol E n inputs output) :
    (E.declarations.get (Uflia.SExpr.Renaming.symbolIndex symbol)).inputs = List.ofFn inputs := by
  cases symbol
  exact (List.ofFn_get _).symm

def applyProfile? (inputs : List (SortCode String)) (output : SortCode String)
    (symbol : Symbol E inputs.length inputs.get output)
    (recur : Expr → Option (PackedTerm E Γ)) (es : List Expr) : Option (PackedTerm E Γ) := do
  let terms ← decodeArguments? recur inputs es
  pure ⟨output, .app (.uf symbol) terms⟩

/-- Reconstruct the WHOLE typed declaration profile, not merely its index.
Ported from the existing ground applyProfile_lookup at pinned main a290. -/
theorem applyProfile_lookup (inputs : List (SortCode String)) (output : SortCode String)
    (symbol : Symbol E inputs.length inputs.get output)
    (recur : Expr → Option (PackedTerm E Γ)) (es : List Expr) (name : String)
    (lookup : lookup? E name = some (Uflia.SExpr.Renaming.symbolIndex symbol)) :
    applyProfile? inputs output symbol recur es = applyUF? E recur name es := by
  have hin := symbol_inputs symbol
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

/-- Actual selected global applications transport along arbitrary coherent
maps, including symbol identifications and quantified Boolean arguments. -/
theorem uf_syntax (f : NameMap E F)
    {source : Expr → Option (PackedTerm E Γ)} {target : Expr → Option (PackedTerm F Γ)}
    {es outputs : List Expr}
    (related : List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f.abstract)) target) es outputs)
    (name : String) (value : PackedTerm E Γ) (decoded : applyUF? E source name es = some value) :
    applyUF? F target (f.rename name) outputs = some (mapPacked f.abstract value) := by
  cases lookup : lookup? E name with
  | none => simp [applyUF?, lookup] at decoded
  | some i =>
    have shape : ∃ terms, decodeArguments? source (E.declarations.get i).inputs es = some terms ∧
        (⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩ : PackedTerm E Γ) = value := by
      simpa [applyUF?, lookup, Option.bind_eq_some_iff] using decoded
    obtain ⟨terms, arguments, same⟩ := shape
    have mapped := arguments_syntax f.abstract related _ terms arguments
    rw [← applyProfile_lookup _ _ (f.abstract.operations (.declared i)) target outputs
      (f.rename name) (f.lookup name i lookup)]
    simp only [applyProfile?, mapped]
    rw [← same]
    rfl

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
