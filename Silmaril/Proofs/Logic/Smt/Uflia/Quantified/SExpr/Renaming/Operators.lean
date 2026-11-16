module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Related

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment} (f : E.signature ⟶ F.signature)
variable {k : Nat} {Γ : Fin k → SortCode String}

/-- Successful source children produce actual transformed expressions with the
mapped decoding relation, at the SAME caller-supplied target recursion budget. -/
theorem renameChildren_success
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F Γ))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f value))
    (es : List Expr) (decoded : ∃ values, es.mapM source = some values) :
    ∃ outputs, es.mapM rename = some outputs ∧
      List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs := by
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

theorem unary_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)}
    {input output} (op : Operation E.signature 1 (fun _ => input) output)
    (a a' : Expr) (related : DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (value : PackedTerm E Γ) (decoded : unary? source op a = some value) :
    unary? target (Operation.map f op) a' = some (mapPacked f value) := by
  apply unary_related (Operation.map f op) a a' related
  rw [unary_map, decoded]
  rfl

theorem implication_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)} (a a' b b' : Expr)
    (ra : DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (rb : DecodeRelated (fun e => (source e).map (mapPacked f)) target b b')
    (value : PackedTerm E Γ) (decoded : implication? source a b = some value) :
    implication? target a' b' = some (mapPacked f value) := by
  apply implication_related a a' b b' ra rb
  rw [implication_map, decoded]
  rfl

theorem xor_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)} (a a' b b' : Expr)
    (ra : DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (rb : DecodeRelated (fun e => (source e).map (mapPacked f)) target b b')
    (value : PackedTerm E Γ) (decoded : xor? source a b = some value) :
    xor? target a' b' = some (mapPacked f value) := by
  apply xor_related a a' b b' ra rb
  rw [xor_map, decoded]
  rfl

theorem ite_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)} (c c' a a' b b' : Expr)
    (rc : DecodeRelated (fun e => (source e).map (mapPacked f)) target c c')
    (ra : DecodeRelated (fun e => (source e).map (mapPacked f)) target a a')
    (rb : DecodeRelated (fun e => (source e).map (mapPacked f)) target b b')
    (value : PackedTerm E Γ) (decoded : ite? source c a b = some value) :
    ite? target c' a' b' = some (mapPacked f value) := by
  apply ite_related c c' a a' b b' rc ra rb
  rw [ite_map, decoded]
  rfl

theorem fold_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)} {sort}
    (op : Operation E.signature 2 (fun _ => sort) sort) {es outputs : List Expr}
    (related : List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : fold? source op es = some value) :
    fold? target (Operation.map f op) outputs = some (mapPacked f value) := by
  apply fold_related related (Operation.map f op)
  rw [fold_map, decoded]
  rfl

theorem compare_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)}
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool) {es outputs : List Expr}
    (related : List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : compare? source op reverse es = some value) :
    compare? target (Operation.map f op) reverse outputs = some (mapPacked f value) := by
  apply compare_related related (Operation.map f op) reverse
  rw [compare_map, decoded]
  rfl

theorem equalities_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)} (distinct : Bool) {es outputs : List Expr}
    (related : List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : equalities? source distinct es = some value) :
    equalities? target distinct outputs = some (mapPacked f value) := by
  apply equalities_related related distinct
  rw [equalities_map, decoded]
  rfl

theorem multiply_syntax {source : Expr → Option (PackedTerm E Γ)}
    {target : Expr → Option (PackedTerm F Γ)} {es outputs : List Expr}
    (related : List.Forall₂ (DecodeRelated (fun e => (source e).map (mapPacked f)) target) es outputs)
    (value : PackedTerm E Γ) (decoded : multiply? source es = some value) :
    multiply? target outputs = some (mapPacked f value) := by
  apply multiply_related related
  rw [multiply_map, decoded]
  rfl

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
