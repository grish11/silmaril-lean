module

public import Silmaril.Formats.SExp.Family.Defs
import Silmaril.Proofs.Formats.SExp.Family.Basic

/-!
# Tree families: laws

* `SExp.toAST` is injective, lands in the well-arity trees, and `AST.toSExp` inverts it there:
  proper S-expressions are exactly the well-arity trees of `sexpSig` (`SExp.equivAST`);
* a leaf with a child is not a well-arity tree (`leaf_children_not_wellArity`): the arity
  predicate is what separates atoms from internal nodes;
* dotted versus proper: `SExp2.toSExp?` is a partial inverse of `SExp.toSExp2`
  (`toSExp?_toSExp2`, `toSExp2_of_toSExp?`) defined exactly on the proper expressions
  (`isProper_iff_toSExp?`); improper lists `(a . b)` have no proper part;
* `HintedSExp.toSpki` is injective: hinted S-expressions embed in the RFC 9804 data model.
-/

@[expose] public section

namespace Silmaril.Formats

variable {α : Type}

@[simp] theorem SExp.toSExp_toAST (e : SExp α) : (SExp.toAST e).toSExp = e :=
  Silmaril.Proofs.Formats.SExp.Family.toSExp_toAST e

theorem SExp.toAST_wellArity (e : SExp α) : AST.WellArity (SExp.toAST e) :=
  Silmaril.Proofs.Formats.SExp.Family.toAST_wellArity e

theorem AST.toAST_toSExp {x : AST (sexpSig α)} (h : AST.WellArity x) :
    SExp.toAST x.toSExp = x :=
  Silmaril.Proofs.Formats.SExp.Family.toAST_toSExp x h

theorem SExp.toAST_injective : Function.Injective (SExp.toAST : SExp α → AST (sexpSig α)) :=
  Silmaril.Proofs.Formats.SExp.Family.toAST_injective

/-- **Proper S-expressions are the well-arity `sexpSig` trees.** -/
def SExp.equivAST (α : Type) : SExp α ≃ {x : AST (sexpSig α) // AST.WellArity x} where
  toFun e := ⟨SExp.toAST e, SExp.toAST_wellArity e⟩
  invFun x := x.1.toSExp
  left_inv e := SExp.toSExp_toAST e
  right_inv x := Subtype.ext (AST.toAST_toSExp x.2)

theorem leaf_children_not_wellArity (a : α) (c : AST (sexpSig α)) :
    ¬ AST.WellArity (AST.node (S := sexpSig α) SxTag.leaf a [c]) :=
  Silmaril.Proofs.Formats.SExp.Family.leaf_children_not_wellArity a c

theorem HintedSExp.toSpki_injective : Function.Injective HintedSExp.toSpki :=
  Silmaril.Proofs.Formats.SExp.Family.toSpki_injective

/-! ## Dotted and proper S-expressions -/

/-- Roundtrip: the proper part of an embedded proper S-expression is itself. -/
@[simp] theorem SExp2.toSExp?_toSExp2 (e : SExp α) : SExp2.toSExp? e.toSExp2 = some e := by
  have h : ∃ e' : SExp α, e'.toSExp2 = e.toSExp2 := ⟨e, rfl⟩
  simp only [SExp2.toSExp?, h, dite_true, Option.some.injEq]
  exact SExp.toSExp2_injective h.choose_spec

/-- Roundtrip: a proper part embeds back to the dotted S-expression. -/
theorem SExp2.toSExp2_of_toSExp? {x : SExp2 α} {e : SExp α} (h : SExp2.toSExp? x = some e) :
    e.toSExp2 = x := by
  unfold SExp2.toSExp? at h
  split at h
  · rename_i hx; cases h; exact hx.choose_spec
  · cases h

/-- **Properness is exactly having a proper part.** -/
theorem SExp2.isProper_iff_toSExp? (x : SExp2 α) :
    SExp2.IsProper x ↔ (SExp2.toSExp? x).isSome := by
  rw [SExp.proper_iff_exists]
  constructor
  · rintro ⟨e, rfl⟩; simp
  · intro h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
    exact ⟨e, SExp2.toSExp2_of_toSExp? he⟩

end Silmaril.Formats
