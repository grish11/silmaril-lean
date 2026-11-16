module

public import Silmaril.Formats.SExp.Family.Defs

/-! # Proofs: S-expressions are the well-arity trees of the S-expression signature -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Family

open Silmaril.Formats

variable {α : Type}

theorem toSExp_toAST : ∀ e : SExp α, (SExp.toAST e).toSExp = e := by
  intro e
  induction e with
  | atom a => rfl
  | list n cs ih =>
      simp only [SExp.toAST, AST.toSExp]
      exact congrArg (SExp.list n) (funext ih)

theorem toAST_wellArity : ∀ e : SExp α, AST.WellArity (SExp.toAST e) := by
  intro e
  induction e with
  | atom a => exact ⟨rfl, fun i => i.elim0⟩
  | list n cs ih => exact ⟨rfl, ih⟩

theorem toAST_toSExp : ∀ x : AST (sexpSig α), AST.WellArity x → SExp.toAST x.toSExp = x := by
  intro x
  induction x with
  | atom e => exact e.elim
  | tag v n cs ih =>
      obtain ⟨t, a⟩ := v
      cases t with
      | leaf =>
          intro h
          have hn : n = 0 := by simpa [sexpSig, Arity.Admits] using h.1
          subst hn
          simp only [AST.toSExp, SExp.toAST]
          exact congrArg (TExpr.tag _ 0) (funext fun i => i.elim0)
      | branch =>
          intro h
          cases a
          simp only [AST.toSExp, SExp.toAST]
          exact congrArg (TExpr.tag _ n) (funext fun i => ih i (h.2 i))

theorem toAST_injective : Function.Injective (SExp.toAST : SExp α → AST (sexpSig α)) := by
  intro a b h
  rw [← toSExp_toAST a, ← toSExp_toAST b, h]

theorem leaf_children_not_wellArity (a : α) (c : AST (sexpSig α)) :
    ¬ AST.WellArity (AST.node (S := sexpSig α) SxTag.leaf a [c]) := by
  intro h
  simp [AST.node, TExpr.ofList, AST.WellArity, sexpSig, Arity.Admits] at h

theorem toSpki_injective : Function.Injective HintedSExp.toSpki := by
  intro a
  induction a with
  | atom p =>
      intro b h
      cases b with
      | atom q =>
          obtain ⟨h1, o1⟩ := p; obtain ⟨h2, o2⟩ := q
          simp only [HintedSExp.toSpki, Spki.Sexp.atom.injEq] at h
          rw [h.1, h.2]
      | list m ds => simp [HintedSExp.toSpki] at h
  | list n cs ih =>
      intro b h
      cases b with
      | atom q => simp [HintedSExp.toSpki] at h
      | list m ds =>
          simp only [HintedSExp.toSpki, Spki.Sexp.list.injEq] at h
          have hlen : n = m := by simpa using congrArg List.length h
          subst hlen
          have : cs = ds := by
            funext i
            apply ih i
            have := congrArg (fun l => l[i]?) h
            simpa using this
          rw [this]

end Silmaril.Proofs.Formats.SExp.Family
