module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryQuotation

/-! # Native quotation of a query with live typed continuations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Removing a weakened binder by substitution recovers the original region. -/
theorem drop_weakening (r : Region signature.Instr) (a : Tm signature.Instr) :
    (r.renameVars Nat.succ).substVars (Tm.singleSubst a) = r :=
  BitQueryQuotation.drop_weakening r a

/-- Compare pure queries at any finite collection of distinct typed slots.
The arbitrary continuations keep the original context and outward labels. -/
theorem choose_eq {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e f : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L)
    (equal : ∀ env, e.eval env = f.eval env) :
    Extension.Eqv Seed Γ (choose e slots.terms l r) (choose f slots.terms l r) L :=
  BitQueryQuotation.choose_eq slots e f hl hr equal

/-- Quote the query in fixed slot order with its original continuations. -/
theorem quote_choose {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L) :
    Extension.Eqv Seed Γ (choose e slots.terms l r) (choose (Expr.quote n e.eval) slots.terms l r) L :=
  BitQueryQuotation.quote_choose slots e hl hr

/-- Replay the quoted tree at any typed lexical interface, under all reply binders. -/
theorem region_replay {n : Nat} (t : Tree n) {Γ : VCtx (Ty Empty)} (slots : Slots Γ n) :
    Extension.Eqv Seed Γ (t.region slots) (t.key.region slots) Exits :=
  BitQueryQuotation.region_replay t slots

/-- The recorded pure guard only supplies its constructor, preserving the open arrow. -/
theorem packed_unguarded (t : Tree 1) :
    t.packed = Extension.Singleton.ofRegion Seed (t.typed inputSlots).packExits :=
  BitQueryQuotation.packed_unguarded t

theorem packed_replay (t : Tree 1) : t.packed = t.key.packed :=
  BitQueryQuotation.packed_replay t

/-- Equal structural keys suffice for native equality of the original packed arrows. -/
theorem packed_eq_of_key {t u : Tree 1} (h : t.key = u.key) : t.packed = u.packed :=
  (packed_replay t).trans ((congrArg Tree.packed h).trans (packed_replay u).symm)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
