module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryQuotation

/-! # Native quotation of a query with live typed continuations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Removing a weakened binder by substitution recovers the original region. -/
theorem drop_weakening (r : Region signature.Instr) (a : Tm signature.Instr) :
    (r.renameVars Nat.succ).substVars (Tm.singleSubst a) = r :=
  BitQueryQuotation.drop_weakening r a

/-- Expose both constructors of the exact live Bit slot and retain each
branch's original unit payload. -/
theorem native_focus_bit {Γ L : List (Ty Empty)} {r : Region signature.Instr} {i : Nat}
    (hi : At Γ i Bit) (hr : HasType Γ r L) :
    SubstitutionEquiv Γ (.case (.var i) (r.substVars (focus i false)) (r.substVars (focus i true))) r L :=
  BitQueryQuotation.expand_bit hi hr

/-- The query comparison in native `SubstitutionEquiv`. The proof uses
constructor case beta, focused case expansion, and pure let beta. -/
theorem native_choose_eq {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e f : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L)
    (equal : ∀ env, e.eval env = f.eval env) :
    SubstitutionEquiv Γ (choose e slots.terms l r) (choose f slots.terms l r) L :=
  BitQueryQuotation.choose_eq slots e f hl hr equal

/-- Quote the query natively while keeping its original continuations. -/
theorem native_quote_choose {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L) :
    SubstitutionEquiv Γ (choose e slots.terms l r) (choose (Expr.quote n e.eval) slots.terms l r) L :=
  BitQueryQuotation.quote_choose slots e hl hr

/-- Native replay traverses both actual reply binders at each node. -/
theorem native_region_replay {n : Nat} (t : Tree n) {Γ : VCtx (Ty Empty)} (slots : Slots Γ n) :
    SubstitutionEquiv Γ (t.region slots) (t.key.region slots) Exits :=
  BitQueryQuotation.region_replay t slots

/-- Typed exit substitution transports the native replay to the literal packed endpoints. -/
theorem native_packed_replay (t : Tree 1) :
    SubstitutionEquiv [Bit] t.guarded.packExits t.key.guarded.packExits [packedExitType Exits] :=
  BitQueryQuotation.packed_replay t

/-- Compare pure queries at any finite collection of distinct typed slots.
The arbitrary continuations keep the original context and outward labels. -/
theorem choose_eq {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e f : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L)
    (equal : ∀ env, e.eval env = f.eval env) :
    Extension.Eqv Seed Γ (choose e slots.terms l r) (choose f slots.terms l r) L :=
  .paper (.cfgEta (.native (native_choose_eq slots e f hl hr equal)))

/-- Quote the query in fixed slot order with its original continuations. -/
theorem quote_choose {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L) :
    Extension.Eqv Seed Γ (choose e slots.terms l r) (choose (Expr.quote n e.eval) slots.terms l r) L :=
  .paper (.cfgEta (.native (native_quote_choose slots e hl hr)))

/-- Replay the quoted tree at any typed lexical interface, under all reply binders. -/
theorem region_replay {n : Nat} (t : Tree n) {Γ : VCtx (Ty Empty)} (slots : Slots Γ n) :
    Extension.Eqv Seed Γ (t.region slots) (t.key.region slots) Exits :=
  .paper (.cfgEta (.native (native_region_replay t slots)))

/-- The entry guard is a native expansion of the unguarded region. -/
theorem native_packed_unguarded (t : Tree 1) :
    SubstitutionEquiv [Bit] t.guarded.packExits (t.region inputSlots).packExits
      [packedExitType Exits] :=
  BitQueryQuotation.packed_unguarded t

/-- The recorded pure guard only supplies its constructor, preserving the open arrow. -/
theorem packed_unguarded (t : Tree 1) :
    t.packed = Extension.Singleton.ofRegion Seed (t.typed inputSlots).packExits :=
  (Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
    (.paper (.cfgEta (.native (native_packed_unguarded t))))

theorem packed_replay (t : Tree 1) : t.packed = t.key.packed :=
  (Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr (.paper (.cfgEta (.native (native_packed_replay t))))

/-- Equal structural keys suffice for native equality of the original packed arrows. -/
theorem packed_eq_of_key {t u : Tree 1} (h : t.key = u.key) : t.packed = u.packed :=
  (packed_replay t).trans ((congrArg Tree.packed h).trans (packed_replay u).symm)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
