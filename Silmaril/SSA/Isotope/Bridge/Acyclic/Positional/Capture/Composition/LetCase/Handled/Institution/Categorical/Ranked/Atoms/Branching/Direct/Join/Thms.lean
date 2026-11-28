module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Join.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomJoin

/-! # A shared join is inlined into the tree-shaped prefix

A join is a let whose bound term is a case: the two arms of the case feed
one continuation, written once. It is natively equal to the case with the
continuation in each arm:

`let₁ (case y P₁[v₁] P₂[v₂]) K = case y (P₁[K[v₁]]) (P₂[K[v₂]])`

where each arm is a finite nonbranching prefix around the slot it
supplies, and `K[v]` is the continuation with its newest slot renamed to
that slot and its other slots weakened past the slots of the prefix.

The laws are the native sequencing laws and pure-let beta. The case is
pulled out of the bound term of the let, which copies the continuation
into the two arms. In each arm the requests and pattern lets of the prefix
are moved out of the bound term of the let, one at a time and in order.
The remaining let binds a slot and is a renaming. No exchange law is used:
no request moves past another request or past a case, and on each path the
requests of the arm come before the requests of the continuation, as in
the join.

So the expansion of a join node is natively equal to it, in the same
context and at the same exits. The expansion is a tree of the tree-shaped
family, so with the stored reply above it, it is the checked delayed case.
Ranked validity is transferred along the native equation: the graph read
back from a typed term that is natively equal to a spelled tree, at the
original ordered exits, is valid together with the graph of a spelled tree
exactly when the two trees have the same normal form.

The scope is one binary branch feeding one continuation. Each arm is a
nonbranching prefix whose requests have replies with one tag; it supplies
the tuple on top of its stack and leaves the older tuples in place. The
continuation is a tree and may branch after the join. The stored reply has
two tags. Arms that branch before the join, a joined value that is not a
slot, and joins of more than two arms are not covered.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-! ## A prefix in the bound term of a let -/

section Prefix

variable {stack stack' : List (List α)} {holds : Holds β stack} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
  {holds' : Holds Δ' stack'}

/-- A prefix around natively equal terms gives natively equal terms. -/
theorem spelledPrefix_plug_congr (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds')
    {e e' : LetCase.LocallyNameless.Tm Empty Φ m'} {C : Ty α} (h : Equiv false Γ₀ Δ' e e' C) :
    Equiv false Γ₀ β (p.plug e) (p.plug e') C :=
  p.plug_congr_proof h

/-- A let whose bound term is a prefix around a term is the prefix around
the let, with the body weakened past the slots of the prefix. The requests
and pattern lets of the prefix are moved out of the bound term by the
native sequencing laws, in order. -/
theorem spelledPrefix_let_plug (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds')
    {v : LetCase.LocallyNameless.Tm Empty Φ m'} {K : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} {J C : Ty α} (hv : HasType Φ Γ₀ Δ' v J)
    (hK : HasType Φ Γ₀ (β.snoc J) K C) :
    Equiv false Γ₀ β (.let₁ (p.plug v) K) (p.plug (.let₁ v (K.rename (LetCase.LocallyNameless.Tm.up p.weaken.toFun)))) C :=
  p.let_plug_proof hv hK

/-- A let whose bound term is a prefix around a slot is the prefix around
the body, with the newest slot of the body renamed to that slot. -/
theorem spelledPrefix_let_plug_slot (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds')
    {J C : Ty α} (top : Slot Δ' J) {K : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} (hK : HasType Φ Γ₀ (β.snoc J) K C) :
    Equiv false Γ₀ β (.let₁ (p.plug (.bv top.1)) K)
      (p.plug (K.rename (Fin.cases top.1 p.weaken.toFun))) C :=
  p.let_plug_slot_proof top hK

end Prefix

/-! ## The join is inlined -/

/-- The join-inlining equation. A let whose bound term is a case on a
slot of sum type, with a prefix around a supplied slot in each arm, is
natively equal to the case with, in each arm, the prefix around the body
renamed into the arm. -/
theorem join_inline {stackA stackB : List (List α)} {A B J C : Ty α} (y : Slot β (.coprod A B))
    {holdsA : Holds (β.snoc A) stackA} {stackA' : List (List α)} {mA : Nat} {ΔA : BoundCtx (Ty α) mA}
    {holdsA' : Holds ΔA stackA'}
    (left : SpelledPrefix (Φ := Φ) stackA (β.snoc A) holdsA stackA' ΔA holdsA') (topA : Slot ΔA J)
    {holdsB : Holds (β.snoc B) stackB} {stackB' : List (List α)} {mB : Nat} {ΔB : BoundCtx (Ty α) mB}
    {holdsB' : Holds ΔB stackB'}
    (right : SpelledPrefix (Φ := Φ) stackB (β.snoc B) holdsB stackB' ΔB holdsB') (topB : Slot ΔB J)
    {K : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} (hK : HasType Φ Γ₀ (β.snoc J) K C) :
    Equiv false Γ₀ β (.let₁ (.case (.bv y.1) (left.plug (.bv topA.1)) (right.plug (.bv topB.1))) K)
      (.case (.bv y.1) (left.plug (K.rename (joinRenaming left.weaken topA).toFun))
        (right.plug (K.rename (joinRenaming right.weaken topB).toFun))) C :=
  join_inline_proof y left topA right topB hK

/-- A join node is natively equal to the term of its expansion, under the
reply slot. -/
theorem spelledJoinTags_equiv_inlined {atoms next : List α} {stack : List (List α)} {tags : List (List α)}
    {holds : Holds β stack} {s : Fin n} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (j : SpelledJoinTags atoms next stack tags β holds s L t) :
    Equiv false Γ₀ (β.snoc (tagsTy tags)) t j.inlined (packedExitType L) :=
  j.equiv_expand_proof

/-- A join node is natively equal to its expansion into the tree-shaped
family. -/
theorem spelledJoinTags_equiv_expand {atoms next : List α} {stack : List (List α)} {tags : List (List α)}
    {holds : Holds β stack} {s : Fin n} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (j : SpelledJoinTags atoms next stack tags β holds s L t) :
    Equiv false Γ₀ (β.snoc (tagsTy tags)) t j.expand.term (packedExitType L) :=
  cast (congrArg (fun x => Equiv false Γ₀ (β.snoc (tagsTy tags)) t x (packedExitType L)) j.expand.term_eq.symm)
    j.equiv_expand_proof

/-! ## Ranked validity along a native equation -/

/-- The graph read back from a typed term that is natively equal to a
spelled tree and the graph read back from a spelled tree are valid
together, at the original ordered exits, exactly when the two trees have
the same normal form. -/
theorem rankedValid_expanded_iff {t t' u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (typing : Derivation Φ Γ₀ β t (packedExitType L)) (d : Spelled β L t')
    (same : Equiv false Γ₀ β t t' (packedExitType L)) (q : Spelled β L u) :
    RankedValid false (sentenceOf (entryOf (CheckedTable.ofLetCase d.exits_ne_nil typing))
        (entryOf q.graph)) ↔
      (d.normal (.id β)).1 = (q.normal (.id β)).1 :=
  rankedValid_expanded_iff_proof separable typing d same q

/-- At the ordered trace model with atoms, the two graphs have the same
ordered-exit arrow exactly when the two trees have the same normal
form. -/
theorem denoteRanked_expanded_iff {t t' u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (typing : Derivation Φ Γ₀ β t (packedExitType L)) (d : Spelled β L t')
    (same : Equiv false Γ₀ β t t' (packedExitType L)) (q : Spelled β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ)
        (entryOf (CheckedTable.ofLetCase d.exits_ne_nil typing)) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔
      (d.normal (.id β)).1 = (q.normal (.id β)).1 :=
  denoteRanked_expanded_iff_proof separable typing d same q

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
