module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Renaming.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomSpelledRenaming

/-! # Renamed spelled trees and computed specializations

The renaming action on spelled trees keeps the term and the normal form.
The term of the renamed tree is the renamed term; that equation is a field
of the result. The normal form of the renamed tree along a renaming is the
normal form of the tree along the composite. So ranked validity between
two renamed trees is equality of the normal forms along the renaming.

A reply with two tags inspected after a finite nonbranching prefix is
built from the prefix and the two arms at its end. The specializations of
the tree to the tags are computed with the renaming action, and the node
is the checked `deferred` node on them. Its term is natively equal to the
case on the reply slot around the two specializations, by the finite-prefix
equation, and its normal form is the normal form of the eager spelling
that cases on the reply at once.

A prefix is renamed as well. The renamed prefix comes with its end context
and its end renaming. The end renaming commutes with the weakenings of the
two prefixes, and the term of the renamed prefix around a term renamed
along the end renaming is the renamed term of the prefix. The
specialization term of a prefix at a payload slot is the term of the
prefix placed under that slot, around the term at the end with the payload
moved beneath the prefix. The `Spine` headers beside these use that
equation to build a delayed case with any number of tags.

No law is added. A prefix does not branch.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open LetCase.LocallyNameless (Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-! ## The normal form of a renamed tree -/

/-- The normal form of a renamed spelled tree along a renaming is the
normal form of the tree along the composite. -/
theorem spelled_renamed_normal {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : Spelled β L t) {m k : Nat}
    {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π) :=
  d.renamed_normal_proof ρ π

/-- The normal form of a renamed spelled tree is the normal form of the
tree along the renaming. -/
theorem spelled_renamed_normal_id {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : Spelled β L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    (d.renamed ρ).tree.normal (.id γ) = d.normal ρ :=
  spelled_renamed_normal d ρ (.id γ)

/-- The same for the head of a request. -/
theorem spelledHead_renamed_normal {tags : List (List α)} {e t : LetCase.LocallyNameless.Tm Empty Φ n} (d : SpelledHead tags e β L t)
    {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ)
    (e' : LetCase.LocallyNameless.Tm Empty Φ m) (he : e' = e.rename ρ.toFun) (π : BoundCtx.Renaming γ δ) :
    (d.renamed ρ e' he).tree.normal π = d.normal (ρ.comp π) :=
  d.renamed_normal_proof ρ e' he π

/-- The same for a pending reply. -/
theorem spelledTags_renamed_normal {tags : List (List α)} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} (d : SpelledTags tags β L t)
    {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ)
    (π : BoundCtx.Renaming γ δ) : (d.renamed ρ).tree.normal π = d.normal (ρ.comp π) :=
  d.renamed_normal_proof ρ π

/-- The same for a pending tuple. -/
theorem spelledTuple_renamed_normal {atoms : List α} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} (d : SpelledTuple atoms β L t)
    {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ)
    (π : BoundCtx.Renaming γ δ) : (d.renamed ρ).tree.normal π = d.normal (ρ.comp π) :=
  d.renamed_normal_proof ρ π

/-- The same for a chain over a stack of packed tuples, renamed onto given
slots of the stack. -/
theorem spelledStack_renamed_opened {stack : List (List α)} {holds : Holds β stack} {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : SpelledStack stack β holds L t) {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming β γ) (holds' : Holds γ stack) (h : holds.rename ρ = holds')
    (π : BoundCtx.Renaming γ δ) : (d.renamed ρ holds' h).tree.opened π = d.opened (ρ.comp π) :=
  d.renamed_opened_proof ρ holds' h π

/-- The same for the bound reply of a request of a chain. -/
theorem spelledStackTags_renamed_opened {stack : List (List α)} {tags : List (List α)} {holds : Holds β stack}
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} (d : SpelledStackTags stack tags β holds L t) {m k : Nat}
    {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (holds' : Holds γ stack)
    (h : holds.rename ρ = holds') (π : BoundCtx.Renaming γ δ) :
    (d.renamed ρ holds' h).tree.opened π = d.opened (ρ.comp π) :=
  d.renamed_opened_proof ρ holds' h π

/-- The same for the arms of a case delayed across one request. -/
theorem spelledLaterTags_renamed_opened {stack : List (List α)} {tags : List (List α)} {g : Φ}
    {holds : Holds β stack} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)} (d : SpelledLaterTags stack tags g β holds L t)
    {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ)
    (holds' : Holds γ stack) (h : holds.rename ρ = holds') (π : BoundCtx.Renaming γ δ)
    (arg : Assembly (δ.snoc (tagsTy tags)) (instrSrc g)) :
    (d.renamed ρ holds' h).tree.opened π arg = d.opened (ρ.comp π) arg :=
  d.renamed_opened_proof ρ holds' h π arg

/-- A renamed spelled tree is natively equal to the normal form of the
tree along the renaming. -/
theorem spelled_renamed_equiv_normal {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : Spelled β L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (d.renamed ρ).term (d.normal ρ).1 (packedExitType L) :=
  spelled_renamed_normal_id d ρ ▸ spelled_equiv_normal (d.renamed ρ).tree

/-- On the graphs read back from two renamed spelled trees, validity in the
ranked room is equality of the normal forms of the trees along the
renaming. -/
theorem rankedValid_spelled_renamed_iff {t u : LetCase.LocallyNameless.Tm Empty Φ n} {m : Nat} {γ : BoundCtx (Ty α) m}
    (separable : Separable γ) (p : Spelled β L t) (q : Spelled β L u) (ρ : BoundCtx.Renaming β γ) :
    RankedValid false (sentenceOf (entryOf (p.renamed ρ).tree.graph) (entryOf (q.renamed ρ).tree.graph)) ↔
      (p.normal ρ).1 = (q.normal ρ).1 :=
  spelled_renamed_normal_id p ρ ▸ spelled_renamed_normal_id q ρ ▸
    rankedValid_spelledTree_iff separable (p.renamed ρ).tree (q.renamed ρ).tree

/-! ## A case after a prefix, from the prefix and the arms -/

/-- The term of a reply with two tags inspected after a prefix is natively
equal to the case on the reply slot around the two computed
specializations. This is the finite-prefix equation at the computed shape
of the prefix. -/
theorem delayed_equiv {stack : List (List α)} {holds : Holds β stack} (atoms next : List α)
    {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
    (p : SpelledPrefix (Φ := Φ) stack (β.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy [atoms, next]))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledStack (next :: stack') (Δ'.snoc (tupleTy next))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy next)))) L r) :
    Equiv false Γ₀ (β.snoc (tagsTy [atoms, next])) (p.plug (.case (.bv (p.weaken.toFun 0)) l r))
      (.case (.bv 0) (p.special (tupleTy atoms) l) (p.special (tupleTy next) r)) (packedExitType L) :=
  deferred_equiv (p.shape 0 rfl l r)
    ((p.spec atoms left _ (Holds.rename_comp holds _ _)).term_eq ▸
      (p.spec atoms left _ (Holds.rename_comp holds _ _)).tree.typing.toHasType)
    ((p.spec next right _ rfl).term_eq ▸ (p.spec next right _ rfl).tree.typing.toHasType)

/-- The normal form of a reply inspected after a prefix is the normal form
of the eager spelling: the case on the reply at once, around the two
computed specializations. -/
theorem delayed_opened {stack : List (List α)} {holds : Holds β stack} (atoms next : List α)
    {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
    (p : SpelledPrefix (Φ := Φ) stack (β.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy [atoms, next]))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledStack (next :: stack') (Δ'.snoc (tupleTy next))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy next)))) L r)
    {k : Nat} {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β Θ) :
    (SpelledStackTags.delayed atoms next p left right).opened ρ =
      (SpelledStackTags.split atoms next []
        (p.spec atoms left (holds.rename (pastPair β (tagsTy [atoms, next]) (tupleTy atoms)))
          (Holds.rename_comp holds _ _)).tree
        (.bind next (p.spec next right _ rfl).tree)).opened ρ :=
  rfl

/-! ## Renaming a prefix -/

section Prefix

variable {stack stack' : List (List α)} {holds : Holds β stack} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
  {holds' : Holds Δ' stack'}

/-- The end renaming of a renamed prefix commutes with the weakenings: the
weakening of the prefix followed by the end renaming is the renaming
followed by the weakening of the renamed prefix. -/
theorem spelledPrefix_renamed_weaken (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds') {k : Nat}
    {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β Θ) (H : Holds Θ stack) (h : holds.rename ρ = H) :
    p.weaken.comp (p.renamed ρ H h).ren = ρ.comp (p.renamed ρ H h).tree.weaken :=
  p.renamed_weaken_proof ρ H h

/-- The term of a renamed prefix around a term renamed along the end
renaming is the renamed term of the prefix. -/
theorem spelledPrefix_renamed_plug (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds') {k : Nat}
    {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β Θ) (H : Holds Θ stack) (h : holds.rename ρ = H)
    (e : LetCase.LocallyNameless.Tm Empty Φ m') :
    (p.plug e).rename ρ.toFun = (p.renamed ρ H h).tree.plug (e.rename (p.renamed ρ H h).ren.toFun) :=
  p.renamed_plug_proof ρ H h e

/-- The specialization term of a prefix at a payload slot `Z`, renamed
along a renaming `τ` of the context with `Z` newest, is the term of the
prefix renamed along `τ` past `Z`, around the term at the end: its slots
follow the end renaming and `Z` goes to the weakened image of `τ 0`. -/
theorem spelledPrefix_special_renamed (Z : Ty α) (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds')
    {k : Nat} {Θ : BoundCtx (Ty α) k} (τ : BoundCtx.Renaming (β.snoc Z) Θ) (ρ : BoundCtx.Renaming β Θ)
    (hρ : (BoundCtx.Renaming.succ β Z).comp τ = ρ) (H : Holds Θ stack) (h : holds.rename ρ = H)
    (e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) :
    (p.special Z e).rename τ.toFun = (p.renamed ρ H h).tree.plug
      (e.rename (Fin.cases ((p.renamed ρ H h).tree.weaken.toFun (τ.toFun 0)) (p.renamed ρ H h).ren.toFun)) :=
  p.special_renamed_proof Z τ ρ hρ H h e

/-- The specialization term of a prefix at a payload slot is the term of
the prefix placed under the payload, around the term at the end with the
payload moved beneath the prefix. -/
theorem spelledPrefix_special_eq_plug (Z : Ty α) (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds')
    (e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) : p.special Z e = (p.under Z).tree.plug (e.rename (p.past Z).toFun) :=
  p.special_eq_plug_proof Z e

end Prefix

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
