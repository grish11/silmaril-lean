module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Spine.Defs

/-! # A delayed case with any number of tags is the checked delayed case

`SpelledStackTags.delayedArms` builds a reply with two or more tags
inspected after a finite nonbranching prefix from the prefix and the arms
at its end. It is a tree of the spelled grammar, so the theorems of the
grammar apply: it is natively equal to its normal form, and ranked
validity between two such trees, at the original ordered exits, is
equality of their normal forms.

Its term, the prefix around the case on the reply slot, is natively equal
to the case on the reply slot around the computed specializations. Its
normal form is the normal form of the eager spelling that cases on the
reply at once, with the computed specializations as arms. With two tags it
is the constructor `SpelledStackTags.delayed`.

No law is added and no two requests are exchanged. The prefix does not
branch, and its requests have replies with one tag. There is no general
theorem that the computed specializations are the trees one would write by
hand for the eager spelling; the regression checks that on its instance.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
  {stack stack' : List (List α)} {holds : Holds β stack} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
  {holds' : Holds Δ' stack'}

/-- The term of a reply inspected after a prefix is natively equal to the
case on the reply slot around the two computed specializations: the one to
the first tag and the one to the remaining tags. This is the finite-prefix
equation at the computed shape of the prefix. -/
theorem delayedArms_equiv (atoms next : List α) (more : List (List α))
    (p : SpelledPrefix (Φ := Φ) stack (β.snoc (tagsTy (atoms :: next :: more)))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy (atoms :: next :: more)))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledArms stack' (next :: more) Δ' holds' L r) :
    Equiv false Γ₀ (β.snoc (tagsTy (atoms :: next :: more))) (p.plug (.case (.bv (p.weaken.toFun 0)) l r))
      (.case (.bv 0) (p.special (tupleTy atoms) l) (p.special (tagsTy (next :: more)) r))
      (packedExitType L) :=
  deferred_equiv (p.shape 0 rfl l r)
    ((p.spec atoms left _ (Holds.rename_comp holds _ _)).term_eq ▸
      (p.spec atoms left _ (Holds.rename_comp holds _ _)).tree.typing.toHasType)
    ((p.specArms more next right).term_eq ▸ (p.specArms more next right).tree.typing.toHasType)

/-- The normal form of a reply inspected after a prefix is the normal form
of the eager spelling: the case on the reply at once, around the computed
specializations. -/
theorem delayedArms_opened (atoms next : List α) (more : List (List α))
    (p : SpelledPrefix (Φ := Φ) stack (β.snoc (tagsTy (atoms :: next :: more)))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy (atoms :: next :: more)))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledArms stack' (next :: more) Δ' holds' L r)
    {k : Nat} {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β Θ) :
    (SpelledStackTags.delayedArms atoms next more p left right).opened ρ =
      (SpelledStackTags.split atoms next more
        (p.spec atoms left (holds.rename (pastPair β (tagsTy (atoms :: next :: more)) (tupleTy atoms)))
          (Holds.rename_comp holds _ _)).tree
        (p.specArms more next right).tree).opened ρ :=
  rfl

/-- With two tags the constructor is `SpelledStackTags.delayed`, with the
arm of the second tag as the one arm of the spine. -/
theorem delayedArms_two (atoms next : List α)
    (p : SpelledPrefix (Φ := Φ) stack (β.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy [atoms, next]))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledStack (next :: stack') (Δ'.snoc (tupleTy next))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy next)))) L r) :
    SpelledStackTags.delayedArms atoms next [] p left (.only next right) =
      SpelledStackTags.delayed atoms next p left right :=
  rfl

/-- The term of the specialization of a prefix to the remaining tags is
the term of the prefix placed under the slot of the remaining tags, around
the term of the arms moved beneath it. -/
theorem specArms_term (more : List (List α)) (atoms : List α)
    (p : SpelledPrefix (Φ := Φ) stack β holds stack' Δ' holds') {e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (arms : SpelledArms stack' (atoms :: more) Δ' holds' L e) :
    (p.specArms more atoms arms).term =
      (p.under (tagsTy (atoms :: more))).tree.plug (e.rename (p.past (tagsTy (atoms :: more))).toFun) :=
  (p.specArms more atoms arms).term_eq.trans (spelledPrefix_special_eq_plug (tagsTy (atoms :: more)) p e)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
