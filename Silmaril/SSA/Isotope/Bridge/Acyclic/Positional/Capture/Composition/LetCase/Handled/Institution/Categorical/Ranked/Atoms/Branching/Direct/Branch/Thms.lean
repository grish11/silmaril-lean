module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Branch.Defs

/-! # A stored reply inspected after a branching prefix is the checked delayed case

`SpelledStackTags.delayedTree` builds a reply with two tags inspected
after a prefix that may branch, from the tree alone. It is a tree of the
spelled grammar, so the theorems of the grammar apply: it is natively
equal to its normal form, and ranked validity between two such trees, at
the original ordered exits, is equality of their normal forms.

Its term is natively equal to the case on the reply slot around the two
computed specializations. That is the finite-prefix equation at the
computed shape; at a branch it uses the equation that exchanges a case on
a slot with the cases on a stored slot in its arms, which is derived from
native laws. Its normal form is the normal form of the eager spelling that
cases on the reply at once, with the computed specializations as arms.

The scope is a tree-shaped prefix with branch-specific continuations.
Every path ends in its own inspection of the stored reply with its own
arms. The arms of a branch are not joined, and no continuation is shared
between them: a term in which two branches meet again before the stored
reply is inspected is not of this form, and writing its continuation once
in each arm is a different term. A branch cases on the reply of a request
at that request. No request and no scrutinee of the prefix reads the
stored reply. No law is added and no two requests are exchanged: on each
path the specializations have the requests of that path, in their order.

The stored reply has two tags here. There is no general theorem that the
computed specializations are the trees one would write by hand for the
eager spelling; the regression checks that on its instance.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
  {stack : List (List α)} {holds : Holds β stack}

/-- The term of a reply inspected after a branching prefix is natively
equal to the case on the reply slot around the two computed
specializations. -/
theorem delayedTree_equiv (atoms next : List α) {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledDelay atoms next stack (β.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy [atoms, next]))) 0 L t) :
    Equiv false Γ₀ (β.snoc (tagsTy [atoms, next])) t
      (.case (.bv 0) (d.special true) (d.special false)) (packedExitType L) :=
  deferred_equiv d.shape
    ((d.spec true _ (Holds.rename_comp holds _ _)).term_eq ▸
      (d.spec true _ (Holds.rename_comp holds _ _)).tree.typing.toHasType)
    ((d.spec false _ rfl).term_eq ▸ (d.spec false _ rfl).tree.typing.toHasType)

/-- The normal form of a reply inspected after a branching prefix is the
normal form of the eager spelling: the case on the reply at once, around
the two computed specializations. -/
theorem delayedTree_opened (atoms next : List α) {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledDelay atoms next stack (β.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ β (tagsTy [atoms, next]))) 0 L t)
    {k : Nat} {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β Θ) :
    (SpelledStackTags.delayedTree atoms next d).opened ρ =
      (SpelledStackTags.split atoms next []
        (d.spec true (holds.rename (pastPair β (tagsTy [atoms, next]) (tupleTy atoms)))
          (Holds.rename_comp holds _ _)).tree
        (.bind next (d.spec false _ rfl).tree)).opened ρ :=
  rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
