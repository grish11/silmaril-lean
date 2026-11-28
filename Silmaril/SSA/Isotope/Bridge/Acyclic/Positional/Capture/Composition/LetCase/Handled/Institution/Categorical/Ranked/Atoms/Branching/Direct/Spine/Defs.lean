module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Renaming.Thms

/-! # A delayed case with any number of tags, from its prefix and its arms

A reply with two or more tags is inspected after a finite nonbranching
prefix. The original input is one prefix and the arms at its end: the arm
of the first tag, and the arms of the remaining tags as a spine of cases
on the slot of the remaining tags, each arm with the payload of its tag
newest and on top of the stack.

The specialization of the prefix to the remaining tags is computed by
recursion on the spine. With one tag left it is the specialization to that
tag. With more, it is again a delayed case: the prefix is placed under the
slot of the remaining tags by the renaming action on prefixes, the arms
are moved beneath it by the renaming action on trees, and the recursion
continues with the renamed prefix and the moved arms. Its term is the
specialization term of the prefix, by the equation between that term and
the term of the prefix placed under the slot.

The result is the checked `deferred` node on the computed shape and
specializations, at every level of the spine.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-- The arms of the tags of a pending reply, at the newest slot: the spine
of cases on the remaining tags, eager and without requests between the
cases. With one tag the arm has the tuple of the tag on top of the stack.
With more, the first arm has the payload of the first tag on top of the
stack, and the other arms are the arms of the remaining tags. -/
inductive SpelledArms : (stack : List (List α)) → List (List α) → {m : Nat} → (Δ : BoundCtx (Ty α) m) →
    Holds Δ stack → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ (m + 1) → Type where
  | only {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms : List α) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (arm : SpelledStack (atoms :: stack) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)))) L k) :
      SpelledArms stack [atoms] Δ holds L k
  | split {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms next : List α) (more : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (left : SpelledStack (atoms :: stack)
        ((Δ.snoc (tagsTy (atoms :: next :: more))).snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))) L l)
      (right : SpelledArms stack (next :: more) (Δ.snoc (tagsTy (atoms :: next :: more)))
        (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: next :: more)))) L r) :
      SpelledArms stack (atoms :: next :: more) Δ holds L (.case (.bv 0) l r)

/-- The arms as a bound reply that is cased on at once: the eager
spelling. -/
def SpelledArms.eager : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledArms stack tags Δ holds L t → SpelledStackTags stack tags Δ holds L t
  | _, _, _, _, _, _, .only atoms arm => .bind atoms arm
  | _, _, _, _, _, _, .split atoms next more left right => .split atoms next more left right.eager

/-- The renaming action on arms, along a renaming of the context beneath
the pending slot, onto given slots of the stack that are the renamed
slots. -/
def SpelledArms.renamed : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledArms stack tags Δ holds L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) → holds.rename ρ = holds' →
    Renamed (SpelledArms stack tags Θ holds' L) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
  | _, _, _, _, holds, _, .only atoms arm, _, Θ, ρ, holds', h =>
    let r := arm.renamed (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl))))
    ⟨_, .only atoms r.tree, r.term_eq⟩
  | _, _, _, _, holds, _, .split atoms next more left right, _, Θ, ρ, holds', h =>
    let rl := left.renamed ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
    let rr := right.renamed (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl)))
    ⟨_, .split atoms next more rl.tree rr.tree, congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 0)) rl.term_eq rr.term_eq⟩

/-- The specialization of a prefix to the remaining tags, as a tree, from
the prefix and the arms of those tags at its end. The recursion is on the
spine of tags. With one tag it is the specialization to that tag. With
more it is a delayed case on the prefix placed under the slot of the
remaining tags: the arms are moved beneath that prefix, the first arm is
specialized, and the other arms are specialized by the recursion. Its term
is the specialization term of the prefix. -/
def SpelledPrefix.specArms : (more : List (List α)) → (atoms : List α) → {stack : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') → {e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)} →
    SpelledArms stack' (atoms :: more) Δ' holds' L e →
    Renamed (SpelledStackTags stack (atoms :: more) Δ holds L) (p.special (tagsTy (atoms :: more)) e)
  | [], atoms, _, _, _, _, _, _, _, _, p, _, .only _ arm =>
    let q := p.spec atoms arm _ rfl
    ⟨_, .bind atoms q.tree, q.term_eq⟩
  | next :: more, atoms, _, _, Δ, holds, _, _, _, holds', p, _, .split (l := l) (r := r) _ _ _ left right =>
    let u := p.under (tagsTy (atoms :: next :: more))
    let past := p.past (tagsTy (atoms :: next :: more))
    let left' := left.renamed (past.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (u.slots.rename (BoundCtx.Renaming.succ u.ctx (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds' (BoundCtx.Renaming.succ u.ctx (tupleTy atoms))
        u.slots_eq (renaming_ext (fun _ => rfl))))
    let right' := right.renamed past u.slots
      ((Holds.rename_comp holds' _ past).trans
        ((congrArg (fun q => holds'.rename q) (renaming_ext (fun _ => rfl))).trans u.slots_eq))
    let sl := u.tree.spec atoms left'.tree
      (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms))) (Holds.rename_comp holds _ _)
    let sr := SpelledPrefix.specArms more next u.tree right'.tree
    ⟨_, .deferred atoms next more (u.tree.shape 0 rfl left'.term right'.term) sl.tree sr.tree
        sl.term_eq sr.term_eq,
      (congrArg₂ (fun a b => u.tree.plug (.case (.bv (u.tree.weaken.toFun 0)) a b))
        left'.term_eq right'.term_eq).trans
        (spelledPrefix_special_eq_plug (tagsTy (atoms :: next :: more)) p (.case (.bv 0) l r)).symm⟩

/-- A reply with two or more tags inspected after a finite nonbranching
prefix, from the prefix and the arms at its end alone. The prefix starts
under the reply slot. The arm of the first tag has its payload newest and
on top of the stack, and the arms of the remaining tags are their spine at
the end of the prefix. The term is the prefix around the case on the reply
slot. The shape of the prefix and the specializations to all tags are
computed. -/
def SpelledStackTags.delayedArms {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
    {holds : Holds Δ stack} (atoms next : List α) (more : List (List α)) {stack' : List (List α)}
    {m' : Nat} {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
    (p : SpelledPrefix (Φ := Φ) stack (Δ.snoc (tagsTy (atoms :: next :: more)))
      (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: next :: more)))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledArms stack' (next :: more) Δ' holds' L r) :
    SpelledStackTags stack (atoms :: next :: more) Δ holds L
      (p.plug (.case (.bv (p.weaken.toFun 0)) l r)) :=
  .deferred atoms next more (p.shape 0 rfl l r)
    (p.spec atoms left (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))
      (Holds.rename_comp holds _ _)).tree
    (p.specArms more next right).tree
    (p.spec atoms left (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))
      (Holds.rename_comp holds _ _)).term_eq
    (p.specArms more next right).term_eq

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
