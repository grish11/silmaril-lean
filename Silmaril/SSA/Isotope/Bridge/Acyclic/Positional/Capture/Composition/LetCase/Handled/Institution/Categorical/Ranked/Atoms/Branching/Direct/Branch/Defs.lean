module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Renaming.Thms

/-! # A stored reply inspected after a prefix that branches

A reply with two tags is stored as one slot while a prefix runs, and the
prefix may branch: it asks a request and cases on its reply at once, and
each arm continues on its own. The prefix is a tree. Every path of the
tree ends in its own inspection of the stored reply, with its own two
arms. The arms of a branch are not joined and they share no continuation.

`SpelledDelay` is that tree, over a stack of packed tuples: requests,
pattern lets on the top tuple, selections, branches on the reply of a
request of the prefix, and at each leaf the case on the stored slot. A
request is assembled from atom slots, so no request and no scrutinee of
the prefix reads the stored reply; a branch cases on the reply bound just
before it.

From the tree alone, the shape of the prefix and the two specializations
to the tags of the stored reply are computed. A specialization places the
payload of the tag beneath the slots of the prefix: at each slot the tree
built so far is renamed past it by the renaming action, and the payload is
selected back to the top of the stack. At a branch both arms are
specialized and the branch is kept, so the specialization has the same
requests on each path, in the same order. The result is the checked
`deferred` node on the computed shape and specializations.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-- The atoms of the tag of a side of a stored reply with two tags: the
first tag for `true` and the second for `false`. -/
abbrev sideAtoms (atoms next : List α) : Bool → List α
  | true => atoms
  | false => next

omit [TaggedSignature α Φ] in
/-- Moving the newest slot beneath two slots is exchanging it with the
slot under it and then, under that slot, with the next one. -/
theorem before_eq_swap_swap {k : Nat} (Δ : BoundCtx (Ty α) k) (R A Z : Ty α) (x : LetCase.LocallyNameless.Tm Empty Φ (k + 3)) :
    x.rename beforePair =
      (x.rename (swapRenaming (Δ.snoc R) A Z).toFun).rename (LetCase.LocallyNameless.Tm.up (swapRenaming Δ R Z).toFun) :=
  (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun i => Fin.cases rfl
      (fun i => Fin.cases rfl (fun _ => rfl) i) i) i) x).trans
    (LetCase.LocallyNameless.Tm.rename_comp (swapRenaming (Δ.snoc R) A Z).toFun (LetCase.LocallyNameless.Tm.up (swapRenaming Δ R Z).toFun) x).symm

mutual

/-- A chain over a stack that keeps a stored reply with tags `atoms` and
`next` as one slot `s` and inspects it at every leaf. It is a tree: a
request of the chain may be cased on at once, and each arm continues on
its own, to its own inspections of `s`. -/
inductive SpelledDelay (atoms next : List α) : (stack : List (List α)) → {m : Nat} →
    (Δ : BoundCtx (Ty α) m) → Holds Δ stack → Fin m → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ m → Type where
  | inspect {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (s : Slot Δ (tagsTy [atoms, next])) {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (left : SpelledStack (atoms :: stack) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)))) L l)
      (right : SpelledStack (next :: stack) (Δ.snoc (tupleTy next))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy next)))) L r) :
      SpelledDelay atoms next stack Δ holds s.1 L (.case (.bv s.1) l r)
  | unit {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy ([] : List α))}
      {older : Holds Δ stack} {s : Fin m} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m}
      (tail : SpelledDelay atoms next stack Δ older s L t) :
      SpelledDelay atoms next ([] :: stack) Δ (.cons top older) s L t
  | atom {c : α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy [c])}
      {older : Holds Δ stack} {s : Fin m} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m}
      (tail : SpelledDelay atoms next stack Δ older s L t) :
      SpelledDelay atoms next ([c] :: stack) Δ (.cons top older) s L t
  | step {a b : α} {rest : List α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {top : Slot Δ (tupleTy (a :: b :: rest))} {older : Holds Δ stack} {s : Fin m} {L : List (Ty α)}
      {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (tail : SpelledDelay atoms next ((b :: rest) :: stack) ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest)))
        (.cons ⟨0, rfl⟩ (older.rename (pastPair Δ (.base a) (tupleTy (b :: rest))))) s.succ.succ L k) :
      SpelledDelay atoms next ((a :: b :: rest) :: stack) Δ (.cons top older) s L (.let₂ (.bv top.1) k)
  | ask {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {s : Fin m}
      {L : List (Ty α)} (g : Φ) (argument : Assembly Δ (instrSrc g)) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (reply : SpelledDelayTags atoms next stack (replyTags g) Δ holds s L k) :
      SpelledDelay atoms next stack Δ holds s L (.let₁ (.op g (argTerm argument)) k)
  | pick {stack : List (List α)} {picked : List α} {rest : List (List α)} {m : Nat}
      {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {s : Fin m} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m}
      (sel : Select stack picked rest)
      (tail : SpelledDelay atoms next (picked :: rest) Δ (holds.select sel) s L t) :
      SpelledDelay atoms next stack Δ holds s L t

/-- The bound reply of a request of such a chain, pending at the newest
slot, with the stored slot `s` beneath it. A reply with one tag is pushed
on the stack. A reply with more tags is cased on at once: this is where
the tree branches. Each arm continues on its own. -/
inductive SpelledDelayTags (atoms next : List α) : (stack : List (List α)) → List (List α) → {m : Nat} →
    (Δ : BoundCtx (Ty α) m) → Holds Δ stack → Fin m → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ (m + 1) → Type where
  | bind {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {s : Fin m}
      {L : List (Ty α)} (reply : List α) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (tail : SpelledDelay atoms next (reply :: stack) (Δ.snoc (tupleTy reply))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy reply)))) s.succ L k) :
      SpelledDelayTags atoms next stack [reply] Δ holds s L k
  | split {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {s : Fin m}
      {L : List (Ty α)} (first second : List α) (more : List (List α)) {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (left : SpelledDelay atoms next (first :: stack)
        ((Δ.snoc (tagsTy (first :: second :: more))).snoc (tupleTy first))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (first :: second :: more)) (tupleTy first))))
        s.succ.succ L l)
      (right : SpelledDelayTags atoms next stack (second :: more) (Δ.snoc (tagsTy (first :: second :: more)))
        (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (first :: second :: more)))) s.succ L r) :
      SpelledDelayTags atoms next stack (first :: second :: more) Δ holds s L (.case (.bv 0) l r)

end

mutual

/-- The term of the specialization of the tree to a side of the stored
reply: the tree under the payload of that tag, with the arm of that tag at
each leaf. The payload is beneath the slots of the tree. -/
def SpelledDelay.special {atoms next : List α} (side : Bool) : {stack : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    SpelledDelay atoms next stack Δ holds s L t → LetCase.LocallyNameless.Tm Empty Φ (m + 1)
  | _, _, _, _, _, _, .inspect (l := l) (r := r) _ _ _ => match side with
    | true => l
    | false => r
  | _, _, _, _, _, _, .unit tail => tail.special side
  | _, _, _, _, _, _, .atom tail => tail.special side
  | _, _, _, .cons top _, _, _, .step tail => .let₂ (.bv top.1.succ) ((tail.special side).rename beforePair)
  | _, _, Δ, _, _, _, .ask g argument reply =>
    .let₁ (.op g (argTerm (argument.rename (BoundCtx.Renaming.succ Δ (tupleTy (sideAtoms atoms next side))))))
      ((reply.special side).rename
        (swapRenaming Δ (tagsTy (replyTags g)) (tupleTy (sideAtoms atoms next side))).toFun)
  | _, _, _, _, _, _, .pick _ tail => tail.special side

/-- The term of the specialization of a bound reply, with the payload
newest. At a branch the case on the reply is kept and each arm is the
specialization of that arm. -/
def SpelledDelayTags.special {atoms next : List α} (side : Bool) : {stack : List (List α)} →
    {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → SpelledDelayTags atoms next stack tags Δ holds s L t → LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)
  | _, _, _, _, _, _, _, .bind _ tail => tail.special side
  | _, _, m, Δ, _, _, _, .split first second more left right =>
    .case (.bv (0 : Fin (m + 1)).succ)
      ((left.special side).rename (swapRenaming (Δ.snoc (tagsTy (first :: second :: more)))
        (tupleTy first) (tupleTy (sideAtoms atoms next side))).toFun)
      ((right.special side).rename (swapRenaming (Δ.snoc (tagsTy (first :: second :: more)))
        (tagsTy (second :: more)) (tupleTy (sideAtoms atoms next side))).toFun)

end

mutual

/-- The shape of the tree: a tree-shaped prefix in front of the cases on
the stored slot, with the two computed specializations. -/
def SpelledDelay.shape {atoms next : List α} : {stack : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay atoms next stack Δ holds s L t) →
    Deferred (tupleTy atoms) (tupleTy next) Δ s t (d.special true) (d.special false)
  | _, _, _, _, _, _, .inspect s _ _ => .here s.2 _ _
  | _, _, _, _, _, _, .unit tail => tail.shape
  | _, _, _, _, _, _, .atom tail => tail.shape
  | _, _, _, .cons top _, _, _, .step tail => .unpack top tail.shape
  | _, _, _, _, _, _, .ask g argument reply => .ask g argument reply.shape
  | _, _, _, _, _, _, .pick _ tail => tail.shape

/-- The shape of a bound reply. A branch is a case on the reply slot. -/
def SpelledDelayTags.shape {atoms next : List α} : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledDelayTags atoms next stack tags Δ holds s L t) →
    Deferred (tupleTy atoms) (tupleTy next) (Δ.snoc (tagsTy tags)) s.succ t (d.special true)
      (d.special false)
  | _, _, _, _, _, _, _, .bind _ tail => tail.shape
  | _, _, _, _, _, _, _, .split _ _ _ left right => .split ⟨0, rfl⟩ left.shape right.shape

end

mutual

/-- The specialization of the tree to a side of the stored reply, as a
tree of the grammar, over given slots of the stack that are the weakened
slots. The payload of the tag is newest and on top of the stack. -/
def SpelledDelay.spec {atoms next : List α} (side : Bool) : {stack : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay atoms next stack Δ holds s L t) →
    (base : Holds (Δ.snoc (tupleTy (sideAtoms atoms next side))) stack) →
    holds.rename (BoundCtx.Renaming.succ Δ (tupleTy (sideAtoms atoms next side))) = base →
    Renamed (SpelledStack (sideAtoms atoms next side :: stack) (Δ.snoc (tupleTy (sideAtoms atoms next side)))
      (.cons ⟨0, rfl⟩ base) L) (d.special side)
  | stack, _, Δ, _, _, _, .inspect (l := l) (r := r) _ left right, base, hb => match side, base, hb with
    | true, _, hb => ⟨_, cast (congrArg (fun b => SpelledStack (atoms :: stack) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ b) L l) hb) left, rfl⟩
    | false, _, hb => ⟨_, cast (congrArg (fun b => SpelledStack (next :: stack) (Δ.snoc (tupleTy next))
        (.cons ⟨0, rfl⟩ b) L r) hb) right, rfl⟩
  | _, _, _, .cons _ _, _, _, .unit tail, .cons _ older', hb =>
    let q := tail.spec side older' (Holds.cons.inj hb).2
    ⟨_, .pick (.there .here) (.unit q.tree), q.term_eq⟩
  | _, _, _, .cons _ _, _, _, .atom tail, .cons _ older', hb =>
    let q := tail.spec side older' (Holds.cons.inj hb).2
    ⟨_, .pick (.there .here) (.atom q.tree), q.term_eq⟩
  | (a :: b :: rest) :: _, _, Δ, .cons _ older, _, _, .step tail, .cons _ older', hb =>
    let q := tail.spec side _ rfl
    let q' := q.tree.renamed
      (beforePairRenaming Δ (tupleTy (sideAtoms atoms next side)) (.base a) (tupleTy (b :: rest)))
      (.cons ⟨2, rfl⟩ (.cons ⟨0, rfl⟩ (older'.rename
        (pastPair (Δ.snoc (tupleTy (sideAtoms atoms next side))) (.base a) (tupleTy (b :: rest))))))
      (congrArg (Holds.cons ⟨2, rfl⟩) (congrArg (Holds.cons ⟨0, rfl⟩)
        (holds_cube older
          (pastPair (Δ.snoc (tupleTy (sideAtoms atoms next side))) (.base a) (tupleTy (b :: rest)))
          (Holds.cons.inj hb).2 (renaming_ext (fun _ => rfl)))))
    ⟨_, .pick (.there .here) (.step (.pick (.there .here) q'.tree)),
      congrArg₂ (fun i x => LetCase.LocallyNameless.Tm.let₂ (.bv i) x) (congrArg Subtype.val (Holds.cons.inj hb).1).symm
        (q'.term_eq.trans (congrArg (fun x => x.rename beforePair) q.term_eq))⟩
  | _, _, Δ, _, _, _, .ask g argument reply, base, hb =>
    let q := reply.spec side base hb
    ⟨_, .ask g (argument.rename (BoundCtx.Renaming.succ Δ (tupleTy (sideAtoms atoms next side)))) q.tree,
      congrArg (LetCase.LocallyNameless.Tm.let₁ (.op g (argTerm (argument.rename
        (BoundCtx.Renaming.succ Δ (tupleTy (sideAtoms atoms next side))))))) q.term_eq⟩
  | _, _, Δ, holds, _, _, .pick sel tail, base, hb =>
    let q := tail.spec side (base.select sel)
      ((Holds.select_rename sel holds
        (BoundCtx.Renaming.succ Δ (tupleTy (sideAtoms atoms next side)))).symm.trans
        (congrArg (Holds.select sel) hb))
    ⟨_, .pick (.there sel) (.pick (.there .here) q.tree), q.term_eq⟩

/-- The specialization of a bound reply to a side of the stored reply, as
a tree of the grammar, with the payload beneath the reply slot. At a
branch the case on the reply is kept: both arms are specialized, moved
beneath the reply slot, and the payload is selected back to the top of
the stack in the first arm. -/
def SpelledDelayTags.spec {atoms next : List α} (side : Bool) : {stack : List (List α)} →
    {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledDelayTags atoms next stack tags Δ holds s L t) →
    (base : Holds (Δ.snoc (tupleTy (sideAtoms atoms next side))) stack) →
    holds.rename (BoundCtx.Renaming.succ Δ (tupleTy (sideAtoms atoms next side))) = base →
    Renamed (SpelledStackTags (sideAtoms atoms next side :: stack) tags
      (Δ.snoc (tupleTy (sideAtoms atoms next side))) (.cons ⟨0, rfl⟩ base) L)
      ((d.special side).rename (swapRenaming Δ (tagsTy tags) (tupleTy (sideAtoms atoms next side))).toFun)
  | _, _, _, Δ, holds, _, _, .bind reply tail, base, hb =>
    let q := tail.spec side _ rfl
    let q' := q.tree.renamed (swapRenaming Δ (tupleTy reply) (tupleTy (sideAtoms atoms next side)))
      (.cons ⟨1, rfl⟩ (.cons ⟨0, rfl⟩
        (base.rename (BoundCtx.Renaming.succ (Δ.snoc (tupleTy (sideAtoms atoms next side))) (tupleTy reply)))))
      (congrArg (Holds.cons ⟨1, rfl⟩) (congrArg (Holds.cons ⟨0, rfl⟩)
        (holds_cube holds
          (BoundCtx.Renaming.succ (Δ.snoc (tupleTy (sideAtoms atoms next side))) (tupleTy reply)) hb
          (renaming_ext (fun _ => rfl)))))
    ⟨_, .bind reply (.pick (.there .here) q'.tree),
      q'.term_eq.trans (congrArg (fun x => x.rename
        (swapRenaming Δ (tupleTy reply) (tupleTy (sideAtoms atoms next side))).toFun) q.term_eq)⟩
  | _, _, _, Δ, holds, _, _, .split first second more left right, base, hb =>
    let ql := left.spec side _ rfl
    let ql' := ql.tree.renamed
      (beforePairRenaming Δ (tupleTy (sideAtoms atoms next side)) (tagsTy (first :: second :: more))
        (tupleTy first))
      (.cons ⟨2, rfl⟩ (.cons ⟨0, rfl⟩ (base.rename
        (pastPair (Δ.snoc (tupleTy (sideAtoms atoms next side))) (tagsTy (first :: second :: more))
          (tupleTy first)))))
      (congrArg (Holds.cons ⟨2, rfl⟩) (congrArg (Holds.cons ⟨0, rfl⟩)
        (holds_cube holds
          (pastPair (Δ.snoc (tupleTy (sideAtoms atoms next side))) (tagsTy (first :: second :: more))
            (tupleTy first)) hb (renaming_ext (fun _ => rfl)))))
    let qr := right.spec side _ rfl
    let qr' := qr.tree.renamed
      (swapRenaming Δ (tagsTy (first :: second :: more)) (tupleTy (sideAtoms atoms next side)))
      (.cons ⟨1, rfl⟩ (base.rename (BoundCtx.Renaming.succ (Δ.snoc (tupleTy (sideAtoms atoms next side)))
        (tagsTy (first :: second :: more)))))
      (congrArg (Holds.cons ⟨1, rfl⟩)
        (holds_cube holds
          (BoundCtx.Renaming.succ (Δ.snoc (tupleTy (sideAtoms atoms next side)))
            (tagsTy (first :: second :: more))) hb (renaming_ext (fun _ => rfl))))
    ⟨_, .split first second more (.pick (.there .here) ql'.tree) qr'.tree,
      congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 0))
        (ql'.term_eq.trans ((congrArg (fun x => x.rename beforePair) ql.term_eq).trans
          (before_eq_swap_swap Δ (tagsTy (first :: second :: more)) (tupleTy first)
            (tupleTy (sideAtoms atoms next side)) (left.special side))))
        (qr'.term_eq.trans (congrArg (fun x => x.rename (LetCase.LocallyNameless.Tm.up
          (swapRenaming Δ (tagsTy (first :: second :: more)) (tupleTy (sideAtoms atoms next side))).toFun))
          qr.term_eq))⟩

end

/-- A reply with two tags inspected after a prefix that may branch, from
the tree alone. The tree starts under the reply slot and inspects it at
every leaf. The shape of the tree and the two specializations to the tags
are computed, and the result is the checked `deferred` node on them. -/
def SpelledStackTags.delayedTree {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
    {holds : Holds Δ stack} (atoms next : List α) {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
    (d : SpelledDelay atoms next stack (Δ.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy [atoms, next]))) 0 L t) :
    SpelledStackTags stack [atoms, next] Δ holds L t :=
  .deferred atoms next [] d.shape
    (d.spec true (holds.rename (pastPair Δ (tagsTy [atoms, next]) (tupleTy atoms)))
      (Holds.rename_comp holds _ _)).tree
    (.bind next (d.spec false _ rfl).tree)
    (d.spec true (holds.rename (pastPair Δ (tagsTy [atoms, next]) (tupleTy atoms)))
      (Holds.rename_comp holds _ _)).term_eq
    (d.spec false _ rfl).term_eq

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
