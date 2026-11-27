module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Thms

/-! # The renaming action on spelled trees

A spelled tree is renamed along a typed renaming of its bound context. The
action is defined on all the spelled families at once: trees in body
position, heads of requests, pending replies and tuples, chains over a
stack of packed tuples, their bound replies, and the arms of a delayed
case. A pending reply or tuple is renamed along a renaming of the context
beneath its pending slot, as for case trees.

The renamed tree is a tree of the same family over the target context. Its
term is the renamed term; this equation is part of the result, so the
action needs no transport of trees along equations. A chain is renamed
onto given slots of its stack in the target context, with a proof that
they are the renamed slots.

The action also renames the shape of a deferred prefix, with its two
specializations.

The second part uses the action. A finite nonbranching prefix of a chain
is a family of its own: requests whose replies have one tag, pattern lets
on the top tuple of the stack, and selections. From a prefix and an arm at
its end, the specialization of the prefix to the tag of the arm is
computed as a tree: the arm is renamed past each slot of the prefix. With
the computed shape of the prefix this gives a reply with two tags
inspected after the prefix, from the prefix and the two arms alone.

The third part renames a prefix. The renamed prefix comes with its end
context, its end slots and its end renaming. A prefix placed under a new
slot, and the renaming that moves a slot bound after the prefix beneath
it, are the instances used for a reply with more tags.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-- A tree of a family over a term, with a proof that the term is a given
one. The result of renaming a tree: the family is the one of the tree over
the target context, and the given term is the renamed term. -/
structure Renamed {m : Nat} (F : LetCase.LocallyNameless.Tm Empty Φ m → Type) (target : LetCase.LocallyNameless.Tm Empty Φ m) where
  /-- The term of the tree. -/
  term : LetCase.LocallyNameless.Tm Empty Φ m
  /-- The tree. -/
  tree : F term
  /-- Its term is the given one. -/
  term_eq : term = target

omit [TaggedSignature α Φ] in
/-- Slots of a stack renamed along two sides of a commuting square, onto
given slots. -/
theorem holds_square {stack : List (List α)} {m i j k : Nat} {Δ : BoundCtx (Ty α) m}
    {Δ₁ : BoundCtx (Ty α) i} {Θ : BoundCtx (Ty α) j} {Ξ : BoundCtx (Ty α) k} (H : Holds Δ stack)
    {H' : Holds Θ stack} {ρ₁ : BoundCtx.Renaming Δ Δ₁} {ρ₂ : BoundCtx.Renaming Δ₁ Ξ}
    {σ₁ : BoundCtx.Renaming Δ Θ} (σ₂ : BoundCtx.Renaming Θ Ξ) (h : H.rename σ₁ = H')
    (e : ρ₁.comp ρ₂ = σ₁.comp σ₂) : (H.rename ρ₁).rename ρ₂ = H'.rename σ₂ :=
  (Holds.rename_comp H ρ₁ ρ₂).trans ((congrArg (fun q => H.rename q) e).trans
    ((Holds.rename_comp H σ₁ σ₂).symm.trans (congrArg (fun q => Holds.rename σ₂ q) h)))

omit [TaggedSignature α Φ] in
/-- Exchanging two slots commutes with renaming beneath them, on terms. -/
theorem swap_rename_square {k j : Nat} {Ω : BoundCtx (Ty α) k} {Ω' : BoundCtx (Ty α) j}
    (ω : BoundCtx.Renaming Ω Ω') (X Z : Ty α) (x : LetCase.LocallyNameless.Tm Empty Φ (k + 2)) :
    (x.rename ((ω.up X).up Z).toFun).rename (swapRenaming Ω' X Z).toFun =
      (x.rename (swapRenaming Ω X Z).toFun).rename ((ω.up Z).up X).toFun :=
  (LetCase.LocallyNameless.Tm.rename_comp ((ω.up X).up Z).toFun (swapRenaming Ω' X Z).toFun x).trans
    ((congrArg (fun q : BoundCtx.Renaming ((Ω.snoc X).snoc Z) ((Ω'.snoc Z).snoc X) => x.rename q.toFun)
      (swapRenaming_natural ω X Z).symm).trans
      (LetCase.LocallyNameless.Tm.rename_comp (swapRenaming Ω X Z).toFun ((ω.up Z).up X).toFun x).symm)

omit [TaggedSignature α Φ] in
/-- Moving the newest slot beneath two slots commutes with renaming beneath
them, on terms. -/
theorem before_rename_square {k j : Nat} (f : Fin k → Fin j) (x : LetCase.LocallyNameless.Tm Empty Φ (k + 3)) :
    (x.rename (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up f)))).rename beforePair =
      (x.rename beforePair).rename (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up f))) :=
  (LetCase.LocallyNameless.Tm.rename_comp (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up f))) beforePair x).trans
    ((LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun i => Fin.cases rfl
      (fun i => Fin.cases rfl (fun _ => rfl) i) i) i) x).trans
      (LetCase.LocallyNameless.Tm.rename_comp beforePair (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up f))) x).symm)

/-- The renamed shape of a deferred prefix, with its terms. -/
structure Deferred.Renamed (X Y : Ty α) {k j : Nat} {Γ : BoundCtx (Ty α) k} {Γ' : BoundCtx (Ty α) j}
    (ρ : BoundCtx.Renaming Γ Γ') (s : Fin k) (t : LetCase.LocallyNameless.Tm Empty Φ k) (l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)) where
  /-- The term of the renamed prefix. -/
  term : LetCase.LocallyNameless.Tm Empty Φ j
  /-- Its specialization to the first tag. -/
  left : LetCase.LocallyNameless.Tm Empty Φ (j + 1)
  /-- Its specialization to the other tags. -/
  right : LetCase.LocallyNameless.Tm Empty Φ (j + 1)
  /-- The renamed shape. -/
  shape : Deferred X Y Γ' (ρ.toFun s) term left right
  /-- The term is the renamed term. -/
  term_eq : term = t.rename ρ.toFun
  /-- The first specialization is the renamed first specialization. -/
  left_eq : left = l.rename (ρ.up X).toFun
  /-- The other specialization is the renamed other specialization. -/
  right_eq : right = r.rename (ρ.up Y).toFun

/-- The renaming action on the shape of a deferred prefix. The requests
and the destructured slots are renamed, and the two specializations are
renamed with the payload kept newest. -/
def Deferred.renamed {X Y : Ty α} : {k : Nat} → {Γ : BoundCtx (Ty α) k} → {s : Fin k} →
    {t : LetCase.LocallyNameless.Tm Empty Φ k} → {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} → Deferred X Y Γ s t l r → {j : Nat} →
    {Γ' : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Γ Γ') → Deferred.Renamed X Y ρ s t l r
  | _, _, s, _, _, _, .here hs l r, _, _, ρ =>
    ⟨_, _, _, .here ((ρ.typed s).trans hs) (l.rename (ρ.up X).toFun) (r.rename (ρ.up Y).toFun), rfl, rfl, rfl⟩
  | _, Γ, _, _, _, _, .ask (l := l) (r := r) g argument rest, _, Γ', ρ =>
    let q := rest.renamed (ρ.up (tagsTy (replyTags g)))
    have arg (W : Ty α) : argTerm (Φ := Φ) ((argument.rename ρ).rename (BoundCtx.Renaming.succ Γ' W)) =
        (argTerm (argument.rename (BoundCtx.Renaming.succ Γ W))).rename (ρ.up W).toFun :=
      (congrArg argTerm ((assembly_rename_comp argument ρ (BoundCtx.Renaming.succ Γ' W)).trans
        ((congrArg (fun q => argument.rename q) (renaming_ext (ρ := ρ.comp (BoundCtx.Renaming.succ Γ' W))
          (π := (BoundCtx.Renaming.succ Γ W).comp (ρ.up W)) (fun _ => rfl))).trans
          (assembly_rename_comp argument (BoundCtx.Renaming.succ Γ W) (ρ.up W)).symm))).trans
        (argTerm_rename (argument.rename (BoundCtx.Renaming.succ Γ W)) (ρ.up W)).symm
    ⟨_, _, _, .ask g (argument.rename ρ) q.shape,
      congrArg₂ LetCase.LocallyNameless.Tm.let₁ (congrArg (LetCase.LocallyNameless.Tm.op g) (argTerm_rename argument ρ)).symm q.term_eq,
      congrArg₂ LetCase.LocallyNameless.Tm.let₁ (congrArg (LetCase.LocallyNameless.Tm.op g) (arg X))
        ((congrArg (fun x => x.rename (swapRenaming Γ' (tagsTy (replyTags g)) X).toFun) q.left_eq).trans
          (swap_rename_square ρ (tagsTy (replyTags g)) X l)),
      congrArg₂ LetCase.LocallyNameless.Tm.let₁ (congrArg (LetCase.LocallyNameless.Tm.op g) (arg Y))
        ((congrArg (fun x => x.rename (swapRenaming Γ' (tagsTy (replyTags g)) Y).toFun) q.right_eq).trans
          (swap_rename_square ρ (tagsTy (replyTags g)) Y r))⟩
  | _, _, _, _, _, _, .unpack (A := A) (B := B) (l := l) (r := r) x rest, _, _, ρ =>
    let q := rest.renamed ((ρ.up A).up B)
    ⟨_, _, _, .unpack (x.rename ρ) q.shape,
      congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv (ρ.toFun x.1))) q.term_eq,
      congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv (ρ.toFun x.1).succ))
        ((congrArg (fun x => x.rename beforePair) q.left_eq).trans (before_rename_square ρ.toFun l)),
      congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv (ρ.toFun x.1).succ))
        ((congrArg (fun x => x.rename beforePair) q.right_eq).trans (before_rename_square ρ.toFun r))⟩

mutual

/-- The renaming action on a spelled tree in body position. -/
def Spelled.renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} → Spelled β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Renamed (Spelled γ L) (t.rename ρ.toFun)
  | _, _, _, .ret exit payload, _, _, ρ =>
    ⟨_, .ret exit (payload.rename ρ),
      ((ExitAt.term_rename exit ρ.toFun _).trans (congrArg exit.term (argTerm_rename payload ρ))).symm⟩
  | _, _, _, .ask f argument head, _, _, ρ =>
    let r := head.renamed ρ (.op f (argTerm (argument.rename ρ)))
      (congrArg (LetCase.LocallyNameless.Tm.op f) (argTerm_rename argument ρ)).symm
    ⟨_, .ask f (argument.rename ρ) r.tree, r.term_eq⟩
  | _, _, _, .chain c, _, _, ρ =>
    let r := c.renamed ρ .nil rfl
    ⟨_, .chain r.tree, r.term_eq⟩

/-- The renaming action on the head of a request. The renamed request term
is given. -/
def SpelledHead.renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → SpelledHead tags e β L t → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    (ρ : BoundCtx.Renaming β γ) → (e' : LetCase.LocallyNameless.Tm Empty Φ m) → e' = e.rename ρ.toFun →
    Renamed (SpelledHead tags e' γ L) (t.rename ρ.toFun)
  | _, _, _, _, _, .bind reply, _, _, ρ, _, he =>
    let r := reply.renamed ρ
    ⟨_, .bind r.tree, congrArg₂ LetCase.LocallyNameless.Tm.let₁ he r.term_eq⟩
  | _, _, _, _, _, .destruct a b rest later, _, _, ρ, _, he =>
    let r := later.renamed (ρ.up (.base a))
    ⟨_, .destruct a b rest r.tree, congrArg₂ LetCase.LocallyNameless.Tm.let₂ he r.term_eq⟩
  | _, _, _, _, _, .branch atoms next rest left right, _, _, ρ, _, he =>
    let rl := left.renamed ρ
    let rr := right.renamed ρ
    ⟨_, .branch atoms next rest rl.tree rr.tree, congr (congrArg₂ LetCase.LocallyNameless.Tm.case he rl.term_eq) rr.term_eq⟩

/-- The renaming action on a pending reply, along a renaming of the context
beneath its slot. -/
def SpelledTags.renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTags tags β L t → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    (ρ : BoundCtx.Renaming β γ) → Renamed (SpelledTags tags γ L) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
  | _, _, _, _, .only atoms payload, _, _, ρ =>
    let r := payload.renamed ρ
    ⟨_, .only atoms r.tree, r.term_eq⟩
  | _, _, _, _, .split atoms next rest left right, _, _, ρ =>
    let rl := left.renamed (ρ.up (tagsTy (atoms :: next :: rest)))
    let rr := right.renamed (ρ.up (tagsTy (atoms :: next :: rest)))
    ⟨_, .split atoms next rest rl.tree rr.tree, congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 0)) rl.term_eq rr.term_eq⟩

/-- The renaming action on a pending tuple, along a renaming of the context
beneath its slot. -/
def SpelledTuple.renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTuple atoms β L t → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    (ρ : BoundCtx.Renaming β γ) → Renamed (SpelledTuple atoms γ L) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
  | _, _, _, _, .unit body, _, _, ρ =>
    let r := body.renamed (ρ.up (tupleTy ([] : List α)))
    ⟨_, .unit r.tree, r.term_eq⟩
  | _, _, _, _, .atom a body, _, _, ρ =>
    let r := body.renamed (ρ.up (tupleTy [a]))
    ⟨_, .atom a r.tree, r.term_eq⟩
  | _, _, _, _, .pair a b rest later, _, _, ρ =>
    let r := later.renamed ((ρ.up (tupleTy (a :: b :: rest))).up (.base a))
    ⟨_, .pair a b rest r.tree, congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv 0)) r.term_eq⟩
  | _, _, _, _, .hold atoms chain, _, _, ρ =>
    let r := chain.renamed (ρ.up (tupleTy atoms)) (.cons ⟨0, rfl⟩ .nil) rfl
    ⟨_, .hold atoms r.tree, r.term_eq⟩

/-- The renaming action on a chain over a stack of packed tuples, onto
given slots of the stack that are the renamed slots. -/
def SpelledStack.renamed : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledStack stack Δ holds L t → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) →
    holds.rename ρ = holds' → Renamed (SpelledStack stack Θ holds' L) (t.rename ρ.toFun)
  | _, _, _, _, _, .done body, _, _, ρ, .nil, _ =>
    let r := body.renamed ρ
    ⟨_, .done r.tree, r.term_eq⟩
  | _, _, _, .cons _ _, _, .unit next, _, _, ρ, .cons _ older', h =>
    let r := next.renamed ρ older' (Holds.cons.inj h).2
    ⟨_, .unit r.tree, r.term_eq⟩
  | _, _, _, .cons _ _, _, .atom next, _, _, ρ, .cons _ older', h =>
    let r := next.renamed ρ older' (Holds.cons.inj h).2
    ⟨_, .atom r.tree, r.term_eq⟩
  | (a :: b :: rest) :: _, _, _, .cons _ older, _, .step next, _, Θ, ρ, .cons _ older', h =>
    let r := next.renamed ((ρ.up (.base a)).up (tupleTy (b :: rest)))
      (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
        (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl))))
    ⟨_, .step r.tree, congrArg₂ (fun i x => LetCase.LocallyNameless.Tm.let₂ (.bv i) x)
      (congrArg Subtype.val (Holds.cons.inj h).1).symm r.term_eq⟩
  | _, _, _, _, _, .ask g argument reply, _, _, ρ, holds', h =>
    let r := reply.renamed ρ holds' h
    ⟨_, .ask g (argument.rename ρ) r.tree,
      congrArg₂ LetCase.LocallyNameless.Tm.let₁ (congrArg (LetCase.LocallyNameless.Tm.op g) (argTerm_rename argument ρ)).symm r.term_eq⟩
  | _, _, _, holds, _, .pick sel next, _, _, ρ, holds', h =>
    let r := next.renamed ρ (holds'.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h))
    ⟨_, .pick sel r.tree, r.term_eq⟩

/-- The renaming action on the bound reply of a request of a chain. -/
def SpelledStackTags.renamed : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledStackTags stack tags Δ holds L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) → holds.rename ρ = holds' →
    Renamed (SpelledStackTags stack tags Θ holds' L) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
  | _, _, _, _, holds, _, .bind atoms next, _, Θ, ρ, holds', h =>
    let r := next.renamed (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl))))
    ⟨_, .bind atoms r.tree, r.term_eq⟩
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
  | _, tags, _, _, _, _, .later g argument arms, _, _, ρ, holds', h =>
    let r := arms.renamed ρ holds' h
    ⟨_, .later g (argument.rename (ρ.up (tagsTy tags))) r.tree,
      congrArg₂ LetCase.LocallyNameless.Tm.let₁ (congrArg (LetCase.LocallyNameless.Tm.op g) (argTerm_rename argument (ρ.up (tagsTy tags)))).symm r.term_eq⟩
  | _, _, _, _, holds, _, .deferred atoms next more shape left right hl hr, _, Θ, ρ, holds', h =>
    let q := shape.renamed (ρ.up (tagsTy (atoms :: next :: more)))
    let rl := left.renamed ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
    let rr := right.renamed (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl)))
    ⟨_, .deferred atoms next more q.shape rl.tree rr.tree
      (rl.term_eq.trans ((congrArg (fun x => x.rename
        ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms)).toFun) hl).trans q.left_eq.symm))
      (rr.term_eq.trans ((congrArg (fun x => x.rename
        ((ρ.up (tagsTy (atoms :: next :: more))).up (tagsTy (next :: more))).toFun) hr).trans q.right_eq.symm)),
      q.term_eq⟩

/-- The renaming action on the arms of a case delayed across one request. -/
def SpelledLaterTags.renamed : {stack : List (List α)} → {tags : List (List α)} → {g : Φ} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)} →
    SpelledLaterTags stack tags g Δ holds L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) → holds.rename ρ = holds' →
    Renamed (SpelledLaterTags stack tags g Θ holds' L) (t.rename (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up ρ.toFun)))
  | _, _, _, _, _, holds, _, .only atoms next, _, Θ, ρ, holds', h =>
    let r := next.renamed (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl))))
    ⟨_, .only atoms r.tree, r.term_eq⟩
  | _, _, g, _, _, holds, _, .split (l := l) (r := r) atoms next more left right, _, Θ, ρ, holds', h =>
    let rl := left.renamed ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
    let rr := right.renamed (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl)))
    ⟨_, .split atoms next more rl.tree rr.tree, congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 1))
      ((congrArg (fun x => x.rename (swapRenaming (Θ.snoc (tagsTy (atoms :: next :: more))) (tupleTy atoms)
          (tagsTy (replyTags g))).toFun) rl.term_eq).trans
        (swap_rename_square (ρ.up (tagsTy (atoms :: next :: more))) (tupleTy atoms) (tagsTy (replyTags g)) l))
      ((congrArg (fun x => x.rename (swapRenaming (Θ.snoc (tagsTy (atoms :: next :: more)))
          (tagsTy (next :: more)) (tagsTy (replyTags g))).toFun) rr.term_eq).trans
        (swap_rename_square (ρ.up (tagsTy (atoms :: next :: more))) (tagsTy (next :: more))
          (tagsTy (replyTags g)) r))⟩

end

/-! ## A finite nonbranching prefix

The prefix of a chain over a stack: requests whose replies have one tag
and are pushed on the stack, pattern lets on the top tuple, and selections
of a tuple. It runs from a stack, a context and slots of the stack to
those at its end, and it does not branch. -/

mutual

/-- A finite nonbranching prefix of a chain over a stack of packed tuples,
with the stack, the context and the slots of the stack at its end. -/
inductive SpelledPrefix : (stack : List (List α)) → {m : Nat} → (Δ : BoundCtx (Ty α) m) → Holds Δ stack →
    (stack' : List (List α)) → {m' : Nat} → (Δ' : BoundCtx (Ty α) m') → Holds Δ' stack' → Type where
  | stop {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} :
      SpelledPrefix stack Δ holds stack Δ holds
  | unit {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy ([] : List α))}
      {older : Holds Δ stack} {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
      {holds' : Holds Δ' stack'} (next : SpelledPrefix stack Δ older stack' Δ' holds') :
      SpelledPrefix ([] :: stack) Δ (.cons top older) stack' Δ' holds'
  | atom {c : α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy [c])}
      {older : Holds Δ stack} {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
      {holds' : Holds Δ' stack'} (next : SpelledPrefix stack Δ older stack' Δ' holds') :
      SpelledPrefix ([c] :: stack) Δ (.cons top older) stack' Δ' holds'
  | step {a b : α} {rest : List α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {top : Slot Δ (tupleTy (a :: b :: rest))} {older : Holds Δ stack} {stack' : List (List α)} {m' : Nat}
      {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
      (next : SpelledPrefix ((b :: rest) :: stack) ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest)))
        (.cons ⟨0, rfl⟩ (older.rename (pastPair Δ (.base a) (tupleTy (b :: rest))))) stack' Δ' holds') :
      SpelledPrefix ((a :: b :: rest) :: stack) Δ (.cons top older) stack' Δ' holds'
  | ask {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
      (g : Φ) (argument : Assembly Δ (instrSrc g))
      (reply : SpelledPrefixTags stack (replyTags g) Δ holds stack' Δ' holds') :
      SpelledPrefix stack Δ holds stack' Δ' holds'
  | pick {stack : List (List α)} {atoms : List α} {rest : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {holds : Holds Δ stack} {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
      {holds' : Holds Δ' stack'} (sel : Select stack atoms rest)
      (next : SpelledPrefix (atoms :: rest) Δ (holds.select sel) stack' Δ' holds') :
      SpelledPrefix stack Δ holds stack' Δ' holds'

/-- The bound reply of a request of a prefix. It has one tag, and its tuple
is pushed on the stack. -/
inductive SpelledPrefixTags : (stack : List (List α)) → List (List α) → {m : Nat} → (Δ : BoundCtx (Ty α) m) →
    Holds Δ stack → (stack' : List (List α)) → {m' : Nat} → (Δ' : BoundCtx (Ty α) m') → Holds Δ' stack' →
    Type where
  | bind {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
      (atoms : List α)
      (next : SpelledPrefix (atoms :: stack) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)))) stack' Δ' holds') :
      SpelledPrefixTags stack [atoms] Δ holds stack' Δ' holds'

end

mutual

/-- The weakening of the context at the start of a prefix into the context
at its end. -/
def SpelledPrefix.weaken : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds' → BoundCtx.Renaming Δ Δ'
  | _, _, Δ, _, _, _, _, _, .stop => .id Δ
  | _, _, _, _, _, _, _, _, .unit next => next.weaken
  | _, _, _, _, _, _, _, _, .atom next => next.weaken
  | (a :: b :: rest) :: _, _, Δ, _, _, _, _, _, .step next =>
    (pastPair Δ (.base a) (tupleTy (b :: rest))).comp next.weaken
  | _, _, _, _, _, _, _, _, .ask _ _ reply => reply.weaken
  | _, _, _, _, _, _, _, _, .pick _ next => next.weaken

/-- The weakening of the context beneath a bound reply into the context at
the end of the prefix. -/
def SpelledPrefixTags.weaken : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds' → BoundCtx.Renaming Δ Δ'
  | _, _, _, Δ, _, _, _, _, _, .bind atoms next => (BoundCtx.Renaming.succ Δ (tupleTy atoms)).comp next.weaken

end

mutual

/-- The term of a prefix around a term at its end. -/
def SpelledPrefix.plug : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds' → LetCase.LocallyNameless.Tm Empty Φ m' →
    LetCase.LocallyNameless.Tm Empty Φ m
  | _, _, _, _, _, _, _, _, .stop, e => e
  | _, _, _, _, _, _, _, _, .unit next, e => next.plug e
  | _, _, _, _, _, _, _, _, .atom next, e => next.plug e
  | _, _, _, .cons top _, _, _, _, _, .step next, e => .let₂ (.bv top.1) (next.plug e)
  | _, _, _, _, _, _, _, _, .ask g argument reply, e => .let₁ (.op g (argTerm argument)) (reply.plug e)
  | _, _, _, _, _, _, _, _, .pick _ next, e => next.plug e

/-- The term of a bound reply of a prefix around a term at its end. -/
def SpelledPrefixTags.plug : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds' → LetCase.LocallyNameless.Tm Empty Φ m' → LetCase.LocallyNameless.Tm Empty Φ (m + 1)
  | _, _, _, _, _, _, _, _, _, .bind _ next, e => next.plug e

end

mutual

/-- The term of the specialization of a prefix: the prefix under a payload
slot `Z`, around a term at its end that has the payload newest. The
payload is beneath the slots of the prefix, so the term at the end is
renamed past each of them. -/
def SpelledPrefix.special (Z : Ty α) : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds' → LetCase.LocallyNameless.Tm Empty Φ (m' + 1) →
    LetCase.LocallyNameless.Tm Empty Φ (m + 1)
  | _, _, _, _, _, _, _, _, .stop, e => e
  | _, _, _, _, _, _, _, _, .unit next, e => next.special Z e
  | _, _, _, _, _, _, _, _, .atom next, e => next.special Z e
  | _, _, _, .cons top _, _, _, _, _, .step next, e =>
    .let₂ (.bv top.1.succ) ((next.special Z e).rename beforePair)
  | _, _, Δ, _, _, _, _, _, .ask g argument reply, e =>
    .let₁ (.op g (argTerm (argument.rename (BoundCtx.Renaming.succ Δ Z))))
      ((reply.special Z e).rename (swapRenaming Δ (tagsTy (replyTags g)) Z).toFun)
  | _, _, _, _, _, _, _, _, .pick _ next, e => next.special Z e

/-- The term of the specialization of a bound reply of a prefix, with the
payload newest. -/
def SpelledPrefixTags.special (Z : Ty α) : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds' → LetCase.LocallyNameless.Tm Empty Φ (m' + 1) →
    LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)
  | _, _, _, _, _, _, _, _, _, .bind _ next, e => next.special Z e

end

mutual

/-- The shape of a prefix around a case on a stored slot of sum type. Its
two specializations are the specializations of the prefix around the two
arms. -/
def SpelledPrefix.shape {X Y : Ty α} : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') → (s : Fin m) →
    Δ.get s = .coprod X Y → (l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) →
    Deferred X Y Δ s (p.plug (.case (.bv (p.weaken.toFun s)) l r)) (p.special X l) (p.special Y r)
  | _, _, _, _, _, _, _, _, .stop, _, hs, l, r => .here hs l r
  | _, _, _, _, _, _, _, _, .unit next, s, hs, l, r => next.shape s hs l r
  | _, _, _, _, _, _, _, _, .atom next, s, hs, l, r => next.shape s hs l r
  | (a :: b :: rest) :: _, _, Δ, .cons top _, _, _, _, _, .step next, s, hs, l, r =>
    .unpack top (next.shape s.succ.succ
      (((pastPair Δ (.base a) (tupleTy (b :: rest))).typed s).trans hs) l r)
  | _, _, _, _, _, _, _, _, .ask g argument reply, s, hs, l, r =>
    .ask g argument (reply.shape s hs l r)
  | _, _, _, _, _, _, _, _, .pick _ next, s, hs, l, r => next.shape s hs l r

/-- The shape of a bound reply of a prefix around a case on a stored
slot. -/
def SpelledPrefixTags.shape {X Y : Ty α} : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → (s : Fin m) →
    Δ.get s = .coprod X Y → (l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)) →
    Deferred X Y (Δ.snoc (tagsTy tags)) s.succ (p.plug (.case (.bv (p.weaken.toFun s)) l r))
      (p.special X l) (p.special Y r)
  | _, _, _, Δ, _, _, _, _, _, .bind atoms next, s, hs, l, r =>
    next.shape s.succ (((BoundCtx.Renaming.succ Δ (tupleTy atoms)).typed s).trans hs) l r

end

omit [TaggedSignature α Φ] in
/-- Slots of a stack renamed along three renamings, onto the renamed
given slots. -/
theorem holds_cube {stack : List (List α)} {m i j k l : Nat} {Δ : BoundCtx (Ty α) m}
    {Δ₁ : BoundCtx (Ty α) i} {Δ₂ : BoundCtx (Ty α) j} {Θ : BoundCtx (Ty α) k} {Ξ : BoundCtx (Ty α) l}
    (H : Holds Δ stack) {H' : Holds Θ stack} {ρ₁ : BoundCtx.Renaming Δ Δ₁} {ρ₂ : BoundCtx.Renaming Δ₁ Δ₂}
    {ρ₃ : BoundCtx.Renaming Δ₂ Ξ} {σ₁ : BoundCtx.Renaming Δ Θ} (σ₂ : BoundCtx.Renaming Θ Ξ)
    (h : H.rename σ₁ = H') (e : (ρ₁.comp ρ₂).comp ρ₃ = σ₁.comp σ₂) :
    ((H.rename ρ₁).rename ρ₂).rename ρ₃ = H'.rename σ₂ :=
  (congrArg (fun q => Holds.rename ρ₃ q) (Holds.rename_comp H ρ₁ ρ₂)).trans (holds_square H σ₂ h e)

mutual

/-- The specialization of a prefix to a tag, as a tree: the prefix under
the payload of the tag, around the arm of the tag. The arm has the payload
newest and on top of the stack. The payload is placed beneath the slots of
the prefix: the arm is renamed past each of them by the renaming action,
and selected back to the top of the stack. The result is over given slots
of the stack that are the weakened slots. -/
def SpelledPrefix.spec (atoms : List α) : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') →
    {e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)} →
    SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L e →
    (base : Holds (Δ.snoc (tupleTy atoms)) stack) →
    holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)) = base →
    Renamed (SpelledStack (atoms :: stack) (Δ.snoc (tupleTy atoms)) (.cons ⟨0, rfl⟩ base) L)
      (p.special (tupleTy atoms) e)
  | _, _, _, _, _, _, _, _, .stop, _, arm, _, hb => ⟨_, hb ▸ arm, rfl⟩
  | _, _, _, .cons _ _, _, _, _, _, .unit next, _, arm, .cons _ older', hb =>
    let q := next.spec atoms arm older' (Holds.cons.inj hb).2
    ⟨_, .pick (.there .here) (.unit q.tree), q.term_eq⟩
  | _, _, _, .cons _ _, _, _, _, _, .atom next, _, arm, .cons _ older', hb =>
    let q := next.spec atoms arm older' (Holds.cons.inj hb).2
    ⟨_, .pick (.there .here) (.atom q.tree), q.term_eq⟩
  | (a :: b :: rest) :: _, _, Δ, .cons _ older, _, _, _, _, .step next, _, arm, .cons _ older', hb =>
    let q := next.spec atoms arm _ rfl
    let q' := q.tree.renamed (beforePairRenaming Δ (tupleTy atoms) (.base a) (tupleTy (b :: rest)))
      (.cons ⟨2, rfl⟩ (.cons ⟨0, rfl⟩
        (older'.rename (pastPair (Δ.snoc (tupleTy atoms)) (.base a) (tupleTy (b :: rest))))))
      (congrArg (Holds.cons ⟨2, rfl⟩) (congrArg (Holds.cons ⟨0, rfl⟩)
        (holds_cube older (pastPair (Δ.snoc (tupleTy atoms)) (.base a) (tupleTy (b :: rest)))
          (Holds.cons.inj hb).2 (renaming_ext (fun _ => rfl)))))
    ⟨_, .pick (.there .here) (.step (.pick (.there .here) q'.tree)),
      congrArg₂ (fun i x => LetCase.LocallyNameless.Tm.let₂ (.bv i) x) (congrArg Subtype.val (Holds.cons.inj hb).1).symm
        (q'.term_eq.trans (congrArg (fun x => x.rename beforePair) q.term_eq))⟩
  | _, _, Δ, _, _, _, _, _, .ask g argument reply, _, arm, base, hb =>
    let q := reply.spec atoms arm base hb
    ⟨_, .ask g (argument.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms))) q.tree,
      congrArg (LetCase.LocallyNameless.Tm.let₁ (.op g (argTerm (argument.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms))))))
        q.term_eq⟩
  | _, _, Δ, holds, _, _, _, _, .pick sel next, _, arm, base, hb =>
    let q := next.spec atoms arm (base.select sel)
      ((Holds.select_rename sel holds (BoundCtx.Renaming.succ Δ (tupleTy atoms))).symm.trans
        (congrArg (Holds.select sel) hb))
    ⟨_, .pick (.there sel) (.pick (.there .here) q.tree), q.term_eq⟩

/-- The specialization of a bound reply of a prefix to a tag, as a tree. -/
def SpelledPrefixTags.spec (atoms : List α) : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {e : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)} →
    SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L e →
    (base : Holds (Δ.snoc (tupleTy atoms)) stack) →
    holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)) = base →
    Renamed (SpelledStackTags (atoms :: stack) tags (Δ.snoc (tupleTy atoms)) (.cons ⟨0, rfl⟩ base) L)
      ((p.special (tupleTy atoms) e).rename (swapRenaming Δ (tagsTy tags) (tupleTy atoms)).toFun)
  | _, _, _, Δ, holds, _, _, _, _, .bind reply next, _, arm, base, hb =>
    let q := next.spec atoms arm _ rfl
    let q' := q.tree.renamed (swapRenaming Δ (tupleTy reply) (tupleTy atoms))
      (.cons ⟨1, rfl⟩ (.cons ⟨0, rfl⟩
        (base.rename (BoundCtx.Renaming.succ (Δ.snoc (tupleTy atoms)) (tupleTy reply)))))
      (congrArg (Holds.cons ⟨1, rfl⟩) (congrArg (Holds.cons ⟨0, rfl⟩)
        (holds_cube holds (BoundCtx.Renaming.succ (Δ.snoc (tupleTy atoms)) (tupleTy reply)) hb
          (renaming_ext (fun _ => rfl)))))
    ⟨_, .bind reply (.pick (.there .here) q'.tree),
      q'.term_eq.trans (congrArg (fun x => x.rename (swapRenaming Δ (tupleTy reply) (tupleTy atoms)).toFun)
        q.term_eq)⟩

end

/-- A reply with two tags inspected after a finite nonbranching prefix,
from the prefix and the two arms at its end alone. The prefix starts under
the reply slot, and its requests are assembled from atom slots, so they do
not read the reply. Each arm has the payload of its tag newest and on top
of the stack, in the context at the end of the prefix. The term is the
prefix around the case on the reply slot. The shape of the prefix and the
two specializations to the tags are computed. -/
def SpelledStackTags.delayed {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
    {holds : Holds Δ stack} (atoms next : List α) {stack' : List (List α)} {m' : Nat}
    {Δ' : BoundCtx (Ty α) m'} {holds' : Holds Δ' stack'}
    (p : SpelledPrefix (Φ := Φ) stack (Δ.snoc (tagsTy [atoms, next]))
      (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy [atoms, next]))) stack' Δ' holds')
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m' + 1)}
    (left : SpelledStack (atoms :: stack') (Δ'.snoc (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy atoms)))) L l)
    (right : SpelledStack (next :: stack') (Δ'.snoc (tupleTy next))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Δ' (tupleTy next)))) L r) :
    SpelledStackTags stack [atoms, next] Δ holds L (p.plug (.case (.bv (p.weaken.toFun 0)) l r)) :=
  .deferred atoms next [] (p.shape 0 rfl l r)
    (p.spec atoms left (holds.rename (pastPair Δ (tagsTy [atoms, next]) (tupleTy atoms)))
      (Holds.rename_comp holds _ _)).tree
    (.bind next (p.spec next right _ rfl).tree)
    (p.spec atoms left (holds.rename (pastPair Δ (tagsTy [atoms, next]) (tupleTy atoms)))
      (Holds.rename_comp holds _ _)).term_eq
    (p.spec next right _ rfl).term_eq

/-! ## Renaming a prefix

A prefix is renamed along a renaming of the context at its start. The
context at its end is not given: the renamed prefix comes with the context
and the slots of the stack at its end, and with the end renaming, from the
end of the prefix into the end of the renamed prefix. -/

/-- A renaming out of a context with one more slot: a renaming of the
context, and a slot of the target for the new one. -/
def snocRenaming {m k : Nat} {Δ : BoundCtx (Ty α) m} {Ξ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming Δ Ξ)
    {Z : Ty α} (z : Slot Ξ Z) : BoundCtx.Renaming (Δ.snoc Z) Ξ where
  toFun := Fin.cases z.1 ρ.toFun
  typed := Fin.cases z.2 ρ.typed

/-- A tree of a family over an end context and end slots of a stack, with
the renaming from a given end context into that one, which carries the
given end slots to those. The result of renaming a prefix. -/
structure EndRenamed {stack' : List (List α)}
    (F : {j : Nat} → (Ξ : BoundCtx (Ty α) j) → Holds Ξ stack' → Type) {m' : Nat}
    (Δ' : BoundCtx (Ty α) m') (holds' : Holds Δ' stack') where
  /-- The size of the end context. -/
  size : Nat
  /-- The end context. -/
  ctx : BoundCtx (Ty α) size
  /-- The slots of the stack at the end. -/
  slots : Holds ctx stack'
  /-- The tree. -/
  tree : F ctx slots
  /-- The end renaming. -/
  ren : BoundCtx.Renaming Δ' ctx
  /-- The end renaming carries the given end slots to the end slots. -/
  slots_eq : holds'.rename ren = slots

mutual

/-- The renaming action on a prefix, onto given slots of the stack that
are the renamed slots. The requests are renamed, and the renaming is
lifted under each slot the prefix binds. -/
def SpelledPrefix.renamed : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds' → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Θ) → (H : Holds Θ stack) → holds.rename ρ = H →
    EndRenamed (fun Ξ H' => SpelledPrefix (Φ := Φ) stack Θ H stack' Ξ H') Δ' holds'
  | _, _, _, _, _, _, _, _, .stop, _, Θ, ρ, H, h => ⟨_, Θ, H, .stop, ρ, h⟩
  | _, _, _, .cons _ _, _, _, _, _, .unit next, _, _, ρ, .cons _ older', h =>
    let q := next.renamed ρ older' (Holds.cons.inj h).2
    ⟨_, _, _, .unit q.tree, q.ren, q.slots_eq⟩
  | _, _, _, .cons _ _, _, _, _, _, .atom next, _, _, ρ, .cons _ older', h =>
    let q := next.renamed ρ older' (Holds.cons.inj h).2
    ⟨_, _, _, .atom q.tree, q.ren, q.slots_eq⟩
  | (a :: b :: rest) :: _, _, _, .cons _ older, _, _, _, _, .step next, _, Θ, ρ, .cons _ older', h =>
    let q := next.renamed ((ρ.up (.base a)).up (tupleTy (b :: rest)))
      (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
        (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl))))
    ⟨_, _, _, .step q.tree, q.ren, q.slots_eq⟩
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, ρ, H, h =>
    let q := reply.renamed ρ H h
    ⟨_, _, _, .ask g (argument.rename ρ) q.tree, q.ren, q.slots_eq⟩
  | _, _, _, holds, _, _, _, _, .pick sel next, _, _, ρ, H, h =>
    let q := next.renamed ρ (H.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h))
    ⟨_, _, _, .pick sel q.tree, q.ren, q.slots_eq⟩

/-- The renaming action on the bound reply of a request of a prefix. -/
def SpelledPrefixTags.renamed : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds' → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming Δ Θ) → (H : Holds Θ stack) → holds.rename ρ = H →
    EndRenamed (fun Ξ H' => SpelledPrefixTags (Φ := Φ) stack tags Θ H stack' Ξ H') Δ' holds'
  | _, _, _, _, holds, _, _, _, _, .bind atoms next, _, Θ, ρ, H, h =>
    let q := next.renamed (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (H.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl))))
    ⟨_, _, _, .bind atoms q.tree, q.ren, q.slots_eq⟩

end

/-- A prefix placed under a new slot `Z`: the prefix renamed along the
weakening past `Z`, with its end context and end renaming. -/
def SpelledPrefix.under (Z : Ty α) {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
    {holds : Holds Δ stack} {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
    {holds' : Holds Δ' stack'} (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') :
    EndRenamed (fun Ξ H' => SpelledPrefix (Φ := Φ) stack (Δ.snoc Z)
      (holds.rename (BoundCtx.Renaming.succ Δ Z)) stack' Ξ H') Δ' holds' :=
  p.renamed (BoundCtx.Renaming.succ Δ Z) _ rfl

/-- The renaming that moves a slot `Z` bound after a prefix beneath it:
from the end of the prefix with `Z` newest into the end of the prefix
placed under `Z`. The slots of the end of the prefix follow the end
renaming, and `Z` goes to the weakened slot. -/
def SpelledPrefix.past (Z : Ty α) {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
    {holds : Holds Δ stack} {stack' : List (List α)} {m' : Nat} {Δ' : BoundCtx (Ty α) m'}
    {holds' : Holds Δ' stack'} (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') :
    BoundCtx.Renaming (Δ'.snoc Z) (p.under Z).ctx :=
  snocRenaming (p.under Z).ren ⟨(p.under Z).tree.weaken.toFun 0, (p.under Z).tree.weaken.typed 0⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
