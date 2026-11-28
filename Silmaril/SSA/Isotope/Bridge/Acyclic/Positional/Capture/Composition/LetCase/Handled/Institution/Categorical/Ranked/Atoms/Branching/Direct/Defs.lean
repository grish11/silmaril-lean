module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

/-! # Spellings of a request on a tagged tuple reply

The case trees of the tagged signatures bind the reply of a request and
then consume the bound slot. A spelled tree may consume the reply at the
request itself. It has three spellings of the head of a request:

- `let₁ (op f a) k`: bind the reply, as the case trees do;
- `let₂ (op f a) t`: destructure the reply as a pair, when it has one tag
  whose tuple has two or more atoms;
- `case (op f a) l r`: case on the reply, when it has two or more tags.

After the head, the rest of the reply is in a bound slot and is consumed as
in the case trees: remaining tags are cased on in order and tuples are
unpacked in order. Bodies may contain further requests in any of the three
spellings. Leaves are those of the case trees.

A pending tuple may instead be held, which starts a chain over a stack of
packed tuples. Each tuple of the stack is one slot of the context, and the
stack has any depth. A chain asks a request and binds its reply, which is
pushed on the stack; destructures the newest tuple of the stack by one
pattern let; selects any packed tuple as the one the next pattern let
opens; drops a newest tuple with at most one atom; or, with the stack
empty, continues with any spelled tree. A reply with several tags is
cased on right after its request, and each arm pushes its payload and
continues its own chain. A packed tuple of two or more atoms is not an
atom slot, so no request uses it or its components before they are
destructured.

The inspection of a reply with several tags may be delayed across one later
request, which cannot read the stored reply. The case then directly follows
the later request. It may also be delayed across a finite prefix of
requests and pattern lets, given by its shape and its two specializations.

The normal form unpacks every tuple right after the request or the case
that binds it, and keeps every request in place. A case that directly
follows its request stays in place. A delayed case moves in front of the
one later request, which is then written in each arm.

The normal form of a spelled tree is the case tree with the same requests
in the same order, the same exits and the same payloads. Every slot of the
spelled tree is renamed past the reply slots that the normal form binds.

A direct case tree is the spelled tree of a binary signature in which
every request is cased on directly. A binary signature has two tags of
one atom each.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

/-- The slots under one new slot, past a reply slot bound beneath it: the
new slot stays newest and every older slot moves past the reply slot. -/
def armRenaming {α : Type} {n m : Nat} {β : BoundCtx (Ty α) n} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) (reply payload : Ty α) :
    BoundCtx.Renaming (β.snoc payload) ((γ.snoc reply).snoc payload) :=
  (ρ.comp (BoundCtx.Renaming.succ γ reply)).up payload

/-! ## Actions on terms that commute with a pattern let -/

section Frame

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- An action on terms over a telescope that preserves typing and moves a
pattern let on an older pair slot from its body to its front. -/
structure PairFrame (C : Ty α) {m : Nat} (Ω : BoundCtx (Ty α) m) (tel : List (Ty α))
    (term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k) : Prop where
  /-- The action preserves typing. -/
  typed : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel)},
    LetCase.LocallyNameless.HasType Φ Γ₀ (extendCtx Ω' tel) u C → LetCase.LocallyNameless.HasType Φ Γ₀ Ω' (term ω u) C
  /-- A pattern let on an older pair slot moves in front of the action. -/
  comm : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω') (j : Fin k) {A B : Ty α},
    Ω'.get j = .product A B → ∀ {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel + 1 + 1)},
    LetCase.LocallyNameless.HasType Φ Γ₀ (((extendCtx Ω' tel).snoc A).snoc B) body C →
    Equiv false Γ₀ Ω' (term ω (.let₂ (.bv ((weakenTele Ω' tel).toFun j)) body))
      (.let₂ (.bv j) (term (ω.comp (pastPair Ω' A B)) (body.rename (pairPastTele Ω' tel A B).toFun))) C

end Frame

/-! ## The equation for binding under a pending tuple -/

section Push

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-- The native account of a way to bind a telescope, by an action on
terms. The term of a bound body is the action on the term of the body, and
the action moves a pattern let on an older pair slot from its body to its
front:

`term ω (let₂ x B) = let₂ x (term ω↑↑ B′)`

where `ω↑↑` is `ω` weakened past the two components and `B′` is `B` with
the two components moved beneath the telescope. -/
structure CaseTree.Wrap.Framed {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    (wrap : CaseTree.Wrap Φ L Ω tel)
    (term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k) : Prop where
  /-- The term of the bound body is the action on the term of the body. -/
  spec : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel)} (r : CaseTree .body (extendCtx Ω' tel) L u),
    (wrap ω r).1 = term ω u
  /-- A pattern let on an older pair slot moves in front of the binding. -/
  comm : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω') (j : Fin k) {A B : Ty α},
    Ω'.get j = .product A B → ∀ {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel + 1 + 1)},
    LetCase.LocallyNameless.HasType Φ Γ₀ (((extendCtx Ω' tel).snoc A).snoc B) body (packedExitType L) →
    Equiv false Γ₀ Ω' (term ω (.let₂ (.bv ((weakenTele Ω' tel).toFun j)) body))
      (.let₂ (.bv j) (term (ω.comp (pastPair Ω' A B)) (body.rename (pairPastTele Ω' tel A B).toFun)))
      (packedExitType L)

/-- Binding a telescope in front of a pending tuple is natively equal to
binding it under the full unpacking of the tuple. -/
def CaseTree.PushedSpec : (pending : Pending α) → {n : Nat} → (β : BoundCtx (Ty α) n) →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → Prop
  | .body, _, _, _, _ => True
  | .tags _, _, _, _, _ => True
  | .tuple _, _, .nil, _, _ => True
  | .tuple _, _, .snoc Ξ T, t, tree =>
    ∀ {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)} (π : BoundCtx.Renaming Ξ (extendCtx Ω tel))
      (wrap : CaseTree.Wrap Φ L Ω tel)
      (term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
        LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k),
      wrap.Framed term →
      Equiv false Γ₀ (Ω.snoc T)
        (term (BoundCtx.Renaming.succ Ω T) (t.rename ((π.up T).comp (swapTele Ω tel T)).toFun))
        (CaseTree.pushed tree π wrap).1 (packedExitType L)

/-- The native typing of a renamed term. -/
def renameTyping : {n m : Nat} → {β : BoundCtx (Ty α) n} → {γ : BoundCtx (Ty α) m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → {A : Ty α} → (ρ : BoundCtx.Renaming β γ) → Derivation Φ Γ₀ β t A →
    Derivation Φ Γ₀ γ (t.rename ρ.toFun) A
  | _, _, _, _, _, _, _, .fv h => .fv h
  | _, _, _, γ, _, _, ρ, .bv (ι := ι) => cast (congrArg (Derivation Φ Γ₀ γ (.bv (ρ.toFun ι))) (ρ.typed ι)) .bv
  | _, _, _, _, _, _, ρ, .op ha => .op (renameTyping ρ ha)
  | _, _, _, _, _, _, ρ, .let₁ ha hb => .let₁ (renameTyping ρ ha) (renameTyping (ρ.up _) hb)
  | _, _, _, _, _, _, _, .unit => .unit
  | _, _, _, _, _, _, ρ, .pair ha hb => .pair (renameTyping ρ ha) (renameTyping ρ hb)
  | _, _, _, _, _, _, ρ, .let₂ ha hc => .let₂ (renameTyping ρ ha) (renameTyping ((ρ.up _).up _) hc)
  | _, _, _, _, _, _, ρ, .inl ha => .inl (renameTyping ρ ha)
  | _, _, _, _, _, _, ρ, .inr hb => .inr (renameTyping ρ hb)
  | _, _, _, _, _, _, ρ, .case he hl hr =>
    .case (renameTyping ρ he) (renameTyping (ρ.up _) hl) (renameTyping (ρ.up _) hr)
  | _, _, _, _, _, _, ρ, .abort ha => .abort (renameTyping ρ ha)

omit [TaggedSignature α Φ] in
/-- Exchanging two slots twice is the identity. -/
theorem swap_swap_rename {k : Nat} (Γ : BoundCtx (Ty α) k) (X Z : Ty α) (x : LetCase.LocallyNameless.Tm Empty Φ (k + 2)) :
    (x.rename (swapRenaming Γ X Z).toFun).rename (swapRenaming Γ Z X).toFun = x :=
  ((LetCase.LocallyNameless.Tm.rename_comp _ _ x).trans
    (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i) i) x)).trans
    (LetCase.LocallyNameless.Tm.rename_id x)

omit [TaggedSignature α Φ] in
/-- Moving the newest slot beneath two slots and back is the identity. -/
theorem before_after_rename {k : Nat} (x : LetCase.LocallyNameless.Tm Empty Φ (k + 3)) :
    (x.rename beforePair).rename afterPair = x :=
  ((LetCase.LocallyNameless.Tm.rename_comp _ _ x).trans
    (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun i => Fin.cases rfl
      (fun i => Fin.cases rfl (fun _ => rfl) i) i) i) x)).trans (LetCase.LocallyNameless.Tm.rename_id x)

/-- A finite prefix in front of a case on a stored slot of sum type, with
its two specializations. The term `t` runs the prefix and then cases on the
slot `s`, of type `X + Y`. The terms `l` and `r` are the specializations to
the two tags: the same prefix, weakened past the payload, followed by the
arm of that tag with the payload beneath the slots of the prefix.

A step of the prefix asks a request and binds its reply, or destructures
a slot of pair type, or cases on a slot of sum type. A request is assembled
from the atom slots of the context in which `s` has sum type. So it may use
older captures and the atoms of earlier replies of the prefix, and neither
the stored slot nor its payload; and it is the same request in both
specializations.

With `split` the prefix is a tree: it cases on a slot `y` of sum type and
continues with a prefix of its own in each arm, each ending in its own
case on `s` with its own arms. The arms of `y` are not joined, and nothing
is shared between them. In the specializations the case on `y` is kept,
under the payload, and each of its arms is the specialization of that
arm. -/
inductive Deferred (X Y : Ty α) : {k : Nat} → (Γ : BoundCtx (Ty α) k) → Fin k →
    LetCase.LocallyNameless.Tm Empty Φ k → LetCase.LocallyNameless.Tm Empty Φ (k + 1) → LetCase.LocallyNameless.Tm Empty Φ (k + 1) → Type where
  | here {k : Nat} {Γ : BoundCtx (Ty α) k} {s : Fin k} (hs : Γ.get s = .coprod X Y)
      (l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)) : Deferred X Y Γ s (.case (.bv s) l r) l r
  | ask {k : Nat} {Γ : BoundCtx (Ty α) k} {s : Fin k} (g : Φ) (argument : Assembly Γ (instrSrc g))
      {t : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1)}
      (rest : Deferred X Y (Γ.snoc (tagsTy (replyTags g))) s.succ t l r) :
      Deferred X Y Γ s (.let₁ (.op g (argTerm argument)) t)
        (.let₁ (.op g (argTerm (argument.rename (BoundCtx.Renaming.succ Γ X))))
          (l.rename (swapRenaming Γ (tagsTy (replyTags g)) X).toFun))
        (.let₁ (.op g (argTerm (argument.rename (BoundCtx.Renaming.succ Γ Y))))
          (r.rename (swapRenaming Γ (tagsTy (replyTags g)) Y).toFun))
  | unpack {k : Nat} {Γ : BoundCtx (Ty α) k} {s : Fin k} {A B : Ty α} (x : Slot Γ (.product A B))
      {t : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1)} {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1 + 1)}
      (rest : Deferred X Y ((Γ.snoc A).snoc B) s.succ.succ t l r) :
      Deferred X Y Γ s (.let₂ (.bv x.1) t) (.let₂ (.bv x.1.succ) (l.rename beforePair))
        (.let₂ (.bv x.1.succ) (r.rename beforePair))
  | split {k : Nat} {Γ : BoundCtx (Ty α) k} {s : Fin k} {A B : Ty α} (y : Slot Γ (.coprod A B))
      {t₁ t₂ : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} {l₁ r₁ l₂ r₂ : LetCase.LocallyNameless.Tm Empty Φ (k + 1 + 1)}
      (left : Deferred X Y (Γ.snoc A) s.succ t₁ l₁ r₁) (right : Deferred X Y (Γ.snoc B) s.succ t₂ l₂ r₂) :
      Deferred X Y Γ s (.case (.bv y.1) t₁ t₂)
        (.case (.bv y.1.succ) (l₁.rename (swapRenaming Γ A X).toFun) (l₂.rename (swapRenaming Γ B X).toFun))
        (.case (.bv y.1.succ) (r₁.rename (swapRenaming Γ A Y).toFun) (r₂.rename (swapRenaming Γ B Y).toFun))

/-- The stored slot of a prefix has sum type. -/
theorem Deferred.slot {X Y : Ty α} : {k : Nat} → {Γ : BoundCtx (Ty α) k} → {s : Fin k} →
    {t : LetCase.LocallyNameless.Tm Empty Φ k} → {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} → Deferred X Y Γ s t l r → Γ.get s = .coprod X Y
  | _, _, _, _, _, _, .here hs _ _ => hs
  | _, _, _, _, _, _, .ask _ _ rest => rest.slot
  | _, _, _, _, _, _, .unpack _ rest => rest.slot
  | _, _, _, _, _, _, .split _ left _ => left.slot

/-- The parts of the typing of a let. -/
def letTypingInv {k : Nat} {β : BoundCtx (Ty α) k} {a : LetCase.LocallyNameless.Tm Empty Φ k} {b : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} {C : Ty α} :
    Derivation Φ Γ₀ β (.let₁ a b) C → (A : Ty α) × Derivation Φ Γ₀ β a A × Derivation Φ Γ₀ (β.snoc A) b C
  | .let₁ ha hb => ⟨_, ha, hb⟩

/-- The parts of the typing of a pattern let. -/
def pairTypingInv {k : Nat} {β : BoundCtx (Ty α) k} {a : LetCase.LocallyNameless.Tm Empty Φ k} {c : LetCase.LocallyNameless.Tm Empty Φ (k + 2)} {C : Ty α} :
    Derivation Φ Γ₀ β (.let₂ a c) C →
      (A : Ty α) × (B : Ty α) × Derivation Φ Γ₀ β a (.product A B) × Derivation Φ Γ₀ ((β.snoc A).snoc B) c C
  | .let₂ ha hc => ⟨_, _, ha, hc⟩

/-- The parts of the typing of a case. -/
def caseTypingInv {k : Nat} {β : BoundCtx (Ty α) k} {a : LetCase.LocallyNameless.Tm Empty Φ k} {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} {C : Ty α} :
    Derivation Φ Γ₀ β (.case a l r) C →
      (A : Ty α) × (B : Ty α) × Derivation Φ Γ₀ β a (.coprod A B) × Derivation Φ Γ₀ (β.snoc A) l C ×
        Derivation Φ Γ₀ (β.snoc B) r C
  | .case ha hl hr => ⟨_, _, ha, hl, hr⟩

/-- A request is typed at its reply type. -/
theorem opTypingType {k : Nat} {β : BoundCtx (Ty α) k} {g : Φ} {a : LetCase.LocallyNameless.Tm Empty Φ k} {A : Ty α} :
    Derivation Φ Γ₀ β (.op g a) A → A = tagsTy (replyTags g)
  | .op _ => rfl

/-- A slot is typed at its type in the context. -/
theorem bvTypingType {k : Nat} {β : BoundCtx (Ty α) k} {i : Fin k} {A : Ty α} :
    Derivation Φ Γ₀ β (.bv i) A → A = β.get i
  | .bv => rfl

/-- The native typing of a prefix followed by its case, from the typings of
its two specializations. -/
def Deferred.typing {X Y C : Ty α} : {k : Nat} → {Γ : BoundCtx (Ty α) k} → {s : Fin k} →
    {t : LetCase.LocallyNameless.Tm Empty Φ k} → {l r : LetCase.LocallyNameless.Tm Empty Φ (k + 1)} → Deferred X Y Γ s t l r →
    Derivation Φ Γ₀ (Γ.snoc X) l C → Derivation Φ Γ₀ (Γ.snoc Y) r C → Derivation Φ Γ₀ Γ t C
  | _, _, s, _, _, _, .here hs _ _, dl, dr => .case (slotTyping ⟨s, hs⟩) dl dr
  | _, Γ, _, _, _, _, .ask (l := l) (r := r) g argument rest, dl, dr =>
    let pl := letTypingInv dl
    let pr := letTypingInv dr
    .let₁ (.op (f := g) (argTyping argument))
      (rest.typing
        (cast (congrArg (fun u => Derivation Φ Γ₀ ((Γ.snoc (tagsTy (replyTags g))).snoc X) u C)
            (swap_swap_rename Γ (tagsTy (replyTags g)) X l))
          (renameTyping (swapRenaming Γ X (tagsTy (replyTags g)))
            (cast (congrArg (fun A => Derivation Φ Γ₀ ((Γ.snoc X).snoc A) _ C) (opTypingType pl.2.1)) pl.2.2)))
        (cast (congrArg (fun u => Derivation Φ Γ₀ ((Γ.snoc (tagsTy (replyTags g))).snoc Y) u C)
            (swap_swap_rename Γ (tagsTy (replyTags g)) Y r))
          (renameTyping (swapRenaming Γ Y (tagsTy (replyTags g)))
            (cast (congrArg (fun A => Derivation Φ Γ₀ ((Γ.snoc Y).snoc A) _ C) (opTypingType pr.2.1)) pr.2.2))))
  | _, Γ, _, _, _, _, .unpack (A := A) (B := B) (l := l) (r := r) x rest, dl, dr =>
    let pl := pairTypingInv dl
    let pr := pairTypingInv dr
    have el : Ty.product pl.1 pl.2.1 = Ty.product A B := (bvTypingType pl.2.2.1).trans x.2
    have er : Ty.product pr.1 pr.2.1 = Ty.product A B := (bvTypingType pr.2.2.1).trans x.2
    .let₂ (slotTyping x)
      (rest.typing
        (cast (congrArg (fun u => Derivation Φ Γ₀ (((Γ.snoc A).snoc B).snoc X) u C) (before_after_rename l))
          (renameTyping (afterPairRenaming Γ X A B)
            (cast (congrArg₂ (fun a b => Derivation Φ Γ₀ (((Γ.snoc X).snoc a).snoc b) _ C)
              (Ty.product.inj el).1 (Ty.product.inj el).2) pl.2.2.2)))
        (cast (congrArg (fun u => Derivation Φ Γ₀ (((Γ.snoc A).snoc B).snoc Y) u C) (before_after_rename r))
          (renameTyping (afterPairRenaming Γ Y A B)
            (cast (congrArg₂ (fun a b => Derivation Φ Γ₀ (((Γ.snoc Y).snoc a).snoc b) _ C)
              (Ty.product.inj er).1 (Ty.product.inj er).2) pr.2.2.2))))
  | _, Γ, _, _, _, _, .split (A := A) (B := B) (l₁ := l₁) (r₁ := r₁) (l₂ := l₂) (r₂ := r₂) y left right, dl, dr =>
    let pl := caseTypingInv dl
    let pr := caseTypingInv dr
    have el : Ty.coprod pl.1 pl.2.1 = Ty.coprod A B := (bvTypingType pl.2.2.1).trans y.2
    have er : Ty.coprod pr.1 pr.2.1 = Ty.coprod A B := (bvTypingType pr.2.2.1).trans y.2
    .case (slotTyping y)
      (left.typing
        (cast (congrArg (fun u => Derivation Φ Γ₀ ((Γ.snoc A).snoc X) u C) (swap_swap_rename Γ A X l₁))
          (renameTyping (swapRenaming Γ X A)
            (cast (congrArg (fun a => Derivation Φ Γ₀ ((Γ.snoc X).snoc a) _ C) (Ty.coprod.inj el).1)
              pl.2.2.2.1)))
        (cast (congrArg (fun u => Derivation Φ Γ₀ ((Γ.snoc A).snoc Y) u C) (swap_swap_rename Γ A Y r₁))
          (renameTyping (swapRenaming Γ Y A)
            (cast (congrArg (fun a => Derivation Φ Γ₀ ((Γ.snoc Y).snoc a) _ C) (Ty.coprod.inj er).1)
              pr.2.2.2.1))))
      (right.typing
        (cast (congrArg (fun u => Derivation Φ Γ₀ ((Γ.snoc B).snoc X) u C) (swap_swap_rename Γ B X l₂))
          (renameTyping (swapRenaming Γ X B)
            (cast (congrArg (fun a => Derivation Φ Γ₀ ((Γ.snoc X).snoc a) _ C) (Ty.coprod.inj el).2)
              pl.2.2.2.2)))
        (cast (congrArg (fun u => Derivation Φ Γ₀ ((Γ.snoc B).snoc Y) u C) (swap_swap_rename Γ B Y r₂))
          (renameTyping (swapRenaming Γ Y B)
            (cast (congrArg (fun a => Derivation Φ Γ₀ ((Γ.snoc Y).snoc a) _ C) (Ty.coprod.inj er).2)
              pr.2.2.2.2))))

/-- The native typing of the pattern lets that unpack a tuple slot. -/
def unpackTyping : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (s : Slot Γ (tupleTy atoms)) →
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))} → {C : Ty α} →
    Derivation Φ Γ₀ (extendCtx Γ (pairsTele atoms)) u C → Derivation Φ Γ₀ Γ (unpackAt atoms s.1 u) C
  | [], _, _, _, _, _, d => d
  | [_], _, _, _, _, _, d => d
  | _ :: d :: more, _, _, s, _, _, h => .let₂ (slotTyping s) (unpackTyping (d :: more) ⟨0, rfl⟩ h)

end Push

/-! ## Spelled trees -/

section Spelled

variable {α Φ : Type} [TaggedSignature α Φ]

mutual

/-- A spelled tree in body position: a leaf, or a request followed by one
of the head spellings, or a chain over the empty stack. -/
inductive Spelled : {n : Nat} → BoundCtx (Ty α) n → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : Spelled β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {t : LetCase.LocallyNameless.Tm Empty Φ n}
      (head : SpelledHead (replyTags f) (.op f (argTerm argument)) β L t) : Spelled β L t
  | chain {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ n}
      (c : SpelledStack [] β .nil L t) : Spelled β L t

/-- The head of a request, consuming the request term itself. It binds the
reply; or destructures a one-tag reply of two or more atoms as a pair; or
cases on a reply of two or more tags. -/
inductive SpelledHead : {n : Nat} → List (List α) → LetCase.LocallyNameless.Tm Empty Φ n →
    BoundCtx (Ty α) n → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | bind {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {tags : List (List α)}
      {e : LetCase.LocallyNameless.Tm Empty Φ n} {k : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (reply : SpelledTags tags β L k) : SpelledHead tags e β L (.let₁ e k)
  | destruct {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a b : α) (rest : List α)
      {e : LetCase.LocallyNameless.Tm Empty Φ n} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
      (later : SpelledTuple (b :: rest) (β.snoc (.base a)) L t) :
      SpelledHead [a :: b :: rest] e β L (.let₂ e t)
  | branch {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms next : List α) (rest : List (List α))
      {e : LetCase.LocallyNameless.Tm Empty Φ n} {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : SpelledTuple atoms β L l) (right : SpelledTags (next :: rest) β L r) :
      SpelledHead (atoms :: next :: rest) e β L (.case e l r)

/-- A reply pending at the newest slot, over the base context. One tag is
its tuple; more tags are cased on in order. -/
inductive SpelledTags : {n : Nat} → List (List α) → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ (n + 1) → Type where
  | only {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (payload : SpelledTuple atoms β L t) : SpelledTags [atoms] β L t
  | split {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms next : List α) (rest : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
      (left : SpelledTuple atoms (β.snoc (tagsTy (atoms :: next :: rest))) L l)
      (right : SpelledTags (next :: rest) (β.snoc (tagsTy (atoms :: next :: rest))) L r) :
      SpelledTags (atoms :: next :: rest) β L (.case (.bv 0) l r)

/-- A tuple pending at the newest slot, over the base context. It is
unpacked in order and continues with a body. A tuple of two or more atoms
may instead be held across a chain of requests. -/
inductive SpelledTuple : {n : Nat} → List α → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ (n + 1) → Type where
  | unit {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : Spelled (β.snoc (tupleTy ([] : List α))) L t) : SpelledTuple [] β L t
  | atom {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a : α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : Spelled (β.snoc (tupleTy [a])) L t) : SpelledTuple [a] β L t
  | pair {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a b : α) (rest : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1 + 1)}
      (later : SpelledTuple (b :: rest) ((β.snoc (tupleTy (a :: b :: rest))).snoc (.base a)) L t) :
      SpelledTuple (a :: b :: rest) β L (.let₂ (.bv 0) t)
  | hold {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (chain : SpelledStack [atoms] (β.snoc (tupleTy atoms)) (.cons ⟨0, rfl⟩ .nil) L t) :
      SpelledTuple atoms β L t

/-- A chain over a stack of packed tuples. Each tuple of the stack is one
slot of the context. The stack is indexed by the atoms of its tuples,
newest first, and has any depth.

- `ask` asks a request and binds its reply. The argument is assembled from
  the atom slots in scope. A packed tuple of two or more atoms is not an
  atom slot, so no request uses it or its components.
- `step` destructures the newest tuple by one pattern let, into its first
  atom and the rest. The rest is the newest tuple of the stack again.
- `unit` and `atom` drop a newest tuple with no atom or one atom. It needs
  no pattern let, and with one atom its slot is an atom slot.
- `done` continues with any spelled tree when the stack is empty.
- `pick` selects any tuple of the stack and moves it to the top. The term
  is unchanged. The next `step`, `unit` or `atom` acts on the selected
  tuple, and the other tuples stay packed in their order.

The reply of a request is pushed on the stack by `SpelledStackTags`, so
unpacking it at once is `step`s right after the request, and keeping it
packed is asking further requests first. Tuples are opened in any order. -/
inductive SpelledStack : (stack : List (List α)) → {m : Nat} → (Δ : BoundCtx (Ty α) m) → Holds Δ stack →
    List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ m → Type where
  | done {m : Nat} {Δ : BoundCtx (Ty α) m} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (body : Spelled Δ L t) :
      SpelledStack [] Δ .nil L t
  | unit {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy ([] : List α))}
      {older : Holds Δ stack} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (next : SpelledStack stack Δ older L t) :
      SpelledStack ([] :: stack) Δ (.cons top older) L t
  | atom {c : α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy [c])}
      {older : Holds Δ stack} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (next : SpelledStack stack Δ older L t) :
      SpelledStack ([c] :: stack) Δ (.cons top older) L t
  | step {a b : α} {rest : List α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {top : Slot Δ (tupleTy (a :: b :: rest))} {older : Holds Δ stack} {L : List (Ty α)}
      {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (next : SpelledStack ((b :: rest) :: stack) ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest)))
        (.cons ⟨0, rfl⟩ (older.rename (pastPair Δ (.base a) (tupleTy (b :: rest))))) L k) :
      SpelledStack ((a :: b :: rest) :: stack) Δ (.cons top older) L (.let₂ (.bv top.1) k)
  | ask {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {L : List (Ty α)}
      (g : Φ) (argument : Assembly Δ (instrSrc g)) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (reply : SpelledStackTags stack (replyTags g) Δ holds L k) :
      SpelledStack stack Δ holds L (.let₁ (.op g (argTerm argument)) k)
  | pick {stack : List (List α)} {atoms : List α} {rest : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {holds : Holds Δ stack} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (sel : Select stack atoms rest)
      (next : SpelledStack (atoms :: rest) Δ (holds.select sel) L t) : SpelledStack stack Δ holds L t

/-- The bound reply of a request of a chain over a stack, pending at the
newest slot. A reply with one tag is a tuple of atoms and is pushed on the
stack. A reply with more tags is cased on right after its request: the
payload of the first tag is pushed on the stack in its arm, and the other
arms case on the remaining tags. Each arm continues its own chain over the
older tuples, so the chain branches. With `later` the inspection of the
reply is delayed across one request, which is asked while the reply is one
slot. With `deferred` it is delayed across a finite prefix of requests and
pattern lets: the prefix is given by its shape, and the two specializations
of the tree to the tags are given as trees, with the equations between
their terms and the terms the shape determines. -/
inductive SpelledStackTags : (stack : List (List α)) → List (List α) → {m : Nat} → (Δ : BoundCtx (Ty α) m) →
    Holds Δ stack → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ (m + 1) → Type where
  | bind {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms : List α) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (next : SpelledStack (atoms :: stack) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)))) L k) :
      SpelledStackTags stack [atoms] Δ holds L k
  | split {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms next : List α) (more : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (left : SpelledStack (atoms :: stack)
        ((Δ.snoc (tagsTy (atoms :: next :: more))).snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))) L l)
      (right : SpelledStackTags stack (next :: more) (Δ.snoc (tagsTy (atoms :: next :: more)))
        (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: next :: more)))) L r) :
      SpelledStackTags stack (atoms :: next :: more) Δ holds L (.case (.bv 0) l r)
  | later {stack : List (List α)} {tags : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {holds : Holds Δ stack} {L : List (Ty α)} (h : Φ)
      (argument : Assembly (Δ.snoc (tagsTy tags)) (instrSrc h)) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (arms : SpelledLaterTags stack tags h Δ holds L k) :
      SpelledStackTags stack tags Δ holds L (.let₁ (.op h (argTerm argument)) k)
  | deferred {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms next : List α) (more : List (List α))
      {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} {l r l' r' : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (shape : Deferred (tupleTy atoms) (tagsTy (next :: more))
        (Δ.snoc (tagsTy (atoms :: next :: more))) 0 t l r)
      (left : SpelledStack (atoms :: stack)
        ((Δ.snoc (tagsTy (atoms :: next :: more))).snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))) L l')
      (right : SpelledStackTags stack (next :: more) (Δ.snoc (tagsTy (atoms :: next :: more)))
        (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: next :: more)))) L r')
      (hl : l' = l) (hr : r' = r) :
      SpelledStackTags stack (atoms :: next :: more) Δ holds L t

/-- A reply whose inspection is delayed across one later request. The
reply is one slot, beneath the reply of the later request `h`, which is the
newest slot. The term cases on the stored reply right after `h`:
`case (bv 1) l r`. A stored reply with several tags is a slot of sum type
and not an atom slot, so `h` cannot read it: `h` is the same request
whichever tag the stored reply carries. In each arm the payload of the tag
is pushed on the stack and the reply of `h` is pending, so each arm
continues as the bound reply of `h` does. The arms are given with the reply
of `h` newest, and the term has them with the payload newest. -/
inductive SpelledLaterTags : (stack : List (List α)) → List (List α) → Φ → {m : Nat} →
    (Δ : BoundCtx (Ty α) m) → Holds Δ stack → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1) → Type where
  | only {stack : List (List α)} {h : Φ} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms : List α) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (next : SpelledStackTags (atoms :: stack) (replyTags h) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)))) L k) :
      SpelledLaterTags stack [atoms] h Δ holds L k
  | split {stack : List (List α)} {h : Φ} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms next : List α) (more : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1 + 1)}
      (left : SpelledStackTags (atoms :: stack) (replyTags h)
        ((Δ.snoc (tagsTy (atoms :: next :: more))).snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))) L l)
      (right : SpelledLaterTags stack (next :: more) h (Δ.snoc (tagsTy (atoms :: next :: more)))
        (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: next :: more)))) L r) :
      SpelledLaterTags stack (atoms :: next :: more) h Δ holds L
        (.case (.bv 1)
          (l.rename (swapRenaming (Δ.snoc (tagsTy (atoms :: next :: more))) (tupleTy atoms)
            (tagsTy (replyTags h))).toFun)
          (r.rename (swapRenaming (Δ.snoc (tagsTy (atoms :: next :: more))) (tagsTy (next :: more))
            (tagsTy (replyTags h))).toFun))

end

variable {L : List (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}

mutual

/-- The native typing of a spelled tree at the packed sum of its ordered
exits. -/
def Spelled.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    Spelled β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, .ask f argument head => head.typing (.op (f := f) (argTyping argument))
  | _, _, _, .chain c => c.typing

/-- The native typing of a head, from the typing of the request it
consumes. -/
def SpelledHead.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → SpelledHead tags e β L t →
    Derivation Φ Γ₀ β e (tagsTy tags) → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, _, _, .bind reply, d => .let₁ d reply.typing
  | _, _, _, _, _, .destruct _ _ _ later, d => .let₂ d later.typing
  | _, _, _, _, _, .branch _ _ _ left right, d => .case d left.typing right.typing

/-- The native typing of a pending reply, under its slot. -/
def SpelledTags.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTags tags β L t →
    Derivation Φ Γ₀ (β.snoc (tagsTy tags)) t (packedExitType L)
  | _, _, _, _, .only _ payload => payload.typing
  | _, _, _, _, .split _ _ _ left right => .case .bv left.typing right.typing

/-- The native typing of a pending tuple, under its slot. -/
def SpelledTuple.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTuple atoms β L t →
    Derivation Φ Γ₀ (β.snoc (tupleTy atoms)) t (packedExitType L)
  | _, _, _, _, .unit body => body.typing
  | _, _, _, _, .atom _ body => body.typing
  | _, _, _, _, .pair _ _ _ later => .let₂ .bv later.typing
  | _, _, _, _, .hold _ chain => chain.typing

/-- The native typing of a chain over a stack of packed tuples. -/
def SpelledStack.typing : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledStack stack Δ holds L t →
    Derivation Φ Γ₀ Δ t (packedExitType L)
  | _, _, _, _, _, .done body => body.typing
  | _, _, _, _, _, .unit next => next.typing
  | _, _, _, _, _, .atom next => next.typing
  | _, _, _, .cons top _, _, .step next => .let₂ (slotTyping top) next.typing
  | _, _, _, _, _, .ask g argument reply => .let₁ (.op (f := g) (argTyping argument)) reply.typing
  | _, _, _, _, _, .pick _ next => next.typing

/-- The native typing of the bound reply of a request of such a chain,
under its slot. -/
def SpelledStackTags.typing : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledStackTags stack tags Δ holds L t → Derivation Φ Γ₀ (Δ.snoc (tagsTy tags)) t (packedExitType L)
  | _, _, _, _, _, _, .bind _ next => next.typing
  | _, _, _, _, _, _, .split _ _ _ left right => .case .bv left.typing right.typing
  | _, _, _, _, _, _, .later h argument arms => .let₁ (.op (f := h) (argTyping argument)) arms.typing
  | _, _, _, _, _, _, .deferred atoms next more shape left right hl hr =>
    shape.typing
      (cast (congrArg (fun u => Derivation Φ Γ₀ (_ : BoundCtx (Ty α) _) u (packedExitType L)) hl) left.typing)
      (cast (congrArg (fun u => Derivation Φ Γ₀ (_ : BoundCtx (Ty α) _) u (packedExitType L)) hr) right.typing)

/-- The native typing of a reply inspected after one later request, under
the slot of the reply and the slot of the reply of the later request. -/
def SpelledLaterTags.typing : {stack : List (List α)} → {tags : List (List α)} → {h : Φ} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)} →
    SpelledLaterTags stack tags h Δ holds L t →
    Derivation Φ Γ₀ ((Δ.snoc (tagsTy tags)).snoc (tagsTy (replyTags h))) t (packedExitType L)
  | _, _, _, _, _, _, _, .only _ next => next.typing
  | _, _, h, _, Δ, _, _, .split atoms nxt more left right =>
    .case (slotTyping (β := (Δ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tagsTy (replyTags h))) ⟨1, rfl⟩)
      (renameTyping (swapRenaming (Δ.snoc (tagsTy (atoms :: nxt :: more))) (tupleTy atoms)
        (tagsTy (replyTags h))) left.typing)
      (renameTyping (swapRenaming (Δ.snoc (tagsTy (atoms :: nxt :: more))) (tagsTy (nxt :: more))
        (tagsTy (replyTags h))) right.typing)

end

mutual

/-- The normal form of a spelled tree, along a renaming of its slots. A
leaf keeps its exit and renames its payload. A request keeps its primitive
and renames its argument, binds the reply, and continues with the normal
form of its head. -/
def Spelled.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    Spelled β L t → {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ m) × CaseTree .body γ L u
  | _, _, _, .ret exit payload, _, _, ρ => ⟨_, .ret exit (payload.rename ρ)⟩
  | _, _, _, .ask f argument head, _, _, ρ => ⟨_, .ask f (argument.rename ρ) (head.normal ρ).2⟩
  | _, _, _, .chain c, _, _, ρ => c.opened ρ

/-- The normal form of a head: the case tree that consumes the bound
reply. A bound head is already of that form. A pair head becomes the
unpacking of the bound pair, and a case head the case on the bound reply,
with every older slot moved past the reply slot. -/
def SpelledHead.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → SpelledHead tags e β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tags tags) (γ.snoc (tagsTy tags)) L k
  | _, _, _, _, _, .bind reply, _, _, ρ => reply.normal ρ
  | _, _, _, _, _, .destruct a b rest later, _, _, ρ =>
    ⟨_, .only (a :: b :: rest) (.pair a b rest (later.normal (armRenaming ρ _ _)).2)⟩
  | _, _, _, _, _, .branch atoms next rest left right, _, γ, ρ =>
    ⟨_, .split atoms next rest
      (left.normal (ρ.comp (BoundCtx.Renaming.succ γ _))).2
      (right.normal (ρ.comp (BoundCtx.Renaming.succ γ _))).2⟩

/-- The normal form of a pending reply. The renaming is of the base
context and the pending slot stays newest. -/
def SpelledTags.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTags tags β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tags tags) (γ.snoc (tagsTy tags)) L u
  | _, _, _, _, .only atoms payload, _, _, ρ => ⟨_, .only atoms (payload.normal ρ).2⟩
  | _, _, _, _, .split atoms next rest left right, _, _, ρ =>
    ⟨_, .split atoms next rest (left.normal (ρ.up _)).2 (right.normal (ρ.up _)).2⟩

/-- The normal form of a pending tuple. The renaming is of the base
context and the pending slot stays newest. -/
def SpelledTuple.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTuple atoms β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tuple atoms) (γ.snoc (tupleTy atoms)) L u
  | _, _, _, _, .unit body, _, _, ρ => ⟨_, .unit (body.normal (ρ.up _)).2⟩
  | _, _, _, _, .atom a body, _, _, ρ => ⟨_, .atom a (body.normal (ρ.up _)).2⟩
  | _, _, _, _, .pair a b rest later, _, _, ρ =>
    ⟨_, .pair a b rest (later.normal ((ρ.up _).up _)).2⟩
  | _, _, _, _, .hold atoms chain, _, _, ρ =>
    ⟨_, CaseTree.packed atoms (chain.opened (ρ.up (tupleTy atoms))).2⟩

/-- The body of the normal form of a chain over a stack, under the full
unpacking of every tuple of the stack. The slots of the chain are placed
beneath the slots of those unpackings. Each request is asked there, in
order, and the case on a reply directly follows its request. -/
def SpelledStack.opened : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledStack stack Δ holds L t → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → BoundCtx.Renaming Δ Θ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack)) × CaseTree .body (stackCtx stack Θ) L u
  | _, _, _, _, _, .done body, _, _, ρ => body.normal ρ
  | _, _, _, _, _, .unit next, _, _, ρ => next.opened ρ
  | _, _, _, _, _, .atom next, _, _, ρ => next.opened ρ
  | (a :: b :: rest) :: stack, _, _, _, _, .step next, _, Θ, ρ =>
    CaseTree.renamed (pending := .body) (next.opened ((ρ.up (.base a)).up (tupleTy (b :: rest)))).2
      (upTele (swapStack stack Θ [.base a, tupleTy (b :: rest)]) (pairsTele (b :: rest)))
  | stack, _, _, _, _, .ask g argument reply, _, Θ, ρ =>
    ⟨_, .ask g (argument.rename (ρ.comp (weakenStack stack Θ))) (reply.opened ρ).2⟩
  | _, _, _, _, _, .pick sel next, _, Θ, ρ =>
    CaseTree.renamed (pending := .body) (next.opened ρ).2 (selectRen sel Θ)

/-- The normal form of the bound reply of a request of such a chain,
pending under the unpackings of the stack. The payload of a tag is
unpacked right after the reply, wherever its chain destructures it. -/
def SpelledStackTags.opened : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledStackTags stack tags Δ holds L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming Δ Θ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack + 1)) ×
      CaseTree (.tags tags) ((stackCtx stack Θ).snoc (tagsTy tags)) L u
  | stack, _, _, _, _, _, .bind atoms next, _, Θ, ρ =>
    ⟨_, .only atoms (CaseTree.packed atoms
      (CaseTree.renamed (pending := .body) (next.opened (ρ.up (tupleTy atoms))).2
        (upTele (swapStack stack Θ [tupleTy atoms]) (pairsTele atoms))).2)⟩
  | stack, _, _, _, _, _, .split atoms nxt more left right, _, Θ, ρ =>
    ⟨_, .split atoms nxt more
      (CaseTree.packed atoms
        (CaseTree.renamed (pending := .body)
          (left.opened ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))).2
          (upTele (swapStack stack Θ [tagsTy (atoms :: nxt :: more), tupleTy atoms]) (pairsTele atoms))).2)
      (CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (Θ.snoc (tagsTy (atoms :: nxt :: more)))).snoc (tagsTy (nxt :: more)))
        (right.opened (ρ.up (tagsTy (atoms :: nxt :: more)))).2
        (swapStack stack Θ [tagsTy (atoms :: nxt :: more)])).2⟩
  | _, tags, _, _, _, _, .later _ argument arms, _, _, ρ =>
    arms.opened ρ (argument.rename (ρ.up (tagsTy tags)))
  | stack, _, _, _, _, _, .deferred atoms nxt more _ left right _ _, _, Θ, ρ =>
    ⟨_, .split atoms nxt more
      (CaseTree.packed atoms
        (CaseTree.renamed (pending := .body)
          (left.opened ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))).2
          (upTele (swapStack stack Θ [tagsTy (atoms :: nxt :: more), tupleTy atoms]) (pairsTele atoms))).2)
      (CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (Θ.snoc (tagsTy (atoms :: nxt :: more)))).snoc (tagsTy (nxt :: more)))
        (right.opened (ρ.up (tagsTy (atoms :: nxt :: more)))).2
        (swapStack stack Θ [tagsTy (atoms :: nxt :: more)])).2⟩

/-- The normal form of a reply inspected after one later request `h`,
pending under the unpackings of the stack. The case on the reply comes
first. In the arm of each tag the payload is unpacked and then `h` is
asked, with the argument given over the base context and the reply slot.
So `h` occurs once in every arm, and once on every run. -/
def SpelledLaterTags.opened : {stack : List (List α)} → {tags : List (List α)} → {h : Φ} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)} →
    SpelledLaterTags stack tags h Δ holds L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming Δ Θ → Assembly (Θ.snoc (tagsTy tags)) (instrSrc h) →
    (u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack + 1)) ×
      CaseTree (.tags tags) ((stackCtx stack Θ).snoc (tagsTy tags)) L u
  | stack, _, h, _, _, _, _, .only atoms next, _, Θ, ρ, arg =>
    ⟨_, .only atoms (CaseTree.packed atoms (.ask h
      (arg.rename ((weakenStack (atoms :: stack) (Θ.snoc (tupleTy atoms))).comp
        (upTele (swapStack stack Θ [tupleTy atoms]) (pairsTele atoms))))
      (CaseTree.renamed (pending := .tags (replyTags h))
        (β := (stackCtx (atoms :: stack) (Θ.snoc (tupleTy atoms))).snoc (tagsTy (replyTags h)))
        (next.opened (ρ.up (tupleTy atoms))).2
        (upTele (swapStack stack Θ [tupleTy atoms]) (pairsTele atoms))).2))⟩
  | stack, _, h, _, _, _, _, .split atoms nxt more left right, _, Θ, ρ, arg =>
    ⟨_, .split atoms nxt more
      (CaseTree.packed atoms (.ask h
        (arg.rename (((BoundCtx.Renaming.succ (Θ.snoc (tagsTy (atoms :: nxt :: more))) (tupleTy atoms)).comp
          (weakenStack (atoms :: stack) ((Θ.snoc (tagsTy (atoms :: nxt :: more))).snoc (tupleTy atoms)))).comp
          (upTele (swapStack stack Θ [tagsTy (atoms :: nxt :: more), tupleTy atoms]) (pairsTele atoms))))
        (CaseTree.renamed (pending := .tags (replyTags h))
          (β := (stackCtx (atoms :: stack) ((Θ.snoc (tagsTy (atoms :: nxt :: more))).snoc
            (tupleTy atoms))).snoc (tagsTy (replyTags h)))
          (left.opened ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))).2
          (upTele (swapStack stack Θ [tagsTy (atoms :: nxt :: more), tupleTy atoms]) (pairsTele atoms))).2))
      (CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (Θ.snoc (tagsTy (atoms :: nxt :: more)))).snoc (tagsTy (nxt :: more)))
        (right.opened (ρ.up (tagsTy (atoms :: nxt :: more)))
          (arg.rename (BoundCtx.Renaming.succ (Θ.snoc (tagsTy (atoms :: nxt :: more)))
            (tagsTy (nxt :: more))))).2
        (swapStack stack Θ [tagsTy (atoms :: nxt :: more)])).2⟩

end

/-- A spelled tree has at least one exit. -/
theorem Spelled.exits_ne_nil {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : Spelled β L t) : L ≠ [] :=
  (tree.normal (.id β)).2.exits_ne_nil

/-- A spelled tree as a captured LetCase operand. -/
def Spelled.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : Spelled β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The checked graph that the readback builds from a spelled tree. Its
exits are the original ordered exits. -/
def Spelled.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : Spelled β L t) : CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

/-- The operand is natively equal to a spelled tree. -/
def SpelledOperand (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : Spelled β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

end Spelled

/-! ## Direct case trees of the binary signatures -/

/-- Every primitive takes an argument built from atoms, unit and ordered
products, and replies with one atom under the left or the right tag. -/
class BinarySignature (α Φ : Type) where
  argument : Φ → Shape α
  left : Φ → α
  right : Φ → α

namespace Binary

/-- A binary signature as a tagged signature: two tags of one atom each. -/
scoped instance {α Φ : Type} [BinarySignature α Φ] : TaggedSignature α Φ :=
  ⟨BinarySignature.argument, fun f => [BinarySignature.left f], fun f => [[BinarySignature.right f]]⟩

end Binary

open scoped Binary

variable {α Φ : Type} [BinarySignature α Φ]

/-- A direct case tree over ordered exits. A request node cases on the
request and binds the payload atom in each arm. A leaf returns a payload
assembled from the atom slots in scope, at one exit of its type. -/
inductive DirectTree : {n : Nat} → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : DirectTree β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : DirectTree (β.snoc (.base (BinarySignature.left f))) L l)
      (right : DirectTree (β.snoc (.base (BinarySignature.right f))) L r) :
      DirectTree β L (.case (.op f (argTerm argument)) l r)

variable {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-- The native typing of a direct case tree at the packed sum of its
ordered exits. -/
def DirectTree.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    DirectTree β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, .ask f argument left right => .case (.op (f := f) (argTyping argument)) left.typing right.typing

/-- A direct case tree has at least one exit. -/
theorem DirectTree.exits_ne_nil : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → DirectTree β L t → L ≠ []
  | _, _, _, .ret exit _ => by cases exit <;> exact List.cons_ne_nil _ _
  | _, _, _, .ask _ _ left _ => left.exits_ne_nil

/-- A direct case tree as a captured LetCase operand. -/
def DirectTree.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : DirectTree β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The checked graph that the readback builds from a direct case tree.
Its exits are the original ordered exits. -/
def DirectTree.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : DirectTree β L t) :
    CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

/-- The operand is natively equal to a direct case tree. -/
def Direct (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : DirectTree β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

/-- A direct case tree as a spelled tree: every request is cased on
directly, and each arm has its one atom. -/
def DirectTree.spelled : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    DirectTree β L t → Spelled β L t
  | _, _, _, .ret exit payload => .ret exit payload
  | _, _, _, .ask f argument left right =>
    .ask f argument
      (.branch [BinarySignature.left f] [BinarySignature.right f] []
        (.atom (BinarySignature.left f) left.spelled)
        (.only [BinarySignature.right f] (.atom (BinarySignature.right f) right.spelled)))

/-- The normal form of a direct case tree, along a renaming of its slots.
It is the normal form of its spelled tree. -/
def DirectTree.normal {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : DirectTree β L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    (u : LetCase.LocallyNameless.Tm Empty Φ m) × CaseTree .body γ L u :=
  tree.spelled.normal ρ

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
