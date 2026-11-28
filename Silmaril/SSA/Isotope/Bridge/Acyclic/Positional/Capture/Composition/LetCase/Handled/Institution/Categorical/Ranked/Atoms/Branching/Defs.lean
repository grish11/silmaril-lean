module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Thms

/-! # Case trees on tagged tuple replies

A tagged signature has primitives whose reply carries one of finitely many
ordered tags. Each tag has its own payload: an ordered tuple of atoms,
which may be empty and may differ from tag to tag. There is at least one
tag. The argument is built from atoms, unit and ordered products.

A case tree asks a primitive with an argument assembled from the atom
slots in scope and binds the reply. It then cases on the reply, tag by tag
in order, and in the arm of each tag unpacks the tuple of that tag into
atom slots, component by component in order. Each arm continues with a
case tree. The older slots stay in scope in every arm. The case chain and
the unpacking are forced by the reply type, so a tree has one shape.

The exits are an ordered list of types. A leaf returns a payload at one
exit of the type of the payload. The payload is assembled from the atom
slots in scope: an atom slot, the unit, or an ordered pair of payloads.
Two exits may have the same type.

An operand is branching when it is natively equal to a case tree. A
bound context is separable when some environment gives distinct tokens to
its atom slots of each sort.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Isotope.Semantics (BoundEnv)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly Separates)
open scoped LetSeq.StraightLine.Structural

/-- The type of an ordered tuple of atoms. The empty tuple is the unit and
a tuple of one atom is that atom. -/
def tupleTy {α : Type} : List α → Ty α
  | [] => .unit
  | [a] => .base a
  | a :: b :: rest => .product (.base a) (tupleTy (b :: rest))

/-- The type of a reply with ordered tags, each carrying a tuple of atoms.
One tag is its tuple. -/
def tagsTy {α : Type} : List (List α) → Ty α
  | [] => .empty
  | [as] => tupleTy as
  | as :: bs :: rest => .coprod (tupleTy as) (tagsTy (bs :: rest))

/-- Every primitive takes an argument built from atoms, unit and ordered
products. Its reply carries the first tag or one of the other tags, in
order, and each tag has its own tuple of atoms. -/
class TaggedSignature (α Φ : Type) where
  argument : Φ → Shape α
  first : Φ → List α
  others : Φ → List (List α)

/-- The ordered tags of the reply of a primitive. -/
abbrev replyTags {α Φ : Type} [TaggedSignature α Φ] (f : Φ) : List (List α) :=
  TaggedSignature.first f :: TaggedSignature.others f

namespace Tagged

scoped instance {α Φ : Type} [TaggedSignature α Φ] : HasTy Φ (Ty α) :=
  ⟨fun f => (TaggedSignature.argument f).ty, fun f => tagsTy (replyTags f)⟩

end Tagged

open scoped Tagged

variable {α Φ : Type}

/-- All slots are atoms. These are the older captures. -/
inductive AtomContext : {n : Nat} → BoundCtx (Ty α) n → Prop where
  | nil : AtomContext .nil
  | snoc {n : Nat} {β : BoundCtx (Ty α) n} (older : AtomContext β) (a : α) : AtomContext (β.snoc (.base a))

/-- Some environment gives distinct tokens below a bound to the atom slots
of each sort. -/
def Separable {n : Nat} (β : BoundCtx (Ty α) n) : Prop :=
  ∃ (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) (k : Nat), Separates ρ (Set.Iio k)

variable [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n}

/-- The native typing of a slot. -/
def slotTyping {A : Ty α} (s : Slot β A) : Derivation Φ Γ₀ β (.bv s.1) A :=
  cast (congrArg (Derivation Φ Γ₀ β (.bv s.1)) s.2) .bv

/-- An assembled argument as a LetCase term. -/
def argTerm {A : Ty α} : Assembly β A → LetCase.LocallyNameless.Tm Empty Φ n
  | .atom s => .bv s.1
  | .unit => .unit
  | .pair a b => .pair (argTerm a) (argTerm b)

/-- The native typing of an assembled argument. -/
def argTyping {A : Ty α} : (v : Assembly β A) → Derivation Φ Γ₀ β (argTerm v) A
  | .atom s => slotTyping s
  | .unit => .unit
  | .pair a b => .pair (argTyping a) (argTyping b)

/-- A position in the ordered exits, with the type of that exit. -/
inductive ExitAt : List (Ty α) → Ty α → Type where
  | here {A : Ty α} {L : List (Ty α)} : ExitAt (A :: L) A
  | there {A B : Ty α} {L : List (Ty α)} (later : ExitAt L A) : ExitAt (B :: L) A

/-- The number of exits before this one. -/
def ExitAt.index {L : List (Ty α)} {A : Ty α} : ExitAt L A → Nat
  | .here => 0
  | .there later => later.index + 1

/-- Return a term at this exit of the packed sum of the ordered exits. -/
def ExitAt.term {L : List (Ty α)} {A : Ty α} :
    ExitAt L A → LetCase.LocallyNameless.Tm Empty Φ n → LetCase.LocallyNameless.Tm Empty Φ n
  | .here, t => .inl t
  | .there later, t => .inr (later.term t)

/-- The native typing of a return at this exit. -/
def ExitAt.typing {A : Ty α} {t : LetCase.LocallyNameless.Tm Empty Φ n} :
    {L : List (Ty α)} → (e : ExitAt L A) → Derivation Φ Γ₀ β t A →
      Derivation Φ Γ₀ β (e.term t) (packedExitType L)
  | _, .here, d => .inl d
  | _, .there later, d => .inr (later.typing d)

/-- The value of a payload returned at this exit. -/
def ExitAt.value {A : Ty α} : {L : List (Ty α)} → ExitAt L A →
    LetSeq.StraightLine.Structural.Value (α := α) A →
    LetSeq.StraightLine.Structural.Value (α := α) (packedExitType L)
  | _, .here, x => .inl x
  | _, .there later, x => .inr (later.value x)

/-- What a tree must do with the newest slot before anything else. A body
has nothing pending. A pending tuple is unpacked into its atoms. A pending
reply is cased on, tag by tag. -/
inductive Pending (α : Type) where
  | body
  | tuple (atoms : List α)
  | tags (replies : List (List α))

/-- A case tree over ordered exits, in the context of its slots.

A body is a leaf or a request. A leaf returns a payload assembled from the
atom slots in scope, at one exit of the type of the payload. A request
binds the reply and continues with the reply pending at the newest slot.

A pending reply with one tag is its tuple. With more tags it is cased on:
the left arm has the tuple of the first tag pending and the right arm has
the remaining tags pending.

A pending tuple is unpacked in order. The empty tuple and a tuple of one
atom are already slots. A longer tuple is split into its first atom and
the rest, and the rest is pending. -/
inductive CaseTree : Pending α → {n : Nat} → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : CaseTree .body β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {k : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (reply : CaseTree (.tags (replyTags f)) (β.snoc (tagsTy (replyTags f))) L k) :
      CaseTree .body β L (.let₁ (.op f (argTerm argument)) k)
  | only {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (payload : CaseTree (.tuple atoms) (β.snoc (tupleTy atoms)) L t) :
      CaseTree (.tags [atoms]) (β.snoc (tagsTy [atoms])) L t
  | split {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms next : List α) (rest : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
      (left : CaseTree (.tuple atoms) ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tupleTy atoms)) L l)
      (right : CaseTree (.tags (next :: rest))
        ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tagsTy (next :: rest))) L r) :
      CaseTree (.tags (atoms :: next :: rest)) (β.snoc (tagsTy (atoms :: next :: rest))) L (.case (.bv 0) l r)
  | unit {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : CaseTree .body (β.snoc (tupleTy ([] : List α))) L t) :
      CaseTree (.tuple []) (β.snoc (tupleTy ([] : List α))) L t
  | atom {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a : α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : CaseTree .body (β.snoc (tupleTy [a])) L t) : CaseTree (.tuple [a]) (β.snoc (tupleTy [a])) L t
  | pair {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a b : α) (rest : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1 + 1)}
      (later : CaseTree (.tuple (b :: rest))
        (((β.snoc (tupleTy (a :: b :: rest))).snoc (.base a)).snoc (tupleTy (b :: rest))) L t) :
      CaseTree (.tuple (a :: b :: rest)) (β.snoc (tupleTy (a :: b :: rest))) L (.let₂ (.bv 0) t)

variable {L : List (Ty α)} {pending : Pending α}

/-- The native typing of a case tree at the packed sum of its ordered
exits, in its context. -/
def CaseTree.typing : {pending : Pending α} → {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    CaseTree pending β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, _, .ask f argument reply => .let₁ (.op (f := f) (argTyping argument)) reply.typing
  | _, _, _, _, .only _ payload => payload.typing
  | _, _, _, _, .split _ _ _ left right => .case .bv left.typing right.typing
  | _, _, _, _, .unit body => body.typing
  | _, _, _, _, .atom _ body => body.typing
  | _, _, _, _, .pair _ _ _ later => .let₂ .bv later.typing

/-- A case tree has at least one exit. -/
theorem CaseTree.exits_ne_nil : {pending : Pending α} → {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → L ≠ []
  | _, _, _, _, .ret exit _ => by cases exit <;> exact List.cons_ne_nil _ _
  | _, _, _, _, .ask _ _ reply => reply.exits_ne_nil
  | _, _, _, _, .only _ payload => payload.exits_ne_nil
  | _, _, _, _, .split _ _ _ left _ => left.exits_ne_nil
  | _, _, _, _, .unit body => body.exits_ne_nil
  | _, _, _, _, .atom _ body => body.exits_ne_nil
  | _, _, _, _, .pair _ _ _ later => later.exits_ne_nil

/-- A body as a captured LetCase operand. -/
def CaseTree.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree .body β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The operand is natively equal to a case tree. -/
def Branching (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : CaseTree .body β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

/-- The checked graph that the readback builds from a case tree. Its
exits are the original ordered exits. -/
def CaseTree.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree .body β L t) :
    CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

/-- The fresh value of a tuple of atoms: consecutive tokens from a start. -/
def freshTuple : (atoms : List α) → Nat → LetSeq.StraightLine.Structural.Value (α := α) (tupleTy atoms)
  | [], _ => PUnit.unit
  | [_], k => k
  | _ :: b :: rest, k => (k, freshTuple (b :: rest) (k + 1))

/-- A reply at the first of its tags. -/
def firstReply : (atoms : List α) → (rest : List (List α)) →
    LetSeq.StraightLine.Structural.Value (α := α) (tagsTy (atoms :: rest))
  | atoms, [] => freshTuple atoms 0
  | atoms, _ :: _ => .inl (freshTuple atoms 0)

/-- The environments at which the token induction compares two trees.

For a body: one environment that separates the atom slots below a bound.
For a pending tuple: such an environment under the fresh tuple at that
bound. For a pending reply: every reply value, each over an environment
that separates the atom slots below the bound. The environment under a
reply may depend on the reply, because the slots of earlier case splits
hold what was split. -/
def TokenWitness : Pending α → {n : Nat} → (β : BoundCtx (Ty α) n) → Nat →
    (BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β → Prop) → Prop
  | .body, _, _, k, P => ∃ ρ, Separates ρ (Set.Iio k) ∧ P ρ
  | .tuple atoms, _, .snoc β X, k, P =>
    ∃ (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β)
      (x : LetSeq.StraightLine.Structural.Value (α := α) X),
      Separates ρ (Set.Iio k) ∧ HEq x (freshTuple atoms k) ∧ P (ρ.snoc x)
  | .tags _, _, .snoc β X, k, P =>
    ∃ R : LetSeq.StraightLine.Structural.Value (α := α) X →
        BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β,
      (∀ w, Separates (R w) (Set.Iio k)) ∧ ∀ w, P ((R w).snoc w)
  | .tuple _, _, .nil, _, _ => False
  | .tags _, _, .nil, _, _ => False

/-! ## Renaming case trees

Case trees of the three kinds are one inductive family, so the renaming
action is one recursion. Its inputs and results depend on the kind: a
body is renamed along a renaming of its context, and a pending tuple or
reply along a renaming of the context beneath its pending slot. The types
of the renamings and of the results, and the statements of the laws, are
therefore given by cases on the kind and the context. The theorems restate
the laws for each kind. -/

/-- Move the three newest slots past two slots inserted beneath them: the
newest two move up by one and the third becomes newest. -/
def afterPair {m : Nat} : Fin (m + 3) → Fin (m + 3) :=
  Fin.cases 1 (Fin.cases 2 (Fin.cases 0 (fun i => i.succ.succ.succ)))

/-- That move as a renaming of contexts: two slots `A`, `B` bound after a
slot `X` are placed beneath it. -/
def afterPairRenaming {m : Nat} (Δ : BoundCtx (Ty α) m) (X A B : Ty α) :
    BoundCtx.Renaming (((Δ.snoc X).snoc A).snoc B) (((Δ.snoc A).snoc B).snoc X) where
  toFun := afterPair
  typed := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))

/-- The inverse of that move: the newest slot goes beneath the two slots
under it. -/
def beforePair {m : Nat} : Fin (m + 3) → Fin (m + 3) :=
  Fin.cases 2 (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ)))

/-- The inverse move as a renaming of contexts. -/
def beforePairRenaming {m : Nat} (Δ : BoundCtx (Ty α) m) (X A B : Ty α) :
    BoundCtx.Renaming (((Δ.snoc A).snoc B).snoc X) (((Δ.snoc X).snoc A).snoc B) where
  toFun := beforePair
  typed := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))

/-- Exchange the two newest slots. -/
def swapRenaming {m : Nat} (Ω : BoundCtx (Ty α) m) (X Y : Ty α) :
    BoundCtx.Renaming ((Ω.snoc X).snoc Y) ((Ω.snoc Y).snoc X) where
  toFun := Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))
  typed := Fin.cases rfl (Fin.cases rfl (fun _ => rfl))

/-- The renamings along which a case tree can be renamed. A body is renamed
along any renaming of its context. A pending tuple or reply is renamed
along a renaming of the context beneath its pending slot, which stays
newest. -/
def CaseTree.Along : Pending α → {n : Nat} → BoundCtx (Ty α) n → {m : Nat} → BoundCtx (Ty α) m → Type
  | .body, _, β, _, γ => BoundCtx.Renaming β γ
  | .tuple _, _, .snoc β _, _, γ => BoundCtx.Renaming β γ
  | .tags _, _, .snoc β _, _, γ => BoundCtx.Renaming β γ
  | .tuple _, _, .nil, _, _ => PEmpty
  | .tags _, _, .nil, _, _ => PEmpty

/-- The renamed case trees: a body in the target context, or a pending
tree in the target context under the same pending slot. -/
def CaseTree.Renamed (Φ : Type) [TaggedSignature α Φ] (L : List (Ty α)) :
    Pending α → {n : Nat} → BoundCtx (Ty α) n → {m : Nat} → BoundCtx (Ty α) m → Type
  | .body, _, _, m, γ => (u : LetCase.LocallyNameless.Tm Empty Φ m) × CaseTree .body γ L u
  | .tuple atoms, _, .snoc _ X, m, γ =>
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tuple atoms) (γ.snoc X) L u
  | .tags replies, _, .snoc _ X, m, γ =>
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tags replies) (γ.snoc X) L u
  | .tuple _, _, .nil, _, _ => PEmpty
  | .tags _, _, .nil, _, _ => PEmpty

/-- The renaming action on case trees. -/
def CaseTree.renamed : {pending : Pending α} → {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → CaseTree.Along pending β γ → CaseTree.Renamed Φ L pending β γ
  | _, _, _, _, .ret exit payload, _, _, ρ => ⟨_, .ret exit (payload.rename ρ)⟩
  | _, _, _, _, .ask f argument reply, _, _, ρ => ⟨_, .ask f (argument.rename ρ) (reply.renamed ρ).2⟩
  | _, _, _, _, .only atoms payload, _, _, ρ => ⟨_, .only atoms (payload.renamed ρ).2⟩
  | _, _, _, _, .split atoms next rest left right, _, _, ρ =>
    ⟨_, .split atoms next rest (left.renamed (ρ.up _)).2 (right.renamed (ρ.up _)).2⟩
  | _, _, _, _, .unit body, _, _, ρ => ⟨_, .unit (body.renamed (ρ.up _)).2⟩
  | _, _, _, _, .atom a body, _, _, ρ => ⟨_, .atom a (body.renamed (ρ.up _)).2⟩
  | _, _, _, _, .pair a b rest later, _, _, ρ =>
    ⟨_, .pair a b rest (later.renamed ((ρ.up _).up _)).2⟩

/-- The term of a renamed case tree is the renamed term. Under a pending
slot the renaming keeps that slot. -/
def CaseTree.RenamedTerm : (pending : Pending α) → {n : Nat} → (β : BoundCtx (Ty α) n) → {m : Nat} →
    (γ : BoundCtx (Ty α) m) → LetCase.LocallyNameless.Tm Empty Φ n → CaseTree.Along pending β γ →
    CaseTree.Renamed Φ L pending β γ → Prop
  | .body, _, _, _, _, t, ρ, r => r.1 = t.rename ρ.toFun
  | .tuple _, _, .snoc _ _, _, _, t, ρ, r => r.1 = t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)
  | .tags _, _, .snoc _ _, _, _, t, ρ, r => r.1 = t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)
  | .tuple _, _, .nil, _, _, _, _, _ => True
  | .tags _, _, .nil, _, _, _, _, _ => True

/-- Renaming a case tree twice is renaming along the composite. -/
def CaseTree.RenamedComp : (pending : Pending α) → {n : Nat} → (β : BoundCtx (Ty α) n) →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → Prop
  | .body, _, β, _, tree =>
    ∀ {m : Nat} {γ : BoundCtx (Ty α) m} {k : Nat} {δ : BoundCtx (Ty α) k}
      (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ),
      CaseTree.renamed (pending := .body) (tree.renamed ρ).2 π = tree.renamed (ρ.comp π)
  | .tuple atoms, _, .snoc β X, _, tree =>
    ∀ {m : Nat} {γ : BoundCtx (Ty α) m} {k : Nat} {δ : BoundCtx (Ty α) k}
      (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ),
      CaseTree.renamed (pending := .tuple atoms) (β := γ.snoc X) (tree.renamed ρ).2 π =
        tree.renamed (ρ.comp π)
  | .tags replies, _, .snoc β X, _, tree =>
    ∀ {m : Nat} {γ : BoundCtx (Ty α) m} {k : Nat} {δ : BoundCtx (Ty α) k}
      (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ),
      CaseTree.renamed (pending := .tags replies) (β := γ.snoc X) (tree.renamed ρ).2 π =
        tree.renamed (ρ.comp π)
  | .tuple _, _, .nil, _, _ => True
  | .tags _, _, .nil, _, _ => True

/-! ## Telescopes

A telescope is a list of slot types, oldest first, that extends a context.
One renaming moves a slot bound after a telescope beneath it. The other
permutations of binders used below are composed from it and from the
exchange of two slots, so no tuple length is fixed. -/

/-- The size of a context extended by a telescope. -/
def teleSize : Nat → List (Ty α) → Nat
  | k, [] => k
  | k, _ :: tel => teleSize (k + 1) tel

/-- A context extended by a telescope: a list of slot types, oldest first. -/
def extendCtx : {k : Nat} → BoundCtx (Ty α) k → (tel : List (Ty α)) → BoundCtx (Ty α) (teleSize k tel)
  | _, Ω, [] => Ω
  | _, Ω, X :: tel => extendCtx (Ω.snoc X) tel

/-- Weaken past a telescope. -/
def weakenTele : {k : Nat} → (Ω : BoundCtx (Ty α) k) → (tel : List (Ty α)) →
    BoundCtx.Renaming Ω (extendCtx Ω tel)
  | _, Ω, [] => .id Ω
  | _, Ω, X :: tel => (BoundCtx.Renaming.succ Ω X).comp (weakenTele (Ω.snoc X) tel)

/-- Lift a renaming under a telescope. -/
def upTele : {k j : Nat} → {Ω : BoundCtx (Ty α) k} → {Ω' : BoundCtx (Ty α) j} → BoundCtx.Renaming Ω Ω' →
    (tel : List (Ty α)) → BoundCtx.Renaming (extendCtx Ω tel) (extendCtx Ω' tel)
  | _, _, _, _, ρ, [] => ρ
  | _, _, _, _, ρ, X :: tel => upTele (ρ.up X) tel

/-- Move one slot bound after a telescope beneath it. Every other
permutation of binders used here is built from this one. -/
def swapTele : {k : Nat} → (Ω : BoundCtx (Ty α) k) → (tel : List (Ty α)) → (T : Ty α) →
    BoundCtx.Renaming ((extendCtx Ω tel).snoc T) (extendCtx (Ω.snoc T) tel)
  | _, _, [], _ => .id _
  | _, Ω, X :: tel, T => (swapTele (Ω.snoc X) tel T).comp (upTele (swapRenaming Ω X T) tel)

/-- Move two slots bound after a telescope beneath it, one after the other. -/
def pairPastTele {k : Nat} (Ω : BoundCtx (Ty α) k) (tel : List (Ty α)) (A B : Ty α) :
    BoundCtx.Renaming (((extendCtx Ω tel).snoc A).snoc B) (extendCtx ((Ω.snoc A).snoc B) tel) :=
  ((swapTele Ω tel A).up B).comp (swapTele (Ω.snoc A) tel B)

/-- Move a telescope bound after a telescope beneath it, one slot at a
time. -/
def swapTeles : {k : Nat} → (Ω : BoundCtx (Ty α) k) → (tel : List (Ty α)) → (H : List (Ty α)) →
    BoundCtx.Renaming (extendCtx (extendCtx Ω tel) H) (extendCtx (extendCtx Ω H) tel)
  | _, _, _, [] => .id _
  | _, Ω, tel, X :: H => (upTele (swapTele Ω tel X) H).comp (swapTeles (Ω.snoc X) tel H)

/-- Weaken past two new slots. -/
def pastPair {k : Nat} (Ω : BoundCtx (Ty α) k) (A B : Ty α) : BoundCtx.Renaming Ω ((Ω.snoc A).snoc B) :=
  (BoundCtx.Renaming.succ Ω A).comp (BoundCtx.Renaming.succ (Ω.snoc A) B)

/-- Move the two newest pairs of slots past each other: the newest two
slots go beneath the two slots under them. -/
def afterPairPair {m : Nat} : Fin (m + 4) → Fin (m + 4) :=
  Fin.cases 2 (Fin.cases 3 (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ))))

/-- That move as a renaming of contexts: two slots `A`, `B` bound after two
slots `C`, `D` are placed beneath them. -/
def afterPairPairRenaming {m : Nat} (Γ : BoundCtx (Ty α) m) (C D A B : Ty α) :
    BoundCtx.Renaming ((((Γ.snoc C).snoc D).snoc A).snoc B) ((((Γ.snoc A).snoc B).snoc C).snoc D) where
  toFun := afterPairPair
  typed := Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))

/-! ## Unpacking a tuple slot

The slots bound by unpacking a tuple slot form a telescope, and the
pattern lets of the unpacking wrap a term over that telescope. -/

/-- The slots bound by unpacking a tuple slot, after that slot: for two or
more atoms, the first atom and the rest of the tuple, then the slots of
unpacking the rest. -/
def pairsTele : List α → List (Ty α)
  | [] => []
  | [_] => []
  | c :: d :: more => .base c :: tupleTy (d :: more) :: pairsTele (d :: more)

/-- A tuple slot followed by the slots bound by unpacking it. -/
abbrev unpackTele (atoms : List α) : List (Ty α) := tupleTy atoms :: pairsTele atoms

/-- The pattern lets that unpack a tuple slot around a term. The first is
on the given slot and each later one on the newest slot. -/
def unpackAt : (atoms : List α) → {k : Nat} → Fin k →
    LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms)) → LetCase.LocallyNameless.Tm Empty Φ k
  | [], _, _, u => u
  | [_], _, _, u => u
  | _ :: d :: more, _, i, u => .let₂ (.bv i) (unpackAt (d :: more) 0 u)

/-! ## Stacks of packed tuples

Several tuples may be packed at once, each at its own slot. A stack lists
their atoms, newest first. Unpacking the whole stack unpacks the oldest
tuple outermost. The context under those unpackings, and the renamings
that weaken past it, lift under it and move a telescope beneath it, are
defined by recursion on the stack from the telescope renamings. -/

/-- The size of a context under the unpackings of a stack. -/
def stackSize : Nat → List (List α) → Nat
  | k, [] => k
  | k, atoms :: stack => teleSize (stackSize k stack) (pairsTele atoms)

/-- A context under the unpackings of a stack of packed tuples. -/
def stackCtx : (stack : List (List α)) → {k : Nat} → BoundCtx (Ty α) k →
    BoundCtx (Ty α) (stackSize k stack)
  | [], _, Ω => Ω
  | atoms :: stack, _, Ω => extendCtx (stackCtx stack Ω) (pairsTele atoms)

/-- Weaken past the unpackings of a stack. -/
def weakenStack : (stack : List (List α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    BoundCtx.Renaming Ω (stackCtx stack Ω)
  | [], _, Ω => .id Ω
  | atoms :: stack, _, Ω => (weakenStack stack Ω).comp (weakenTele (stackCtx stack Ω) (pairsTele atoms))

/-- Lift a renaming under the unpackings of a stack. -/
def upStack : (stack : List (List α)) → {k j : Nat} → {Ω : BoundCtx (Ty α) k} → {Ω' : BoundCtx (Ty α) j} →
    BoundCtx.Renaming Ω Ω' → BoundCtx.Renaming (stackCtx stack Ω) (stackCtx stack Ω')
  | [], _, _, _, _, ρ => ρ
  | atoms :: stack, _, _, _, _, ρ => upTele (upStack stack ρ) (pairsTele atoms)

/-- Move a telescope bound before the unpackings of a stack beneath them. -/
def swapStack : (stack : List (List α)) → {k : Nat} → (Ω : BoundCtx (Ty α) k) → (tel : List (Ty α)) →
    BoundCtx.Renaming (stackCtx stack (extendCtx Ω tel)) (extendCtx (stackCtx stack Ω) tel)
  | [], _, _, _ => .id _
  | atoms :: stack, _, Ω, tel =>
    (upTele (swapStack stack Ω tel) (pairsTele atoms)).comp (swapTeles (stackCtx stack Ω) tel (pairsTele atoms))

/-- The slots of a stack of packed tuples, newest first. -/
inductive Holds : {m : Nat} → BoundCtx (Ty α) m → List (List α) → Type where
  | nil {m : Nat} {Δ : BoundCtx (Ty α) m} : Holds Δ []
  | cons {m : Nat} {Δ : BoundCtx (Ty α) m} {atoms : List α} {stack : List (List α)}
      (top : Slot Δ (tupleTy atoms)) (older : Holds Δ stack) : Holds Δ (atoms :: stack)

/-- The slots of a stack along a renaming. -/
def Holds.rename {m k : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming Δ Θ) :
    {stack : List (List α)} → Holds Δ stack → Holds Θ stack
  | _, .nil => .nil
  | _, .cons top older => .cons (top.rename ρ) (older.rename ρ)

/-- A selection of one packed tuple of a stack: the atoms of the selected
tuple, and the stack of the other tuples in their order. Any tuple of the
stack can be selected. -/
inductive Select : List (List α) → List α → List (List α) → Type where
  | here {atoms : List α} {stack : List (List α)} : Select (atoms :: stack) atoms stack
  | there {x : List α} {stack : List (List α)} {atoms : List α} {rest : List (List α)}
      (sel : Select stack atoms rest) : Select (x :: stack) atoms (x :: rest)

/-- The slot of the selected tuple. -/
def Holds.pick {m : Nat} {Δ : BoundCtx (Ty α) m} : {stack : List (List α)} → {atoms : List α} →
    {rest : List (List α)} → Select stack atoms rest → Holds Δ stack → Slot Δ (tupleTy atoms)
  | _, _, _, .here, .cons top _ => top
  | _, _, _, .there sel, .cons _ older => older.pick sel

/-- The slots of the other tuples. -/
def Holds.drop {m : Nat} {Δ : BoundCtx (Ty α) m} : {stack : List (List α)} → {atoms : List α} →
    {rest : List (List α)} → Select stack atoms rest → Holds Δ stack → Holds Δ rest
  | _, _, _, .here, .cons _ older => older
  | _, _, _, .there sel, .cons top older => .cons top (older.drop sel)

/-- The slots of a stack with the selected tuple moved to the top. -/
def Holds.select {m : Nat} {Δ : BoundCtx (Ty α) m} {stack : List (List α)} {atoms : List α}
    {rest : List (List α)} (sel : Select stack atoms rest) (H : Holds Δ stack) : Holds Δ (atoms :: rest) :=
  .cons (H.pick sel) (H.drop sel)

/-- The context under the unpackings of a stack in which the selected tuple
is unpacked innermost, into the context in which it is unpacked in its
place. The slots of the unpacking of the selected tuple move beneath the
slots of the unpackings of the newer tuples, one telescope at a time. -/
def selectRen : {stack : List (List α)} → {atoms : List α} → {rest : List (List α)} →
    Select stack atoms rest → {k : Nat} → (Ω : BoundCtx (Ty α) k) →
    BoundCtx.Renaming (stackCtx (atoms :: rest) Ω) (stackCtx stack Ω)
  | _, _, _, .here, _, _ => .id _
  | _, atoms, _, @Select.there _ x _ _ rest sel, _, Ω =>
    (swapTeles (stackCtx rest Ω) (pairsTele x) (pairsTele atoms)).comp (upTele (selectRen sel Ω) (pairsTele x))

/-- The pattern lets that unpack every tuple of a stack around a term. The
oldest tuple is unpacked outermost. -/
def unpackStack : (stack : List (List α)) → {k : Nat} → {Ω : BoundCtx (Ty α) k} → Holds Ω stack →
    LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack) → LetCase.LocallyNameless.Tm Empty Φ k
  | [], _, _, _, u => u
  | atoms :: stack, _, Ω, .cons top older, u =>
    unpackStack stack older (unpackAt atoms ((weakenStack stack Ω).toFun top.1) u)

/-! ## Binding slots under a pending tuple

The slots of a telescope beneath a pending tuple are moved to bindings
under the unpacking of the tuple. This is an operation on pending case
trees: it places a request asked before a tuple is unpacked under that
unpacking, with the reply of the request and the slots of its unpacking as
the telescope. The normal forms of spelled chains are built directly under
the unpacking instead and do not use it. -/

/-- A way to bind the slots of a telescope in front of a body, in any
context that the base context renames into. -/
abbrev CaseTree.Wrap (Φ : Type) [TaggedSignature α Φ] (L : List (Ty α)) {m : Nat} (Ω : BoundCtx (Ty α) m)
    (tel : List (Ty α)) :=
  ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel)} → CaseTree .body (extendCtx Ω' tel) L u →
    (v : LetCase.LocallyNameless.Tm Empty Φ k) × CaseTree .body Ω' L v

/-- The data for moving a telescope under a pending tuple: a renaming of
the context beneath the tuple that puts the telescope newest. -/
def CaseTree.PushAlong : Pending α → {n : Nat} → BoundCtx (Ty α) n → {m : Nat} → BoundCtx (Ty α) m →
    List (Ty α) → Type
  | .body, _, _, _, _, _ => PEmpty
  | .tags _, _, _, _, _, _ => PEmpty
  | .tuple _, _, .nil, _, _, _ => PEmpty
  | .tuple _, _, .snoc Ξ _, _, Ω, tel => BoundCtx.Renaming Ξ (extendCtx Ω tel)

/-- The result of moving a telescope under a pending tuple: the pending
tuple over the context without the telescope. -/
def CaseTree.Pushed (Φ : Type) [TaggedSignature α Φ] (L : List (Ty α)) :
    Pending α → {n : Nat} → BoundCtx (Ty α) n → {m : Nat} → BoundCtx (Ty α) m → Type
  | .body, _, _, _, _ => PUnit
  | .tags _, _, _, _, _ => PUnit
  | .tuple _, _, .nil, _, _ => PUnit
  | .tuple atoms, _, .snoc _ T, m, Ω =>
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tuple atoms) (Ω.snoc T) L u

/-- Move the slots of a telescope beneath a pending tuple to bindings under
the full unpacking of the tuple. At each body under the unpacking, the
body is renamed so that the telescope is newest and the bindings are put
in front of it. -/
def CaseTree.pushed : {pending : Pending α} → {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → {m : Nat} →
    {Ω : BoundCtx (Ty α) m} → {tel : List (Ty α)} → CaseTree.PushAlong pending β Ω tel →
    CaseTree.Wrap Φ L Ω tel → CaseTree.Pushed Φ L pending β Ω
  | _, _, _, _, .ret _ _, _, _, _, π, _ => nomatch π
  | _, _, _, _, .ask _ _ _reply, _, _, _, π, _ => nomatch π
  | _, _, _, _, .only _ _payload, _, _, _, π, _ => nomatch π
  | _, _, _, _, .split _ _ _ _left _right, _, _, _, π, _ => nomatch π
  | _, _, _, _, .unit body, _, Ω, tel, π, wrap =>
    ⟨_, .unit (wrap (BoundCtx.Renaming.succ Ω _)
      (body.renamed ((π.up _).comp (swapTele Ω tel _))).2).2⟩
  | _, _, _, _, .atom a body, _, Ω, tel, π, wrap =>
    ⟨_, .atom a (wrap (BoundCtx.Renaming.succ Ω _)
      (body.renamed ((π.up _).comp (swapTele Ω tel _))).2).2⟩
  | _, _, _, _, .pair a b rest later, _, Ω, tel, π, wrap =>
    ⟨_, .pair a b rest (later.pushed (((π.up _).up _).comp (pairPastTele Ω tel _ _))
      (fun ω => wrap ((pastPair Ω _ _).comp ω))).2⟩

/-- Binding a telescope under a renamed pending tuple is binding it under
the tuple along the composite renaming. -/
def CaseTree.PushedPre : (pending : Pending α) → {n : Nat} → (β : BoundCtx (Ty α) n) →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → Prop
  | .body, _, _, _, _ => True
  | .tags _, _, _, _, _ => True
  | .tuple _, _, .nil, _, _ => True
  | .tuple atoms, _, .snoc Ξ T, _, tree =>
    ∀ {j : Nat} {Ξ' : BoundCtx (Ty α) j} (ρ : BoundCtx.Renaming Ξ Ξ') {m : Nat} {Ω : BoundCtx (Ty α) m}
      {tel : List (Ty α)} (π : BoundCtx.Renaming Ξ' (extendCtx Ω tel)) (wrap : CaseTree.Wrap Φ L Ω tel),
      CaseTree.pushed (pending := .tuple atoms) (β := Ξ'.snoc T)
        (CaseTree.renamed (pending := .tuple atoms) tree ρ).2 π wrap = CaseTree.pushed tree (ρ.comp π) wrap

/-- A way to bind a telescope commutes with renaming. -/
def CaseTree.Wrap.Natural {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    (wrap : CaseTree.Wrap Φ L Ω tel) : Prop :=
  ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel)} (r : CaseTree .body (extendCtx Ω' tel) L u)
    {j : Nat} {Ω'' : BoundCtx (Ty α) j} (ω' : BoundCtx.Renaming Ω' Ω''),
    CaseTree.renamed (pending := .body) (wrap ω r).2 ω' =
      wrap (ω.comp ω') (CaseTree.renamed (pending := .body) r (upTele ω' tel)).2

/-- Renaming the result of binding a telescope under a pending tuple is
binding the telescope under the tuple along the composite renaming, with
the binding taken after the renaming. -/
def CaseTree.PushedPost : (pending : Pending α) → {n : Nat} → (β : BoundCtx (Ty α) n) →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → Prop
  | .body, _, _, _, _ => True
  | .tags _, _, _, _, _ => True
  | .tuple _, _, .nil, _, _ => True
  | .tuple atoms, _, .snoc Ξ T, _, tree =>
    ∀ {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)} (π : BoundCtx.Renaming Ξ (extendCtx Ω tel))
      (wrap : CaseTree.Wrap Φ L Ω tel), wrap.Natural →
      ∀ {j : Nat} {Ω' : BoundCtx (Ty α) j} (ω : BoundCtx.Renaming Ω Ω'),
      CaseTree.renamed (pending := .tuple atoms) (β := Ω.snoc T) (CaseTree.pushed tree π wrap).2 ω =
        CaseTree.pushed tree (π.comp (upTele ω tel)) (fun ω' => wrap (ω.comp ω'))

/-- The pending tuple whose unpacking ends in a given body. The body is
over the tuple slot and the slots of its unpacking. -/
def CaseTree.packed : (atoms : List α) → {k : Nat} → {Ω : BoundCtx (Ty α) k} →
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms))} →
    CaseTree .body (extendCtx Ω (unpackTele atoms)) L u →
    CaseTree (.tuple atoms) (Ω.snoc (tupleTy atoms)) L (unpackAt atoms 0 u)
  | [], _, _, _, r => .unit r
  | [c], _, _, _, r => .atom c r
  | c :: d :: more, _, _, _, r => .pair c d more (CaseTree.packed (d :: more) r)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
