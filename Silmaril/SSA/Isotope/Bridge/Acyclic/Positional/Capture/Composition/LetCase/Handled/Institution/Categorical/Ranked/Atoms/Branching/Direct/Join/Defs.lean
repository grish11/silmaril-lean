module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Branch.Thms

/-! # A shared join before the stored reply is inspected

While a reply with two tags is stored as one slot, a request is asked and
its reply, with two tags, is cased on. The two arms do not continue on
their own: each arm is a finite nonbranching prefix that ends with a tuple
of one common type on top of its stack, the joined payload, and the two
arms feed one continuation, written once. The continuation has the joined
payload newest and on top of the stack; it may use it, ask further
requests, branch, and it inspects the stored reply at its leaves. As a
term this is

`let₁ (case y A B) K`

where `A` and `B` are the arms, each a prefix around the slot it supplies,
and `K` is the continuation.

`SpelledJoinTags` is that node, as the bound reply of the request. Its
expansion is a bound reply of the tree-shaped family: the case on the
reply with, in each arm, the prefix of the arm followed by the
continuation, renamed so that the joined payload is the slot the arm
supplies. The expansion keeps the context and the exits.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

mutual

/-- The native typing of a prefix around a typed term at its end. -/
def SpelledPrefix.plugTyping : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} →
    {holds' : Holds Δ' stack'} → (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') →
    {e : LetCase.LocallyNameless.Tm Empty Φ m'} → {C : Ty α} → Derivation Φ Γ₀ Δ' e C → Derivation Φ Γ₀ Δ (p.plug e) C
  | _, _, _, _, _, _, _, _, .stop, _, _, d => d
  | _, _, _, _, _, _, _, _, .unit next, _, _, d => next.plugTyping d
  | _, _, _, _, _, _, _, _, .atom next, _, _, d => next.plugTyping d
  | _, _, _, .cons top _, _, _, _, _, .step next, _, _, d => .let₂ (slotTyping top) (next.plugTyping d)
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, d =>
    .let₁ (.op (f := g) (argTyping argument)) (reply.plugTyping d)
  | _, _, _, _, _, _, _, _, .pick _ next, _, _, d => next.plugTyping d

/-- The native typing of a bound reply of a prefix around a typed term at
its end. -/
def SpelledPrefixTags.plugTyping : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {e : LetCase.LocallyNameless.Tm Empty Φ m'} →
    {C : Ty α} → Derivation Φ Γ₀ Δ' e C → Derivation Φ Γ₀ (Δ.snoc (tagsTy tags)) (p.plug e) C
  | _, _, _, _, _, _, _, _, _, .bind _ next, _, _, d => next.plugTyping d

end

mutual

/-- A prefix followed by a tree at its end, as a tree. The stored slot of
the tree at the end is the weakened stored slot. -/
def SpelledPrefix.thenDelay {atoms next : List α} : {stack : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {stack' : List (List α)} → {m' : Nat} →
    {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefix (Φ := Φ) stack Δ holds stack' Δ' holds') → {s : Fin m} → {e : LetCase.LocallyNameless.Tm Empty Φ m'} →
    SpelledDelay atoms next stack' Δ' holds' (p.weaken.toFun s) L e →
    SpelledDelay atoms next stack Δ holds s L (p.plug e)
  | _, _, _, _, _, _, _, _, .stop, _, _, d => d
  | _, _, _, _, _, _, _, _, .unit rest, _, _, d => .unit (rest.thenDelay d)
  | _, _, _, _, _, _, _, _, .atom rest, _, _, d => .atom (rest.thenDelay d)
  | _, _, _, .cons _ _, _, _, _, _, .step rest, _, _, d => .step (rest.thenDelay d)
  | _, _, _, _, _, _, _, _, .ask g argument reply, _, _, d => .ask g argument (reply.thenDelay d)
  | _, _, _, _, _, _, _, _, .pick sel rest, _, _, d => .pick sel (rest.thenDelay d)

/-- A bound reply of a prefix followed by a tree at its end. -/
def SpelledPrefixTags.thenDelay {atoms next : List α} : {stack : List (List α)} →
    {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} →
    {stack' : List (List α)} → {m' : Nat} → {Δ' : BoundCtx (Ty α) m'} → {holds' : Holds Δ' stack'} →
    (p : SpelledPrefixTags (Φ := Φ) stack tags Δ holds stack' Δ' holds') → {s : Fin m} →
    {e : LetCase.LocallyNameless.Tm Empty Φ m'} → SpelledDelay atoms next stack' Δ' holds' (p.weaken.toFun s) L e →
    SpelledDelayTags atoms next stack tags Δ holds s L (p.plug e)
  | _, _, _, _, _, _, _, _, _, .bind reply rest, _, _, d => .bind reply (rest.thenDelay d)

end

/-- The renaming of the continuation of a join into an arm: the slots
beneath the reply payload follow the weakening of the prefix of the arm,
and the joined payload goes to the slot the arm supplies. -/
def joinRenaming {m k : Nat} {Γ : BoundCtx (Ty α) m} {A J : Ty α} {Ξ : BoundCtx (Ty α) k}
    (weaken : BoundCtx.Renaming (Γ.snoc A) Ξ) (top : Slot Ξ J) : BoundCtx.Renaming (Γ.snoc J) Ξ :=
  snocRenaming ((BoundCtx.Renaming.succ Γ A).comp weaken) top

/-- The bound reply of a request whose two tags feed one continuation,
with the stored slot `s` beneath it. Each arm is a nonbranching prefix
from the payload of its tag to a tuple `joined` on top of the stack, with
the older tuples of the stack left in place. The continuation is a tree
with that tuple newest and on top of the stack. -/
inductive SpelledJoinTags (atoms next : List α) : (stack : List (List α)) → List (List α) → {m : Nat} →
    (Δ : BoundCtx (Ty α) m) → Holds Δ stack → Fin m → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ (m + 1) → Type where
  | join {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {s : Fin m}
      {L : List (Ty α)} (first second joined : List α)
      {mA : Nat} {ΔA : BoundCtx (Ty α) mA} {topA : Slot ΔA (tupleTy joined)} {olderA : Holds ΔA stack}
      (left : SpelledPrefix (Φ := Φ) (first :: stack)
        ((Δ.snoc (tagsTy [first, second])).snoc (tupleTy first))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy [first, second]) (tupleTy first))))
        (joined :: stack) ΔA (.cons topA olderA))
      (keptA : (holds.rename (pastPair Δ (tagsTy [first, second]) (tupleTy first))).rename left.weaken =
        olderA)
      {mB : Nat} {ΔB : BoundCtx (Ty α) mB} {topB : Slot ΔB (tupleTy joined)} {olderB : Holds ΔB stack}
      (right : SpelledPrefix (Φ := Φ) (second :: stack)
        ((Δ.snoc (tagsTy [first, second])).snoc (tupleTy second))
        (.cons ⟨0, rfl⟩ ((holds.rename (BoundCtx.Renaming.succ Δ (tagsTy [first, second]))).rename
          (BoundCtx.Renaming.succ (Δ.snoc (tagsTy [first, second])) (tupleTy second))))
        (joined :: stack) ΔB (.cons topB olderB))
      (keptB : (holds.rename (pastPair Δ (tagsTy [first, second]) (tupleTy second))).rename right.weaken =
        olderB)
      {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (rest : SpelledDelay atoms next (joined :: stack)
        ((Δ.snoc (tagsTy [first, second])).snoc (tupleTy joined))
        (.cons ⟨0, rfl⟩ ((holds.rename (BoundCtx.Renaming.succ Δ (tagsTy [first, second]))).rename
          (BoundCtx.Renaming.succ (Δ.snoc (tagsTy [first, second])) (tupleTy joined))))
        s.succ.succ L k) :
      SpelledJoinTags atoms next stack [first, second] Δ holds s L
        (.let₁ (.case (.bv 0) (left.plug (.bv topA.1)) (right.plug (.bv topB.1))) k)

/-- The native typing of a join, under the reply slot. -/
def SpelledJoinTags.typing {atoms next : List α} : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → SpelledJoinTags atoms next stack tags Δ holds s L t →
    Derivation Φ Γ₀ (Δ.snoc (tagsTy tags)) t (packedExitType L)
  | _, _, _, _, _, _, _, .join _ _ _ (topA := topA) (topB := topB) left _ right _ rest =>
    .let₁ (.case .bv (left.plugTyping (slotTyping topA)) (right.plugTyping (slotTyping topB))) rest.typing

/-- The term of the expansion of a join: the case on the reply with, in
each arm, the prefix of the arm around the continuation renamed into the
arm. -/
def SpelledJoinTags.inlined {atoms next : List α} : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → SpelledJoinTags atoms next stack tags Δ holds s L t → LetCase.LocallyNameless.Tm Empty Φ (m + 1)
  | _, _, _, _, _, _, _, .join _ _ _ (topA := topA) (topB := topB) (k := k) left _ right _ _ =>
    .case (.bv 0) (left.plug (k.rename (joinRenaming left.weaken topA).toFun))
      (right.plug (k.rename (joinRenaming right.weaken topB).toFun))

/-- The expansion of a join into the tree-shaped family: the reply is
cased on at once, and each arm is its prefix followed by the continuation
renamed into the arm. The continuation is written once in the join and
once in each arm of the expansion. -/
def SpelledJoinTags.expand {atoms next : List α} : {stack : List (List α)} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {s : Fin m} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (j : SpelledJoinTags atoms next stack tags Δ holds s L t) →
    Renamed (SpelledDelayTags atoms next stack tags Δ holds s L) j.inlined
  | _, _, _, Δ, holds, _, _, .join first second _ (topA := topA) (topB := topB) left keptA right keptB rest =>
    have keepA : ((holds.rename (BoundCtx.Renaming.succ Δ (tagsTy [first, second]))).rename
        (BoundCtx.Renaming.succ (Δ.snoc (tagsTy [first, second])) _)).rename
          (joinRenaming left.weaken topA) =
        (holds.rename (pastPair Δ (tagsTy [first, second]) (tupleTy first))).rename left.weaken :=
      holds_cube holds left.weaken rfl (renaming_ext (fun _ => rfl))
    have keepB : ((holds.rename (BoundCtx.Renaming.succ Δ (tagsTy [first, second]))).rename
        (BoundCtx.Renaming.succ (Δ.snoc (tagsTy [first, second])) _)).rename
          (joinRenaming right.weaken topB) =
        (holds.rename (pastPair Δ (tagsTy [first, second]) (tupleTy second))).rename right.weaken :=
      holds_cube holds right.weaken rfl (renaming_ext (fun _ => rfl))
    let rA := rest.renamed (joinRenaming left.weaken topA) (.cons topA _)
      (congrArg (Holds.cons topA) (keepA.trans keptA))
    let rB := rest.renamed (joinRenaming right.weaken topB) (.cons topB _)
      (congrArg (Holds.cons topB) (keepB.trans keptB))
    ⟨_, .split first second [] (left.thenDelay rA.tree) (.bind second (right.thenDelay rB.tree)),
      congrArg₂ (fun a b => LetCase.LocallyNameless.Tm.case (.bv 0) (left.plug a) (right.plug b)) rA.term_eq rB.term_eq⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
