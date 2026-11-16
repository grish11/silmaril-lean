module

public import Silmaril.Games.Abstract.SessionLink.Defs
public import Silmaril.Games.Abstract.StratOps.Defs

/-!
# Session-level category laws: definitions

Store-retaining triples `ObsTriple E S A (B ⊕ PUnit)` (`StratSession`) are linked by
`SessionLink.linkS`: a server `t` serves the imports `sig1 A B` of a client `u`. This topic
states the category laws of linking on the realizable session domain, by way of the session
strategies `StratSession.threadS`, where linking is composition with hiding
(`SessionLink.comp_threadS`).

**Determinism of returns.** `RetDet t`: any two *returning* behaviours of `t` at the same store
and argument agree as long as the import answers agree (`AFun.Agree`). It is `AFun.Det` restricted
to returns (`.ret`, which includes continuing traps `.ret (.inr ()) s`). Unlike `AFun.Det`, it is
preserved by linking (`SessionCat.Thms.retDet_linkS`): a linked return and a linked divergence
with the same log are allowed. It implies store determinism (`StratThread.StoreDet`), the
hypothesis of `comp_threadS` and `threadS_eq_iff`.

**The identity session** `idS : ObsTriple (sig1 A B) PUnit A (B ⊕ PUnit)` forwards the question
`a` as one call `⟨a, x⟩` and returns its answer `x`: a value `.inl b` returns `.inl b`, a trap
answer `.inr ()` is a continuing trap. Its store is `PUnit`; its only pending call is the forwarded
question, and it has no productive stream.

**Legality.** For a legality predicate `L : (m : E.Op) → E.Ar m → Prop` on import answers
(as in `StratLegal.legalSig`):

* `LogLegal L c`: every answer in the log `c` is legal;
* `Legal L t`: every import answer in the logs of `t` (finished behaviours, pending calls and
  productive streams) is legal;
* `AnsLegal L' t`, for `L'` a legality predicate on the session interface `sig1 A B`: every
  answer of `t` (a returned value or a continuing trap) is legal.

`pairAns L₁ L₂` is the legality of the answers of a paired session (`StratSession.pairS`).
`legalPart L t` keeps the observations of `t` whose logs are legal, on the same interface (a
filter, where `StratLegal.restrict` transports them to the legal interface).

**Sequencing within a round, with store-retaining traps.** For session triples on one store,
`seqS t u` runs `t`, then `u` on its value; a continuing trap `.ret (.inr ()) s₁` of `t` aborts
the round with the store `s₁` (`trapS`), a plain trap or a divergence of `t` is kept. It is
`StratOps.seqT` after the copairing `caseT u trapS`: the Kleisli sequencing of the exception
monad `· ⊕ PUnit`. Its unit is `retS`, returning the argument as a value.

**Store strength.** `frameS S' t : ObsTriple E (S × S') A B` runs `t` on the first store
component and leaves the second untouched (`frameEnd`).

Theorems in `Silmaril.Games.Abstract.SessionCat.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **Returns are deterministic given answers**: two returning behaviours at the same store and
argument agree until the import answers differ. -/
def RetDet (t : ObsTriple E S A B) : Prop :=
  ∀ s a c c' b b' s₁ s₁', (c, End.ret b s₁) ∈ t.1 s a → (c', End.ret b' s₁') ∈ t.1 s a →
    AFun.Agree c (End.ret b s₁) c' (End.ret b' s₁')

/-- **The identity session**: forward the question as one call and return its answer, a trap
answer being a continuing trap. -/
def idS : ObsTriple (sig1 A B) PUnit.{u + 1} A (B ⊕ PUnit.{u + 1}) :=
  (fun _ a => {x | ∃ y, x = ([⟨a, y⟩], End.ret y PUnit.unit)},
    fun _ a => {([], a)},
    fun _ _ => ∅)

/-- Every answer in the log is legal. -/
def LogLegal (L : (m : E.Op) → E.Ar m → Prop) (c : List (Call E)) : Prop :=
  ∀ x ∈ c, L x.1 x.2

/-- **A legal triple**: every import answer in its logs is legal. -/
def Legal (L : (m : E.Op) → E.Ar m → Prop) (t : ObsTriple E S A B) : Prop :=
  (∀ s a x, x ∈ t.1 s a → LogLegal L x.1) ∧ (∀ s a x, x ∈ t.2.1 s a → LogLegal L x.1) ∧
    ∀ s a ω, ω ∈ t.2.2 s a → ∀ k, L (ω k).1 (ω k).2

/-- **Legal answers**: every returned answer (value or continuing trap) is legal for the session
interface `sig1 A B`. -/
def AnsLegal (L : A → B → Prop) (t : ObsTriple E S A B) : Prop :=
  ∀ s a c b s₁, (c, End.ret b s₁) ∈ t.1 s a → L a b

/-- The observations of `t` with legal logs, on the same interface. -/
def legalPart (L : (m : E.Op) → E.Ar m → Prop) (t : ObsTriple E S A B) : ObsTriple E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ LogLegal L x.1},
    fun s a => {x | x ∈ t.2.1 s a ∧ LogLegal L x.1},
    fun s a => {ω | ω ∈ t.2.2 s a ∧ ∀ k, L (ω k).1 (ω k).2})

/-- Legal answers of a paired session (`StratSession.pairS`): an answer to `.inl a₁` is the
relabelling of an `L₁`-legal answer, and to `.inr a₂` of an `L₂`-legal one. -/
def pairAns {A₁ A₂ B₁ B₂ : Type u} (L₁ : A₁ → B₁ ⊕ PUnit.{u + 1} → Prop)
    (L₂ : A₂ → B₂ ⊕ PUnit.{u + 1} → Prop) : A₁ ⊕ A₂ → (B₁ ⊕ B₂) ⊕ PUnit.{u + 1} → Prop
  | .inl a, x => ∃ y, L₁ a y ∧ x = Sum.map .inl id y
  | .inr a, x => ∃ y, L₂ a y ∧ x = Sum.map .inr id y

/-! ## Sequencing and strength -/

open StratOps

/-- **The unit of session sequencing**: return the argument as a value, in the same store. -/
def retS : ObsTriple E S A (A ⊕ PUnit.{u + 1}) := mapT pureT Sum.inl

/-- **The trap continuation**: a continuing trap, in the same store. -/
def trapS : ObsTriple E S PUnit.{u + 1} (B ⊕ PUnit.{u + 1}) := mapT pureT Sum.inr

/-- **Session sequencing within a round**: run `t`, then `u` on its value; a continuing trap of
`t` aborts the round, keeping its store. -/
def seqS {C : Type u} (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S B (C ⊕ PUnit.{u + 1})) : ObsTriple E S A (C ⊕ PUnit.{u + 1}) :=
  seqT t (caseT u trapS)

/-- The end of a framed round: the second store component is kept. -/
def frameEnd {S' : Type u} (s' : S') : End S B → End (S × S') B
  | .ret b s => .ret b (s, s')
  | .trap => .trap
  | .div => .div

/-- **Store strength**: run `t` on the first store component, the second untouched. -/
def frameS (S' : Type u) (t : ObsTriple E S A B) : ObsTriple E (S × S') A B :=
  (fun σ a => (fun x => (x.1, frameEnd σ.2 x.2)) '' t.1 σ.1 a,
    fun σ a => t.2.1 σ.1 a,
    fun σ a => t.2.2 σ.1 a)

end Silmaril.Games.Abstract.SessionCat
