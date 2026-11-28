module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs

/-! # Recursively typed block-free sources with retained Bit captures -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Tree)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live slots Direct)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer)

/-- A query can forward a slot directly or through a constructor-known case.
The dead arm is still a scoped read in the written term. -/
inductive Query (n : Nat) where
  | read (slot : Fin n)
  | known (right : Bool) (payload dead : Fin n)

def Query.slot {n : Nat} : Query n → Fin n
  | .read i | .known _ i _ => i

def Query.map {n m : Nat} (ρ : Fin n → Fin m) : Query n → Query m
  | .read i => .read (ρ i)
  | .known tag i dead => .known tag (ρ i) (ρ dead)

def Query.term {n : Nat} : Query n → Tm signature.Instr
  | .read i => .var i.val
  | .known false i dead => .case (.inl (.var i.val)) (.var 0) (.var (dead.val + 1))
  | .known true i dead => .case (.inr (.var i.val)) (.var (dead.val + 1)) (.var 0)

/-- A source with `k` ordered Bit exits and `n` live Bits. A term producer
is a single-exit source. A request's tagged result is consumed by the
two arms, which bind its actual Bit payload at slot zero. -/
inductive Code : Nat → Nat → Type where
  | ret {k n : Nat} (exit : Fin k) (slot : Fin n) : Code k n
  | letUnit {k n : Nat} (body : Code k n) : Code k n
  | letBit {k n : Nat} (arg : Code 1 n) (body : Code k (n + 1)) : Code k n
  | ask {k n : Nat} (label : Bool) (query : Query n) (left right : Code k (n + 1)) : Code k n

/-- Capture maps can alias slots after a let forwards an old value. -/
def push {n m : Nat} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (Fin.succ ∘ ρ)

def request {m : Nat} (label : Bool) (q : Query m) : Tm signature.Instr :=
  .op (.ask label) q.term

/-- The term spelling is used only for single-exit let producers. -/
def Code.term : {k n m : Nat} → Code k n → (Fin n → Fin m) → Tm signature.Instr
  | _, _, _, .ret _ i, ρ => .var (ρ i).val
  | _, _, _, .letUnit b, ρ => .let₁ .unit ((b.term ρ).rename Nat.succ)
  | _, _, _, .letBit a b, ρ => .let₁ (a.term ρ) (b.term (push ρ))
  | _, _, _, .ask label i l r, ρ =>
    .case (request label (i.map ρ)) (l.term (push ρ)) (r.term (push ρ))

/-- The literal block-free region, including term cases and lets inside
the producer of a Bit bind. -/
def Code.region : {k n m : Nat} → Code k n → (Fin n → Fin m) → Region signature.Instr
  | _, _, _, .ret out i, ρ => .br out.val (.var (ρ i).val)
  | _, _, _, .letUnit b, ρ => .let₁ .unit ((b.region ρ).renameVars Nat.succ)
  | _, _, _, .letBit a b, ρ => .let₁ (a.term ρ) (b.region (push ρ))
  | _, _, _, .ask label i l r, ρ =>
    .case (request label (i.map ρ)) (l.region (push ρ)) (r.region (push ρ))

/-- A request schedule before the two ordered outward exits are packed. -/
inductive Normal (k : Nat) : Nat → Type where
  | ret {n : Nat} (exit : Fin k) (slot : Fin n) : Normal k n
  | ask {n : Nat} (label : Bool) (query : Fin n) (left right : Normal k (n + 1)) : Normal k n

def Normal.region {k : Nat} : {n : Nat} → Normal k n → Region signature.Instr
  | _, .ret out i => .br out.val (.var i.val)
  | _, .ask label i l r => .case (request label (.read i)) l.region r.region

/-- Each continuation receives both the retained-slot map and the actual
slot returned on that path. Only a request extends the physical context. -/
def Normal.bind {k : Nat} : {n : Nat} → Normal 1 n →
    (∀ m, (Fin n → Fin m) → Fin m → Normal k m) → Normal k n
  | n, .ret _ i, next => next n id i
  | _, .ask label i l r, next =>
    .ask label i
      (l.bind (fun m ρ payload => next m (ρ ∘ Fin.succ) payload))
      (r.bind (fun m ρ payload => next m (ρ ∘ Fin.succ) payload))

def Code.normalize : {k n : Nat} → (c : Code k n) → {m : Nat} → (Fin n → Fin m) → Normal k m
  | _, _, .ret out i, _, ρ => .ret out (ρ i)
  | _, _, .letUnit b, _, ρ => b.normalize ρ
  | _, _, .letBit a b, _, ρ =>
    (a.normalize ρ).bind (fun _ captures payload => b.normalize (Fin.cases payload (captures ∘ ρ)))
  | _, _, .ask label i l r, _, ρ =>
    .ask label (ρ i.slot) (l.normalize (push ρ)) (r.normalize (push ρ))
termination_by structural _ _ c _ _ => c

def Normal.tree : {n : Nat} → Normal 2 n → Tree n
  | _, .ret out i => .ret (out.val == 1) i
  | _, .ask label i l r => .ask label (.read i) l.tree r.tree

abbrev Program := Code 2 1

def Program.written (p : Program) := Code.region p id

def Program.tree (p : Program) := (p.normalize id).tree

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive
