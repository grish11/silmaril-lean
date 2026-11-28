module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Defs

/-! # Finite feedback with heterogeneous visible requests -/

@[expose] public section

open Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

/-- Each opcode of the fixed finite family has its own argument and reply code. -/
structure Family (n : Nat) where
  argument : Fin n → Code
  reply : Fin n → Code

structure Opcode {n : Nat} (F : Family n) where
  index : Fin n
  deriving DecidableEq

variable {n : Nat} {F : Family n} {S T B : Code}

abbrev Opcode.argCode (f : Opcode F) : Code := F.argument f.index
abbrev Opcode.replyCode (f : Opcode F) : Code := F.reply f.index

instance : HasTy (Opcode F) (Ty Unit) :=
  ⟨fun f => f.argCode.ty, fun f => f.replyCode.ty⟩

/-- A row immediately returns or makes one typed request. After a reply it
either returns or selects the next state. -/
inductive Row (F : Family n) (S B : Code)
  | ret (value : B.Value)
  | call (op : Opcode F) (arg : op.argCode.Value) (next : op.replyCode.Value → B.Value ⊕ S.Value)

abbrev Table (F : Family n) (S B : Code) := S.Value → Row F S B

def Row.map (h : S.Value → T.Value) : Row F S B → Row F T B
  | .ret v => .ret v
  | .call f x k => .call f x (fun r => Sum.map id h (k r))

def Commutes (L : Table F S B) (R : Table F T B) (h : S.Value → T.Value) : Prop :=
  ∀ s, (L s).map h = R (h s)

def replySource {f : Opcode F} (next : f.replyCode.Value → B.Value ⊕ S.Value) : Expr (Opcode F) :=
  f.replyCode.dispatch (fun r => (Code.sum B S).literal (next r)) (.var 0)

def Row.source : Row F S B → Expr (Opcode F)
  | .ret v => .inl (B.literal v)
  | .call f x k => .let₁ (.op f (f.argCode.literal x)) (replySource k)

def Table.source (M : Table F S B) : Expr (Opcode F) :=
  S.dispatch (fun s => (M s).source) (.var 0)

/-- The tree events retain the full dependent pair of opcode and arguments.
In the step result, only return and next-state constructor values are raised. -/
def Row.step : Row F S B → ITree.Tree (Event (Φ := Opcode F) carriers) (B.Large ⊕ S.Large)
  | .ret v => ITree.ret (.inl (B.raise v))
  | .call f x k => ITree.vis (.call f x) (fun r => ITree.ret (Sum.map B.raise S.raise (k r)))

def Table.step (M : Table F S B) (s : S.Large) :
    ITree.Tree (Event (Φ := Opcode F) carriers) (B.Large ⊕ S.Large) :=
  (M (S.raise.symm s)).step

noncomputable def Table.run (M : Table F S B) (s : S.Value) :
    ITree.Tree (Event (Φ := Opcode F) carriers) B.Large :=
  Silmaril.Elgot.iter M.step (S.raise s)

/-- Joint reachability follows the same opcode, argument and reply at each
repeat. Immediate returns and returning replies have no outgoing edge. -/
inductive PairedReach (L : Table F S B) (R : Table F T B) (s₀ : S.Value) (t₀ : T.Value) :
    S.Value × T.Value → Prop
  | initial : PairedReach L R s₀ t₀ (s₀, t₀)
  | after_reply {s s' : S.Value} {t t' : T.Value} (reach : PairedReach L R s₀ t₀ (s, t))
      (f : Opcode F) (x : f.argCode.Value) (r : f.replyCode.Value)
      (k : f.replyCode.Value → B.Value ⊕ S.Value) (j : f.replyCode.Value → B.Value ⊕ T.Value)
      (left : L s = .call f x k) (right : R t = .call f x j)
      (nextL : k r = .inr s') (nextR : j r = .inr t') :
      PairedReach L R s₀ t₀ (s', t')

/-- For paired reachable requests with the same typed head, both reply
continuations make the same return-or-repeat choice. A return and a repeat
to an immediate return can have equal weak observations. -/
def ReplyAligned (L : Table F S B) (R : Table F T B) (s₀ : S.Value) (t₀ : T.Value) : Prop :=
  ∀ {s t}, PairedReach L R s₀ t₀ (s, t) →
    ∀ {f : Opcode F} {x : f.argCode.Value}
      {k : f.replyCode.Value → B.Value ⊕ S.Value} {j : f.replyCode.Value → B.Value ⊕ T.Value},
    L s = .call f x k → R t = .call f x j → ∀ r,
      (k r).isLeft = (j r).isLeft

/-- Every repeat leads to a visible request row. Immediate returns may still
be used as initial states. -/
def Guarded (M : Table F S B) : Prop :=
  ∀ {s s'} {f : Opcode F} {x : f.argCode.Value} {k : f.replyCode.Value → B.Value ⊕ S.Value},
    M s = .call f x k → ∀ r, k r = .inr s' →
    ∃ (g : Opcode F) (y : g.argCode.Value) (j : g.replyCode.Value → B.Value ⊕ S.Value), M s' = .call g y j

/-- A shared table on exactly the reachable state pairs. -/
structure Cover (L : Table F S B) (R : Table F T B) (s : S.Value) (t : T.Value) where
  code : Code
  decode : code.Value ≃ {p // PairedReach L R s t p}
  table : Table F code B
  left_commutes : Commutes table L (fun v => (decode v).val.1)
  right_commutes : Commutes table R (fun v => (decode v).val.2)

def Cover.initial {L : Table F S B} {R : Table F T B} {s : S.Value} {t : T.Value}
    (C : Cover L R s t) : C.code.Value :=
  C.decode.symm ⟨(s, t), .initial⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
