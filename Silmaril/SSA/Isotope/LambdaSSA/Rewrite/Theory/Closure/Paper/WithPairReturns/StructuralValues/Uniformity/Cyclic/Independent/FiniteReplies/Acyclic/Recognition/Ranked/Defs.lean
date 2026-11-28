module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Thms

/-! # Recognizing ranked native reply tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA

variable {Φ : Type} [Profile Φ] {n : Nat}

/-- The precise Paper equation needed to run a request before resolving
local transfers. The Boolean is the executable part of the policy. -/
structure RequestPolicy (Φ : Type) [Profile Φ] (n : Nat) where
  enabled : Bool
  move : enabled = true → CfgEta.EntryLet (Paper.Eqv (τ := Ty Atom) (Φ := Φ)) n

/-- The existing native rules supply entry-let sequencing at arities zero and one. -/
def nativeRequestPolicy (Φ : Type) [Profile Φ] (n : Nat) : RequestPolicy Φ n where
  enabled := decide (n ≤ 1)
  move h := fun R ha hd hb => .cfgEta (CfgEta.entryLet_of_le_one (of_decide_eq_true h) R ha hd hb)

/-- Enable requests in a larger flat table when its entry-let equation is proved in Paper. -/
def RequestPolicy.ofEntryLet (law : CfgEta.EntryLet (Paper.Eqv (τ := Ty Atom) (Φ := Φ)) n) :
    RequestPolicy Φ n := ⟨true, fun _ => law⟩

/-- A packet-local row can dispatch on its packet, forward it to a local block,
or execute outward-only control. A request before routing carries the
entry-let law for the surrounding table. -/
inductive Block (R : Fin n → ReplyShape) (t : ReplyShape) : ReplyShape → Type where
  | jump {s : ReplyShape} (j : Fin n) (hs : R j = s) : Block R t s
  | exit {s : ReplyShape} (p : Control Φ s t) : Block R t s
  | case {l r : ReplyShape} (left : Block R t l) (right : Block R t r) : Block R t (.sum l r)
  | request (op : Φ) (move : CfgEta.EntryLet (Paper.Eqv (τ := Ty Atom) (Φ := Φ)) n)
      (body : Block R t (Profile.reply op)) : Block R t .unit

def Block.region {R : Fin n → ReplyShape} {s t : ReplyShape} : Block (Φ := Φ) R t s → Region Φ
  | .jump j _ => .br j (.var 0)
  | .exit p => p.region.renameLabels (fun j => n + j)
  | .case l r => .case (.var 0) l.region r.region
  | .request op _ body => .let₁ (.op op (.var 0)) body.region

/-- A branch retains the raw label index and must forward the live slot. -/
def destination (R : Fin n → ReplyShape) (s : ReplyShape) :
    Region Φ → Option {j : Fin n // R j = s}
  | .br j (.var 0) =>
      if hj : j < n then
        if hs : R ⟨j, hj⟩ = s then some ⟨⟨j, hj⟩, hs⟩ else none
      else none
  | _ => none

def proposeWith (R : Fin n → ReplyShape) (allowed : Fin n → Bool) (t : ReplyShape)
    (policy : RequestPolicy Φ n) :
    (s : ReplyShape) → Region Φ → Option (Block (Φ := Φ) R t s)
  | .sum l r, .case (.var 0) left right => do
      let pl ← proposeWith R allowed t policy l left
      let pr ← proposeWith R allowed t policy r right
      some (.case pl pr)
  | .unit, raw@(.let₁ (.op op (.var 0)) body) =>
      if h : policy.enabled then
        (proposeWith R allowed t policy (Profile.reply op) body).map (.request op (policy.move h))
      else (propose .unit t n raw).map Block.exit
  | s, raw =>
      match destination R s raw with
      | some ⟨j, hs⟩ => if allowed j then some (.jump j hs) else none
      | none => (propose s t n raw).map Block.exit

def proposeBlock (R : Fin n → ReplyShape) (allowed : Fin n → Bool) (t s : ReplyShape)
    (r : Region Φ) (policy : RequestPolicy Φ n := nativeRequestPolicy Φ n) :
    Option (Block (Φ := Φ) R t s) :=
  proposeWith R allowed t policy s r

variable [DecidableEq Φ]

/-- Compare with a singleton-input re-emission. Every reference in the
re-emitted block is bound locally or is the block packet. -/
def checkBlock (R : Fin n → ReplyShape) (allowed : Fin n → Bool) (s t : ReplyShape)
    (r : Region Φ) (policy : RequestPolicy Φ n := nativeRequestPolicy Φ n) :
    Option (Block (Φ := Φ) R t s) := do
  let b ← proposeBlock R allowed t s r policy
  if sameBody r b.region then some b else none

def collect (R : Fin n → ReplyShape) (rank : Fin n → Nat) (t : ReplyShape)
    (raw : Fin n → Region Φ) (policy : RequestPolicy Φ n := nativeRequestPolicy Φ n) :
    Option ((i : Fin n) → Block (Φ := Φ) R t (R i)) :=
  let result := fun i => checkBlock R (fun j => decide (rank j < rank i)) (R i) t (raw i) policy
  if h : ∀ i, (result i).isSome then some (fun i => (result i).get (h i)) else none

/-- Inline already-resolved destinations under structural packet cases. -/
def Block.inline {R : Fin n → ReplyShape} {s t : ReplyShape}
    (next : (i : Fin n) → Option (Control Φ (R i) t)) :
    Block (Φ := Φ) R t s → Option (Control Φ s t)
  | .jump j hs => (next j).map (fun p => hs ▸ p)
  | .exit p => some p
  | .case l r => do
      let pl ← l.inline next
      let pr ← r.inline next
      some (.case pl pr)
  | .request op _ body => (body.inline next).map (.let₁ (.call op))

/-- Resolve checked destinations. The executable caller supplies one more
than the destination rank as fuel. -/
def follow {R : Fin n → ReplyShape} {t : ReplyShape}
    (blocks : (i : Fin n) → Block (Φ := Φ) R t (R i)) :
    Nat → (i : Fin n) → Option (Control Φ (R i) t)
  | 0, _ => none
  | fuel + 1, i => (blocks i).inline (follow blocks fuel)

def runEntry {R : Fin n → ReplyShape} {t : ReplyShape} (rank : Fin n → Nat)
    (blocks : (i : Fin n) → Block (Φ := Φ) R t (R i)) (s : ReplyShape) (entry : Region Φ)
    (policy : RequestPolicy Φ n := nativeRequestPolicy Φ n) : Option (Control Φ s t) := do
  let b ← checkBlock R (fun _ => true) s t entry policy
  b.inline (fun i => follow blocks (rank i + 1) i)

/-- Recognize a literal CFG with exactly the supplied packet profile. Every
local edge is checked, including edges in blocks unreachable from the entry.
The default request policy uses the proved zero- and one-block sequencing law. -/
def recognize (R : Fin n → ReplyShape) (rank : Fin n → Nat) (s t : ReplyShape)
    (r : Region Φ) (policy : RequestPolicy Φ n := nativeRequestPolicy Φ n) :
    Option (Control Φ s t) :=
  match r with
  | .cfg entry k raw =>
      if h : k = n then do
        let blocks ← collect R rank t (h ▸ raw) policy
        runEntry rank blocks s entry policy
      else none
  | _ => none

namespace Example

abbrev Op := Recognition.Example.Op
abbrev Reply := Recognition.Example.Reply

def packets (i : Fin 4) : ReplyShape :=
  match i.val with
  | 0 => Reply
  | _ => .unit

def rank (i : Fin 4) : Nat := 3 - i.val

def blocks (last : Region Op) (i : Fin 4) : Region Op :=
  match i.val with
  | 0 => .case (.var 0) (.br 1 (.var 0)) (.br 2 (.var 0))
  | 1 | 2 => .br 3 (.var 0)
  | _ => last

def graph (last : Region Op) : Region Op := .cfg (.br 0 (.var 0)) 4 (blocks last)

/-- Both branches of the first block reach the one written request block. -/
def accepted : Region Op := graph (.let₁ (.op .read (.var 0)) (.br 4 (.var 0)))

/-- Returning from the last block to block one makes a cycle. -/
def backEdge : Region Op := graph (.br 1 (.var 0))

/-- The exit has the right type but reads the ambient input rather than the block packet. -/
def captured : Region Op := graph (.br 4 (.var 1))

def expected : Control Op Reply Reply :=
  let request := Control.let₁ (.call .read) (.forward Reply)
  .case request request

end Example

namespace RequestExample

abbrev Op := Recognition.Example.Op

def packets (_ : Fin 1) : ReplyShape := .unit

def rank (_ : Fin 1) : Nat := 0

/-- Read a two-tag reply and pass the selected payload to label `j`. -/
def choose (j : Nat) : Region Op := .case (.var 0) (.br j (.var 0)) (.br j (.var 0))

def route (j : Nat) : Region Op := .let₁ (.op .read (.var 0)) (choose j)

def downstream (out : Nat) : Region Op := .let₁ (.op .tick (.var 0)) (.br out (.var 0))

def graph (next : Region Op) : Region Op := .cfg (route 0) 1 (fun _ => next)

def accepted : Region Op := graph (downstream 1)

def backEdge : Region Op := graph (.br 0 (.var 0))

def captured : Region Op := graph (.br 1 (.var 1))

def expected : Control Op .unit .unit :=
  let tick := Control.let₁ (.call .tick) (.forward .unit)
  .let₁ (.call .read) (.case tick tick)

def expectedRow : Row Op (ReplyShape.unit.Value) :=
  .call .read (fun _ => .call .tick Row.leaf)

def flatBlocks : Fin 2 → Region Op := Fin.cases (route 1) (fun _ => downstream 2)

/-- Put the request in a local block of a two-label flat table. -/
def flat : Region Op := .cfg (.br 0 (.var 0)) 2 flatBlocks

def flatPackets (_ : Fin 2) : ReplyShape := .unit

def flatRank (i : Fin 2) : Nat := 1 - i.val

/-- The original table after entering its first block. -/
def flatEntered : Region Op := .cfg (route 1) 2 flatBlocks

/-- The request runs ahead of the same table, followed by its reply selection. -/
def flatMoved : Region Op := .let₁ (.op .read (.var 0)) (.cfg (choose 1) 2 flatBlocks)

end RequestExample

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked
