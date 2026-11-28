module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Defs

/-! # Executable recognition of a native two-block reply case -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)

variable {Φ : Type} [Profile Φ]

/-- Recover a forwarded constructor path from the known exact output shape. -/
def path (s t : ReplyShape) : Tm Φ → Option (Control Φ s t)
  | .var 0 => if h : s = t then some (h ▸ .forward s) else none
  | .inl a => match t with
    | .sum l r => (path s l a).map (fun p => .let₁ p (.inl l r))
    | _ => none
  | .inr a => match t with
    | .sum l r => (path s r a).map (fun p => .let₁ p (.inr l r))
    | _ => none
  | _ => none

/-- Propose control for an outward-only body. The final syntax check verifies
the variable bindings and label indices after re-emitting the control. -/
def propose (s t : ReplyShape) (exit : Nat) : Region Φ → Option (Control Φ s t)
  | .br ℓ a => if ℓ = exit then path s t a else none
  | .let₁ (.op p (.var 0)) body => match s with
    | .unit => (propose (Profile.reply p) t exit body).map (.let₁ (.call p))
    | _ => none
  | .case (.var 0) left right => match s with
    | .sum l r => Control.case <$> propose l t exit left <*> propose r t exit right
    | _ => none
  | .let₁ (.abort (.var 0)) (.br ℓ (.var 0)) => match s with
    | .empty => if ℓ = exit then some (.empty t) else none
    | _ => none
  | _ => none

variable [DecidableEq Φ]

/-- A decidable equality check for the CFG-free syntax used by the recognizer. -/
def sameBody : Region Φ → Region Φ → Bool
  | .br i a, .br j b => decide (i = j) && decide (a = b)
  | .let₁ a r, .let₁ b s => decide (a = b) && sameBody r s
  | .case a l r, .case b l' r' => decide (a = b) && sameBody l l' && sameBody r r'
  | _, _ => false

def caseEntry (index : Nat) : Region Φ :=
  .case (.var index) (.br 0 (.var 0)) (.br 1 (.var 0))

/-- A table arm is in the case-payload slot and exits at label two. -/
def arm (ρ : Nat → Nat) {s t : ReplyShape} (p : Control Φ s t) : Region Φ :=
  ((p.region.renameVars (lift Nat.succ)).renameVars (lift ρ)).renameLabels (fun j => 2 + j)

def recognizeArm (s t : ReplyShape) (ρ : Nat → Nat) (r : Region Φ) : Option (Control Φ s t) := do
  let p ← propose s t 2 r
  if sameBody r (arm ρ p) then some p else none

/-- Recognize a two-block case table and check both arms against their
re-emitted outward-only bodies. The two local payload types come from the
exact sum input. -/
def recognizeTable (s t : ReplyShape) (ρ : Nat → Nat) : Region Φ → Option (Control Φ s t) :=
  match s with
  | .sum l r => fun raw =>
    match raw with
    | .cfg entry 2 blocks =>
        if sameBody entry (caseEntry (ρ 0)) then do
          let left ← recognizeArm l t ρ (blocks 0)
          let right ← recognizeArm r t ρ (blocks 1)
          some (.case left right)
        else none
    | _ => none
  | _ => fun _ => none

/-- Recognize a Unit-input request followed by an outward-only case table.
The opcode fixes the erased let's reply type. The caller supplies the
expected singleton output shape. -/
def recognize (t : ReplyShape) : Region Φ → Option (Control Φ .unit t)
  | .let₁ (.op p (.var 0)) body =>
      (recognizeTable (Profile.reply p) t (lift Nat.succ) body).map (.let₁ (.call p))
  | _ => none

namespace Example

inductive Op where
  | read
  | tick
  deriving DecidableEq

abbrev Reply : ReplyShape := .sum .unit .unit

instance : Profile Op where
  reply
    | .read => Reply
    | .tick => .unit

def returnRight : Region Op :=
  .let₁ (.op .tick (.var 0)) (.br 2 (.inr (.var 0)))

def graph (leftIndex : Nat) (right : Region Op) : Region Op :=
  .let₁ (.op .read (.var 0))
    (.cfg (.case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))) 2
      (Fin.cases (.br 2 (.inl (.var leftIndex))) (fun _ => right)))

def accepted : Region Op := graph 0 returnRight
def backEdge : Region Op := graph 0 (.br 1 (.var 0))
def captured : Region Op := graph 2 returnRight

def expected : Control Op .unit Reply :=
  .let₁ (.call .read) (.case
    (.let₁ (.forward .unit) (.inl .unit .unit))
    (.let₁ (.call .tick) (.let₁ (.forward .unit) (.inr .unit .unit))))

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition
