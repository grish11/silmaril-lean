module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Defs

/-! # Outline a selected computed case arm before named emission -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open LambdaSSA (FiniteCFG Flat)
open LetCase.LocallyNameless (Tm)
open SSA.FiniteSum (append)

universe u v
variable {F : Type v} {blocks exits labels n : Nat}

/-- Keep existing block indices, append one block, and move absolute
outward indices past it without changing their positions in the exit list. -/
def relocate (blocks exits : Nat) : Fin (blocks + exits) → Fin (blocks + 1 + exits) :=
  Fin.addCases (fun i => i.castSucc.castAdd exits) (Fin.natAdd (blocks + 1))

def renameLabels {newLabels : Nat} (ρ : Fin labels → Fin newLabels) :
    {m : Nat} → Flat F labels m → Flat F newLabels m
  | _, .br target arg => .br (ρ target) arg
  | _, .let₁ arg tail => .let₁ arg (renameLabels ρ tail)
  | _, .let₂ arg tail => .let₂ arg (renameLabels ρ tail)
  | _, .case discr l r => .case discr (renameLabels ρ l) (renameLabels ρ r)

inductive Side where
  | left
  | right
  deriving DecidableEq

/-- Select one of the two arms in source order. -/
def Side.choose {A : Type u} : Side → A → A → A
  | .left, l, _ => l
  | .right, _, r => r

/-- Place the selected and bypass terms in their original case positions. -/
def Side.branch (side : Side) (discr : Tm Empty F n) (active bypass : Flat F labels (n + 1)) :
    Flat F labels n :=
  .case discr (side.choose active bypass) (side.choose bypass active)

/-- The selected row begins with a case and the selected arm jumps with a
leading operand let. The bypass body retains its original syntax. -/
structure Arm (F : Type v) (labels n : Nat) where
  discr : Tm Empty F (n + 1)
  destination : Fin labels
  value : Tm Empty F (n + 2)
  tail : Tm Empty F (n + 3)
  bypass : Flat F labels (n + 2)
  side : Side := .left

def Arm.operand (a : Arm F labels n) : Tm Empty F (n + 2) := .let₁ a.value a.tail

def Arm.source (a : Arm F labels n) : Flat F labels (n + 1) :=
  a.side.branch a.discr (.br a.destination a.operand) a.bypass

structure Selection (g : FiniteCFG F blocks exits n) where
  selected : Fin blocks
  arm : Arm F (blocks + exits) n
  readback : g.block selected = arm.source

/-- Recognize the actual row structurally. No supplied row equation is
needed when the selected written row has this shape. -/
def read (g : FiniteCFG F blocks exits n) (i : Fin blocks) (side : Side := .left) : Option (Selection g) :=
  match row : g.block i with
  | .case discr left right =>
    match arm : side.choose left right with
    | .br target (.let₁ value tail) =>
      some ⟨i, ⟨discr, target, value, tail, side.choose right left, side⟩, by
        cases side <;> simp only [Side.choose] at arm <;>
          simp only [row, Arm.source, Side.branch, Side.choose, Arm.operand, arm]⟩
    | _ => none
  | _ => none

/-- The selected arm sends the original row packet and the case payload.
The bypass still jumps using only the relocated original labels. -/
def Arm.dispatch (a : Arm F (blocks + exits) n) : Flat F (blocks + 1 + exits) (n + 1) :=
  a.side.branch a.discr (.br ((Fin.last blocks).castAdd exits) (.pair (.bv 1) (.bv 0)))
    (renameLabels (relocate blocks exits) a.bypass)

/-- Decode the transferred packet before evaluating the original arm.
Weakening accounts for the new packet binder below the two projections. -/
def Arm.continuation (a : Arm F (blocks + exits) n) : Flat F (blocks + 1 + exits) (n + 1) :=
  .let₂ (.bv 0) (.br (relocate blocks exits a.destination) a.operand.underTwoBinders)

/-- Outline the selected arm. The existing materializer moves the operand
let into the fresh row's body before named emission. -/
def graph {g : FiniteCFG F blocks exits n} (s : Selection g) : FiniteCFG F (blocks + 1) exits n :=
  ⟨renameLabels (relocate blocks exits) g.entry,
    Fin.lastCases s.arm.continuation fun i =>
      if i = s.selected then s.arm.dispatch else renameLabels (relocate blocks exits) (g.block i)⟩

/-- Two successive selections, with the second read from the first
outline's actual graph. -/
structure TwoArms (g : FiniteCFG F blocks exits n) where
  first : Selection g
  second : Selection (graph first)

/-- Outline the left operand, then select the right operand on the same
old row index. Both selections refer to the written program. -/
def readBoth (g : FiniteCFG F blocks exits n) (i : Fin blocks) : Option (TwoArms g) := do
  let first ← read g i .left
  let second ← read (graph first) i.castSucc .right
  pure ⟨first, second⟩

variable {τ : Type u} [TypeFormers τ] [HasTy F τ]

/-- The fresh block receives the old block argument paired with the selected
sum payload. All old block types stay at their original indices. -/
def packets (R : Fin blocks → τ) (i : Fin blocks) (left : τ) : Fin (blocks + 1) → τ :=
  Fin.lastCases (product (R i) left) R

/-- Exact appended packet type for the selected side of the typed case. -/
def Selection.packetTypes {g : FiniteCFG F blocks exits n} (s : Selection g)
    (R : Fin blocks → τ) (left right : τ) : Fin (blocks + 1) → τ :=
  packets R s.selected (s.arm.side.choose left right)

/-- The selected syntax with its exact discriminator and two arm types. -/
structure Arm.HasType (a : Arm F labels n) (β : BoundCtx τ n) (L : Fin labels → τ)
    (packet left right : τ) : Prop where
  discr : LetCase.LocallyNameless.HasType F .nil (β.snoc packet) a.discr (coprod left right)
  active : LetCase.LocallyNameless.HasType F .nil
    ((β.snoc packet).snoc (a.side.choose left right)) a.operand (L a.destination)
  bypass : a.bypass.HasType L ((β.snoc packet).snoc (a.side.choose right left))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
