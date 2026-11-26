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

/-- The selected row begins with a case whose left arm is a jump with a
leading operand let. The bypass body retains its original syntax. -/
structure Arm (F : Type v) (labels n : Nat) where
  discr : Tm Empty F (n + 1)
  destination : Fin labels
  value : Tm Empty F (n + 2)
  tail : Tm Empty F (n + 3)
  bypass : Flat F labels (n + 2)

def Arm.operand (a : Arm F labels n) : Tm Empty F (n + 2) := .let₁ a.value a.tail

def Arm.source (a : Arm F labels n) : Flat F labels (n + 1) :=
  .case a.discr (.br a.destination a.operand) a.bypass

structure Selection (g : FiniteCFG F blocks exits n) where
  selected : Fin blocks
  arm : Arm F (blocks + exits) n
  readback : g.block selected = arm.source

/-- Recognize the actual row structurally. No supplied row equation is
needed when the selected written row has this shape. -/
def read (g : FiniteCFG F blocks exits n) (i : Fin blocks) : Option (Selection g) :=
  match eq : g.block i with
  | .case discr (.br target (.let₁ value tail)) bypass =>
    some ⟨i, ⟨discr, target, value, tail, bypass⟩, eq⟩
  | _ => none

/-- The selected arm sends the original row packet and the case payload.
The bypass still jumps using only the relocated original labels. -/
def Arm.dispatch (a : Arm F (blocks + exits) n) : Flat F (blocks + 1 + exits) (n + 1) :=
  .case a.discr (.br ((Fin.last blocks).castAdd exits) (.pair (.bv 1) (.bv 0)))
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

variable {τ : Type u} [TypeFormers τ] [HasTy F τ]

/-- The fresh block receives the old block argument paired with the left
sum payload. All old block types stay at their original indices. -/
def packets (R : Fin blocks → τ) (i : Fin blocks) (left : τ) : Fin (blocks + 1) → τ :=
  Fin.lastCases (product (R i) left) R

/-- The selected syntax with its exact discriminator and two arm types. -/
structure Arm.HasType (a : Arm F labels n) (β : BoundCtx τ n) (L : Fin labels → τ)
    (packet left right : τ) : Prop where
  discr : LetCase.LocallyNameless.HasType F .nil (β.snoc packet) a.discr (coprod left right)
  active : LetCase.LocallyNameless.HasType F .nil ((β.snoc packet).snoc left) a.operand (L a.destination)
  bypass : a.bypass.HasType L ((β.snoc packet).snoc right)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
