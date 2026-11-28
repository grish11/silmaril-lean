module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Thms

/-! # From a delimited flat graph to a checked captured table

`CheckedTable.toFlat` writes a checked captured table as a scoped flat
graph. This is a translation in the other direction, for a delimited
fragment of the scoped flat graphs, on the existing typed witness of a
flat graph.

A flat block is in the fragment when it is a row: a line of lets that ends
in one jump, or a line of lets that ends in one case whose two arms are
lines of lets ending in one jump. A line becomes a jump row. Its operand
is the lets around the jump argument, as one term. A case becomes a case
row. Its operand is the lets around the case, with each arm wrapped in the
injection of its side, so that it computes the packet of the arm it
selects. The entry is a line that jumps to the first block; it becomes the
entry operand.

The captured context, the block parameters, the order of the blocks and
the ordered exits are kept. A jump to a block is a local target at the
same index, and a jump to an exit is the exit at the same position.

A block with a case inside an arm of a case, or with lets after a nested
case, is not a row, and the translation is not defined on it.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open SSA.FiniteSum (append)
open Positional.Capture.Reverse (CheckedTable)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {labels blocks exits n m : Nat} {β : BoundCtx τ n} {γ : BoundCtx τ m}
  {L : Fin labels → τ} {R : Fin blocks → τ} {D : Fin exits → τ}

/-- The labels a flat region jumps to, in order: blocks and exits. -/
def jumps : {m : Nat} → Flat Φ labels m → List (Fin labels)
  | _, .br i _ => [i]
  | _, .let₁ _ tail | _, .let₂ _ tail => jumps tail
  | _, .case _ left right => jumps left ++ jumps right

/-- The label and the operand of a line: lets that end in one jump. The
operand is the lets around the jump argument. -/
def Body.line : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ labels m} → Body Φ L γ t →
    Option ((i : Fin labels) × Operand Φ γ (L i))
  | _, _, _, .br i a => some ⟨i, a⟩
  | _, _, _, .let₁ a tail => (line tail).map fun r => ⟨r.1, ⟨.let₁ a.1 r.2.1, .let₁ a.2 r.2.2⟩⟩
  | _, _, _, .let₂ a tail => (line tail).map fun r => ⟨r.1, ⟨.let₂ a.1 r.2.1, .let₂ a.2 r.2.2⟩⟩
  | _, _, _, .case _ _ _ => none

/-- The two labels and the operand of a fork: lets that end in one case
whose arms are lines. The operand is the lets around the case, with each
arm wrapped in the injection of its side. -/
def Body.fork : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ labels m} → Body Φ L γ t →
    Option ((i : Fin labels) × (j : Fin labels) × Operand Φ γ (coprod (L i) (L j)))
  | _, _, _, .br _ _ => none
  | _, _, _, .let₁ a tail =>
    (fork tail).map fun r => ⟨r.1, r.2.1, ⟨.let₁ a.1 r.2.2.1, .let₁ a.2 r.2.2.2⟩⟩
  | _, _, _, .let₂ a tail =>
    (fork tail).map fun r => ⟨r.1, r.2.1, ⟨.let₂ a.1 r.2.2.1, .let₂ a.2 r.2.2.2⟩⟩
  | _, _, _, .case e left right =>
    (line left).bind fun l => (line right).map fun r =>
      ⟨l.1, r.1, ⟨.case e.1 (.inl l.2.1) (.inr r.2.1), .case e.2 (.inl l.2.2) (.inr r.2.2)⟩⟩

/-- The target of a label: a block at its index, or an exit at its
position. -/
def labelTarget (R : Fin blocks → τ) (D : Fin exits → τ) (i : Fin (blocks + exits)) :
    Positional.Capture.Target R (List.ofFn D) (append R D i) :=
  Fin.addCases (motive := fun i => Positional.Capture.Target R (List.ofFn D) (append R D i))
    (fun j => cast (congrArg (Positional.Capture.Target R (List.ofFn D))
      (SSA.FiniteSum.append_left R D j).symm) (.local j))
    (fun e => .exit (i := e.val)
      ((SSA.FiniteSum.at_ofFn D e).trans (congrArg some (SSA.FiniteSum.append_right R D e).symm))) i

/-- The row of a flat block: a jump row for a line, a case row for a fork,
and nothing otherwise. -/
def Body.row {P : τ} {t : Flat Φ (blocks + exits) (n + 1)} (b : Body Φ (append R D) (β.snoc P) t) :
    Option (Positional.Capture.Block Φ β R (List.ofFn D) P) :=
  match b.line with
  | some r => some (.jump r.2 (labelTarget R D r.1))
  | none => b.fork.map fun r => .case r.2.2 (labelTarget R D r.1) (labelTarget R D r.2.1)

variable {size : Nat} {R : Fin (size + 1) → τ} {g : FiniteCFG Φ (size + 1) exits n}

/-- The entry operand of a witnessed flat graph whose entry is a line that
jumps to the first block. -/
def Witness.entryOperand (w : Witness g β R D) : Option (Operand Φ β (R 0)) :=
  w.entry.line.bind fun r =>
    if h : r.1 = Fin.castAdd exits 0 then
      some (cast (congrArg (Operand Φ β)
        ((congrArg (append R D) h).trans (SSA.FiniteSum.append_left R D 0))) r.2)
    else none

/-- A witnessed flat graph is in the fragment when every block is a row
and the entry is a line that jumps to the first block. -/
structure Witness.Delimited (w : Witness g β R D) : Prop where
  /-- Every block is a row. -/
  rows : ∀ i, (w.block i).row.isSome = true
  /-- The entry is a line that jumps to the first block. -/
  entry : w.entryOperand.isSome = true

/-- The table of a witnessed flat graph in the fragment: the rows of its
blocks, in order, over the same captured context and ordered exits. -/
def Witness.table (w : Witness g β R D) (h : w.Delimited) :
    Positional.Capture.Table Φ β (List.ofFn D) size :=
  ⟨R, fun i => ((w.block i).row).get (h.rows i)⟩

/-- The checked table of a witnessed flat graph in the fragment, at its
first block, with the entry operand of the flat entry. -/
def Witness.checkedTable (w : Witness g β R D) (h : w.Delimited)
    (checked : (w.table h).check = true) : CheckedTable Φ β (List.ofFn D) :=
  ⟨size, w.table h, checked, w.entryOperand.get h.entry⟩

/-! ## The shape of the fragment

Whether a witnessed flat graph is in the fragment depends on the flat
graph only, not on the typings of its witness. The shape is a check on
the flat graph. -/

omit [TypeFormers τ] [HasTy Φ τ] in
/-- The label of a line: lets that end in one jump. -/
def lineLabel : {m : Nat} → Flat Φ labels m → Option (Fin labels)
  | _, .br i _ => some i
  | _, .let₁ _ tail | _, .let₂ _ tail => lineLabel tail
  | _, .case _ _ _ => none

omit [TypeFormers τ] [HasTy Φ τ] in
/-- Lets that end in one case whose arms are lines. -/
def forkShape : {m : Nat} → Flat Φ labels m → Bool
  | _, .br _ _ => false
  | _, .let₁ _ tail | _, .let₂ _ tail => forkShape tail
  | _, .case _ left right => (lineLabel left).isSome && (lineLabel right).isSome

omit [TypeFormers τ] [HasTy Φ τ] in
/-- Every block is a line or a fork, and the entry is a line that jumps to
the first block. -/
def delimitedShape (g : FiniteCFG Φ (size + 1) exits n) : Bool :=
  decide (lineLabel g.entry = some (Fin.castAdd exits 0)) &&
    (List.finRange (size + 1)).all fun i =>
      (lineLabel (g.block i)).isSome || forkShape (g.block i)

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
