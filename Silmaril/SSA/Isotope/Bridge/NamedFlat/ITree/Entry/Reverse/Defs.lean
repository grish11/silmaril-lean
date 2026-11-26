module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Defs

/-! # Lower a scoped flat CFG to ordinary named mutable RTL -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LetCase.LocallyNameless (Tm)

-- Keep structural equality with the exact readback checker.
deriving instance DecidableEq for Flat

universe u v w

variable {V K : Type w} {F : Type v} {n blocks exits labels : Nat}

/-- Each body starts afresh at local index zero. Register names can therefore
be reused across edges. The block parameter stores the whole incoming packet. -/
structure Registers (V : Type w) where
  parameter : V
  localAt : Nat → V

def lowerValue (names : Fin n → Option V) : Tm Empty F n → Option (Val V)
  | .bv i => (names i).map .var
  | .unit => some .unit
  | .pair l r => (lowerValue names l).bind fun a => (lowerValue names r).map (.pair a)
  | _ => none

def lowerOperand (names : Fin n → Option V) : Tm Empty F n → Option (Op V F)
  | .op f a => (lowerValue names a).map (.app f)
  | a => (lowerValue names a).map .val

/-- Named case arms are terminators. Mutually exclusive arms can use the
same register for their separately scoped binding at the current depth.
External branches retain only the old payload so the checker can reconstruct
the ordered live-out record from register reads. -/
def lowerTerm (registers : Registers V) (target : Fin labels → K)
    (internal : Fin labels → Bool) {n : Nat} (names : Fin n → Option V) (next : Nat) :
    Flat F labels n → Option (CFG.Term V K F)
  | .br i a =>
      let value : Option (Val V) := if internal i then lowerValue names a else
        match a with
        | .pair old _ => lowerValue names old
        | _ => none
      value.map (.br (target i))
  | .case a l r => do
      let discr ← lowerOperand names a
      let x := registers.localAt next
      let scope := Fin.cases (some x) names
      let left ← lowerTerm registers target internal scope (next + 1) l
      let right ← lowerTerm registers target internal scope (next + 1) r
      pure (.case discr x left x right)
  | .let₁ .. | .let₂ .. => none

/-- Lower the let prefix and its final jump or case. A product RHS is
evaluated into a packet before either destination register is assigned. -/
def lowerBody (registers : Registers V) (target : Fin labels → K)
    (internal : Fin labels → Bool) {n : Nat} (names : Fin n → Option V) (next : Nat) :
    Flat F labels n → Option (CFG.Body V K F)
  | .let₁ a b => do
      let value ← lowerOperand names a
      let x := registers.localAt next
      let tail ← lowerBody registers target internal (Fin.cases (some x) names) (next + 1) b
      pure (.let1 x value tail)
  | .let₂ a b => do
      let value ← lowerOperand names a
      let x := registers.localAt next
      let y := registers.localAt (next + 1)
      let tail ← lowerBody registers target internal
        (Fin.cases (some y) (Fin.cases (some x) names)) (next + 2) b
      pure (.let2 x y value tail)
  | tail => (lowerTerm registers target internal names next tail).map .term

/-- Named blocks may read only the incoming packet and their local writes.
The shared open context remains available in the entry. -/
def lower (registers : Registers V) (inputs : Fin n → V)
    (internal : Fin blocks → K) (external : Fin exits → K)
    (code : FiniteCFG F blocks exits n) : Option (CFG V K F) := do
  let target := SSA.FiniteSum.append internal external
  let isInternal := SSA.FiniteSum.append (fun _ : Fin blocks => true)
    (fun _ : Fin exits => false)
  let entry ← lowerBody registers target isInternal (some ∘ inputs) 0 code.entry
  let bodies ← tabulate blocks fun i =>
    lowerBody registers target isInternal (Fin.cases (some registers.parameter) (fun _ => none))
      0 (code.block i)
  pure ⟨entry, List.ofFn fun i => (internal i, ⟨registers.parameter, bodies i⟩)⟩

/-- Compare exactly the written entry and all written block bodies. -/
local instance [DecidableEq F] : DecidableEq (FiniteCFG F blocks exits n) := fun a b =>
  if h : a.entry = b.entry ∧ ∀ i, a.block i = b.block i then
    isTrue (by cases a; cases b; obtain ⟨rfl, h⟩ := h; cases funext h; rfl)
  else isFalse (fun eq => h (eq ▸ ⟨rfl, fun _ => rfl⟩))

variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} (I : Interface κ V K)
  (fields : K → List (V × Ty κ))

/-- Check the exact typed source syntax by ordinary named readback, after
attaching reads of the selected registers to external branches. -/
def withLiveOut (source : CFG V K P.Instr) : CFG V K P.Instr :=
  CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source

/-- Acceptance of the reverse lowering before reversion. The attached
named table has no ambient block reads and reads back to the original
flat table, including the ordered exit payloads. -/
structure Lowered (code : FiniteCFG P.Instr blocks I.exits.length I.slots) where
  source : CFG V K P.Instr
  closed : CFG.Cyclic.RoundTrip.PacketClosed (withLiveOut (P := P) fields source)
  count : (withLiveOut (P := P) fields source).blocks.length = blocks
  readback : elaborateAt (withLiveOut (P := P) fields source) I.exits I.names blocks count = some code

/-- Run the reverse lowerer and certify its actual output. The exact
readback rejects any used name collision or exit projection that changes
the scoped table. -/
def lowerChecked [DecidableEq P.Instr] (registers : Registers V)
    (internal : Fin blocks → K) (code : FiniteCFG P.Instr blocks I.exits.length I.slots) :
    Option (Lowered I fields code) := do
  let source ← lower registers I.names internal (fun i => I.exits[i]) code
  let attached := withLiveOut (P := P) fields source
  if count : attached.blocks.length = blocks then
    if closed : ∀ i : Fin attached.blocks.length,
        attached.blocks[i].2.body.toRegion.fv ⊆ {attached.blocks[i].2.param} then
      if readback : elaborateAt attached I.exits I.names blocks count = some code then
        some ⟨source, by
          intro item mem
          obtain ⟨i, hi, eq⟩ := List.getElem_of_mem mem
          rw [← eq]
          exact closed ⟨i, hi⟩, count, readback⟩
      else none
    else none
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
