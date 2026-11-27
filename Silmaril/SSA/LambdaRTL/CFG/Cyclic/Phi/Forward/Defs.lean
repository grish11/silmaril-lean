module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Defs

/-! # Forwarding registers through φ rows

A block of a φ graph may read a register that an earlier block defined.
The lowering of φ graphs carries such a register in a record on every
edge, starting at the entry, where it is not yet defined.

This is a normalization of the φ graph that runs before the lowering. A
table lists, for each block, the registers that the block is to receive
explicitly. For each of them the block gets one more φ row. Its
destination is a copy of the register that belongs to the block, and its
operand on the edge from a predecessor is the register as the predecessor
reads it: the predecessor's own copy if it has one, the register itself
otherwise. The block then reads its copy.

The original registers keep their definitions, so the normalized graph
runs like the original graph. The names of the normalized graph are the
original registers and the copies.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward

universe v w

variable {V K : Type w} {F : Type v}

/-- A name of the normalized graph: an original register, or the copy of a
register that belongs to a block. -/
abbrev Name (V K : Type w) := V ⊕ V × K

/-- The registers that each block receives through φ rows. A block that is
not listed receives none. -/
abbrev Table (V K : Type w) := List (K × List V)

variable [DecidableEq K]

/-- The registers that a block receives. -/
def Table.received (table : Table V K) (key : K) : List V :=
  (table.lookup key).getD []

variable [DecidableEq V]

/-- How the entry or a block reads a register: a block reads its copy of a
register that it receives; every other read is of the register itself. -/
def reader (table : Table V K) : Option K → V → Name V K
  | none, register => .inl register
  | some key, register =>
    if register ∈ table.received key then .inr (register, key) else .inl register

omit [DecidableEq K] [DecidableEq V] in
/-- Rename the reads of a terminator. Its binders are original registers. -/
def term (read : V → Name V K) : Term V (Option K) F → Term (Name V K) (Option K) F
  | .br target value => .br target (value.rename read)
  | .case operand x left y right =>
    .case (operand.rename read) (.inl x) (term read left) (.inl y) (term read right)

omit [DecidableEq K] [DecidableEq V] in
/-- Rename the reads of a body. Its binders are original registers. -/
def body (read : V → Name V K) : Body V (Option K) F → Body (Name V K) (Option K) F
  | .let1 x operand next => .let1 (.inl x) (operand.rename read) (body read next)
  | .let2 x y operand next => .let2 (.inl x) (.inl y) (operand.rename read) (body read next)
  | .term tail => .term (term read tail)

/-- An original φ row: each operand is read as its predecessor reads it. -/
def row (table : Table V K) (source : Row V K) : Row (Name V K) K :=
  ⟨.inl source.dst, source.incoming.map fun (pred, value) =>
    (pred, value.rename (reader table pred))⟩

/-- The φ row that gives a block its copy of a register, with one operand
for each predecessor. -/
def copyRow (table : Table V K) (predecessors : List (Option K)) (key : K) (register : V) :
    Row (Name V K) K :=
  ⟨.inr (register, key), predecessors.map fun pred => (pred, .var (reader table pred register))⟩

/-- A block of the normalized graph: its original rows, then one row for
each register it receives, then its body reading the copies. -/
def block (table : Table V K) (graph : Graph V K F) (key : K) (source : Block V K F) :
    Block (Name V K) K F :=
  ⟨source.rows.map (row table) ++
      (table.received key).map (copyRow table (graph.predecessors key) key),
    body (reader table (some key)) source.body⟩

/-- The normalized graph. The entry and the order and labels of the blocks
are kept. -/
def forward (graph : Graph V K F) (table : Table V K) : Graph (Name V K) K F :=
  ⟨body .inl graph.entry, graph.blocks.map fun (key, source) =>
    (key, block table graph key source)⟩

/-- The side condition of the normalization: no block defines, in a φ row
or in its body, a register that it receives. -/
def check (graph : Graph V K F) (table : Table V K) : Bool :=
  graph.blocks.all fun (key, source) =>
    (table.received key).all fun register =>
      !(source.rows.map Row.dst ++ GlobalSSA.bodyDefinitions source.body).contains register

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Forward
