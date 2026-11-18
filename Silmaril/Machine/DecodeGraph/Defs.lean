module

public import Mathlib.Data.List.Forall2
public import Silmaril.Machine.Decoder
public import Silmaril.Semantics.Accept.Rel.Defs

/-! # Decoder graphs, block boundaries and observable rebasing

Successes live in Mathlib's complete lattice of relations, ordered by inclusion.
Lattice operations do not enforce codec laws or select between conflicting parses.
-/

@[expose] public section

namespace Silmaril.Machine.DecodeGraph

open scoped SetRel

abbrev Bytes := List (BitVec 8)

/-- One success: a decoded value and a byte count. At input `(context, bytes)`
the consumed bytes are `bytes.take count` and the remainder is `bytes.drop count`.
The graph alone does not assert that the count fits. -/
abbrev Graph (Context Value : Type*) := SetRel (Context × Bytes) (Value × Nat)

variable {Context Source Target : Type*}

/-- Forget the failure diagnostics and keep exactly the successful outcomes. -/
def successes {Error : Type*} (decode : Context → Bytes → Except Error (Source × Nat)) :
    Graph Context Source := {(input, result) | decode input.1 input.2 = .ok result}

/-- A legacy codec is independent of the added query context. -/
def ofDecoder (decoder : Decoder Source) : Graph Context Source :=
  Accept.ofPartial fun input => decoder.decode input.2

def Deterministic (graph : Graph Context Source) : Prop :=
  Relator.RightUnique (fun input result => input ~[graph] result)

def Positive (graph : Graph Context Source) : Prop :=
  ∀ ⦃ctx bytes value count⦄, ((ctx, bytes), (value, count)) ∈ graph → 0 < count

def Fits (graph : Graph Context Source) : Prop :=
  ∀ ⦃ctx bytes value count⦄, ((ctx, bytes), (value, count)) ∈ graph → count ≤ bytes.length

/-- On in-bounds spans, the bytes after the span do not affect this success. -/
def PrefixLocal (graph : Graph Context Source) : Prop :=
  ∀ ⦃ctx bytes value count⦄, count ≤ bytes.length →
    (((ctx, bytes), (value, count)) ∈ graph ↔ ((ctx, bytes.take count), (value, count)) ∈ graph)

/-- Completeness is relative to a specified success relation, not all byte strings. -/
def CompleteFor (graph spec : Graph Context Source) : Prop := spec ⊆ graph

/-- Relate decoded results without changing their byte span. -/
def onSpan (rel : SetRel Source Target) : SetRel (Source × Nat) (Target × Nat) :=
  {(source, target) | source.1 ~[rel] target.1 ∧ source.2 = target.2}

/-- Existential transport along a value relation. For lists, `rel` may relate
entire lists of different lengths. -/
def transport (rel : SetRel Source Target) (graph : Graph Context Source) : Graph Context Target :=
  graph ○ onSpan rel

/-- Functional transport is transport along the function's graph. -/
def map (f : Source → Target) (graph : Graph Context Source) : Graph Context Target :=
  transport (Function.graph f) graph

/-- The aligned, equal-length special case of a relation on whole lists. -/
def pointwise (rel : SetRel Source Target) : SetRel (List Source) (List Target) :=
  {(source, target) | List.Forall₂ (fun left right => left ~[rel] right) source target}

section Blocks

variable (decoder : Graph (Context × Nat) Source) (ends : Context → Nat → Source → Prop)

/-- A nonempty block starts at the query's byte address. Each ordinary
instruction advances by its positive, in-bounds span, and the first `ends`
instruction closes the block, including its own bytes. Fuel counts instructions.
An undecodable instruction, end of input or exhausted fuel before a terminator
yields no block. Trailing bytes after the terminator are not part of the block.
Addresses are natural byte offsets, not architectural PC arithmetic. -/
inductive Path : Nat → Context → Nat → Bytes → List Source → Nat → Prop
  | last {fuel ctx addr bytes instr width}
      (decoded : (((ctx, addr), bytes), (instr, width)) ∈ decoder)
      (positive : 0 < width) (fits : width ≤ bytes.length) (endsHere : ends ctx addr instr) :
      Path (fuel + 1) ctx addr bytes [instr] width
  | next {fuel ctx addr bytes instr width rest span}
      (decoded : (((ctx, addr), bytes), (instr, width)) ∈ decoder)
      (positive : 0 < width) (fits : width ≤ bytes.length) (continues : ¬ ends ctx addr instr)
      (tail : Path fuel ctx (addr + width) (bytes.drop width) rest span) :
      Path (fuel + 1) ctx addr bytes (instr :: rest) (width + span)

/-- A block decoder in the same outcome space as instruction decoders, with
exit byte boundary `entry + count` (not the architectural successor PC). -/
def blocks (fuel : Nat) : Graph (Context × Nat) (List Source) :=
  {(input, result) | Path decoder ends fuel input.1.1 input.1.2 input.2 result.1 result.2}

end Blocks

/-- A machine described by its observable executions at each input. Input may
include an initial state; an observation is opaque to rebasing. -/
abbrev Observed (Input Observation : Type*) := SetRel Input Observation

/-- An observation is admitted if some related base input admits it. No input
witness gives no observation; different witnesses contribute their union. -/
abbrev rebase {Input Base Observation : Type*} (adapter : SetRel Input Base)
    (machine : Observed Base Observation) : Observed Input Observation := adapter ○ machine

end Silmaril.Machine.DecodeGraph
